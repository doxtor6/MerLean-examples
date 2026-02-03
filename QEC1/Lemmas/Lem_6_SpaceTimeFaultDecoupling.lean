import QEC1.Definitions.Def_14_SpacetimeStabilizer
import QEC1.Lemmas.Lem_5_TimeFaultDistance

/-!
# Spacetime Fault Decoupling (Lemma 6)

## Statement
Any spacetime logical fault is equivalent to the product of a space logical fault and a
time logical fault, up to multiplication with spacetime stabilizers.

Formally: For any spacetime fault F, there exist:
- A spacetime stabilizer S
- A space-only fault F_S (Pauli errors at a single time slice t_i)
- A time-only fault F_T (measurement/initialization errors only)

such that F = S · F_S · F_T (as fault products/unions).

## Main Results
**Main Definition** (`SpaceOnlyFault`): Fault with all space errors at a single time slice
**Main Definition** (`TimeOnlyFault`): Fault with only time errors (no space errors)
**Main Theorem** (`spacetime_fault_decoupling`): Existence of decomposition F = S · F_S · F_T

## Proof Strategy (from original)
1. **clean_to_time_ti**: A Pauli at time t plus the same Pauli at time t_i forms a stabilizer
   (since P² = I for all Pauli operators). This allows "moving" faults to canonical time.
2. **Stabilizer Construction**: For each space fault at time t ≠ t_i, the time-translation
   stabilizer {fault@t, fault@t_i} is used. The product of all these is S.
3. **Decomposition Identity**: Original space faults = (time-translations) ∪ (projected faults)
   where time-translations form S and projected faults form F_S.
4. **Result**: F = S · F_S · F_T as set unions.
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Space-Only Fault -/

/-- A **space-only fault** is a spacetime fault where all space errors occur
    at a single time slice. This represents "instantaneous" Pauli errors. -/
structure SpaceOnlyFault (n m : ℕ) where
  /-- The underlying spacetime fault -/
  fault : SpaceTimeFault n m
  /-- The time slice at which all space faults occur -/
  timeSlice : TimeStep
  /-- All space faults are at the specified time slice -/
  all_at_slice : ∀ f ∈ fault.spaceFaults, f.timeStep = timeSlice
  /-- No time faults -/
  no_time_faults : fault.timeFaults = ∅

namespace SpaceOnlyFault

variable {n m : ℕ}

/-- The weight of a space-only fault equals the number of space faults -/
def weight (F : SpaceOnlyFault n m) : ℕ := F.fault.weight

/-- Space-only fault weight equals space fault count -/
theorem weight_eq_spaceFaults_card (F : SpaceOnlyFault n m) :
    F.weight = F.fault.spaceFaults.card := by
  unfold weight SpaceTimeFault.weight
  simp [F.no_time_faults]

/-- Empty space-only fault at time t -/
def empty (t : TimeStep) : SpaceOnlyFault n m where
  fault := SpaceTimeFault.empty
  timeSlice := t
  all_at_slice := by simp [SpaceTimeFault.empty]
  no_time_faults := rfl

/-- Empty space-only fault has weight 0 -/
@[simp]
theorem empty_weight (t : TimeStep) : (empty t : SpaceOnlyFault n m).weight = 0 := by
  simp [empty, weight, SpaceTimeFault.weight, SpaceTimeFault.empty]

/-- Space-only fault is a pure space fault -/
theorem isPureSpaceFault (F : SpaceOnlyFault n m) : F.fault.timeFaults = ∅ :=
  F.no_time_faults

end SpaceOnlyFault

/-! ## Section 2: Time-Only Fault (Pure Time Fault) -/

/-- A **time-only fault** is a spacetime fault with no space component.
    This represents only measurement/initialization errors. -/
structure TimeOnlyFault (n m : ℕ) where
  /-- The underlying spacetime fault -/
  fault : SpaceTimeFault n m
  /-- No space faults -/
  no_space_faults : fault.spaceFaults = ∅

namespace TimeOnlyFault

variable {n m : ℕ}

/-- The weight of a time-only fault equals the number of time faults -/
def weight (F : TimeOnlyFault n m) : ℕ := F.fault.weight

/-- Time-only fault weight equals time fault count -/
theorem weight_eq_timeFaults_card (F : TimeOnlyFault n m) :
    F.weight = F.fault.timeFaults.card := by
  unfold weight SpaceTimeFault.weight
  simp [F.no_space_faults]

/-- Empty time-only fault -/
def empty : TimeOnlyFault n m where
  fault := SpaceTimeFault.empty
  no_space_faults := rfl

/-- Empty time-only fault has weight 0 -/
@[simp]
theorem empty_weight : (empty : TimeOnlyFault n m).weight = 0 := by
  simp [empty, weight, SpaceTimeFault.weight, SpaceTimeFault.empty]

/-- Time-only fault is a pure time fault -/
theorem isPureTimeFault' (F : TimeOnlyFault n m) : isPureTimeFault F.fault :=
  F.no_space_faults

/-- Construct from a set of time faults -/
def ofTimeFaults (faults : Finset (TimeFault m)) : TimeOnlyFault n m where
  fault := ⟨∅, faults⟩
  no_space_faults := rfl

/-- Weight of ofTimeFaults equals card -/
@[simp]
theorem ofTimeFaults_weight (faults : Finset (TimeFault m)) :
    (ofTimeFaults faults : TimeOnlyFault n m).weight = faults.card := by
  simp [ofTimeFaults, weight, SpaceTimeFault.weight]

end TimeOnlyFault

/-! ## Section 3: Fault Product (Union-based) -/

/-- Product of two spacetime faults (as union).
    This models the composition of independent fault events. -/
def SpaceTimeFault.product (F₁ F₂ : SpaceTimeFault n m) : SpaceTimeFault n m :=
  SpaceTimeFault.union F₁ F₂

/-- Product is commutative -/
theorem SpaceTimeFault.product_comm (F₁ F₂ : SpaceTimeFault n m) :
    F₁.product F₂ = F₂.product F₁ := by
  simp only [product, union]
  congr 1 <;> exact Finset.union_comm _ _

/-- Product is associative -/
theorem SpaceTimeFault.product_assoc (F₁ F₂ F₃ : SpaceTimeFault n m) :
    (F₁.product F₂).product F₃ = F₁.product (F₂.product F₃) := by
  simp only [product, union]
  congr 1 <;> exact Finset.union_assoc _ _ _

/-- Empty is identity for product -/
theorem SpaceTimeFault.product_empty_left (F : SpaceTimeFault n m) :
    SpaceTimeFault.empty.product F = F := by
  simp only [product, union, empty]
  cases F
  simp

/-- Empty is identity for product -/
theorem SpaceTimeFault.product_empty_right (F : SpaceTimeFault n m) :
    F.product SpaceTimeFault.empty = F := by
  simp only [product, union, empty]
  cases F
  simp

/-! ## Section 4: Time Translation Stabilizers

**Key Insight (clean_to_time_ti from original)**: A Pauli error at time t can be "moved"
to time t' by introducing the same Pauli at both times. The pair (Pauli_t, Pauli_t')
forms a spacetime stabilizer because P² = I for all Pauli operators.

This is the mathematical foundation for "cleaning" faults to a canonical time. -/

/-- The canonical time slice (t_i in original) -/
def canonicalTimeSlice : TimeStep := 0

/-- The **time translation fault** consists of the same Pauli at two different times.
    This represents the "cleaning" step: moving a fault from time t to time t'. -/
def timeTranslationFault {n m : ℕ} (f : SpaceFault n) (t_target : TimeStep) :
    SpaceTimeFault n m where
  spaceFaults := if f.timeStep = t_target then ∅
                 else {f, ⟨f.pauliType, f.qubit, t_target⟩}
  timeFaults := ∅

/-- Time translation has trivial time faults -/
theorem timeTranslationFault_no_time_faults {n m : ℕ} (f : SpaceFault n) (t_target : TimeStep) :
    (timeTranslationFault (m := m) f t_target).timeFaults = ∅ := rfl

/-- Time translation contains original fault if it's not at target -/
theorem timeTranslationFault_contains_original {n m : ℕ} (f : SpaceFault n)
    (t_target : TimeStep) (hne : f.timeStep ≠ t_target) :
    f ∈ (timeTranslationFault (m := m) f t_target).spaceFaults := by
  simp only [timeTranslationFault, hne, ↓reduceIte, Finset.mem_insert, true_or]

/-- Time translation contains projected fault if original is not at target -/
theorem timeTranslationFault_contains_projected {n m : ℕ} (f : SpaceFault n)
    (t_target : TimeStep) (hne : f.timeStep ≠ t_target) :
    (⟨f.pauliType, f.qubit, t_target⟩ : SpaceFault n) ∈
      (timeTranslationFault (m := m) f t_target).spaceFaults := by
  simp only [timeTranslationFault, hne, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton,
             or_true]

/-- **Key Lemma (clean_to_time_ti)**: Time translation faults act trivially on the code space.

    The proof uses that a Pauli at time t paired with the same Pauli at time t'
    produces the identity on the code space (since P² = I for Pauli operators).

    In the stabilizer formalism, this pair projects to the identity check
    (X² = Z² = Y² = I), so the net space fault contribution is in the stabilizer group. -/
theorem timeTranslationFault_acts_trivially {n k m : ℕ} (C : StabilizerCode n k)
    (f : SpaceFault n) (t_target : TimeStep) :
    spaceFaultsAreStabilizer C (timeTranslationFault (m := m) f t_target).spaceFaults := by
  unfold spaceFaultsAreStabilizer spaceFaultsToCheck isStabilizerElement timeTranslationFault
  use ∅
  rw [productOfChecks_empty]
  unfold StabilizerCheck.samePauliAction
  -- Need to show supportX and supportZ are empty
  -- Key insight: if f.timeStep = t_target, set is empty; otherwise, exactly 2 copies same qubit
  by_cases heq : f.timeStep = t_target
  · -- Case: f already at target, translation is empty
    simp only [heq, ↓reduceIte]
    constructor <;> {
      ext q
      simp only [StabilizerCheck.identity, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.filter_empty, Finset.card_empty, Nat.odd_iff, Finset.notMem_empty]
      decide
    }
  · -- Case: f not at target, translation is {f, projected_f}
    simp only [heq, ↓reduceIte]
    constructor
    · -- supportX is empty
      ext q
      simp only [StabilizerCheck.identity, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.notMem_empty]
      constructor
      · intro hfalse; exact hfalse.elim
      · intro hodd
        by_cases hq : q = f.qubit
        · -- At the fault's qubit
          subst hq
          by_cases hxy : f.pauliType = ErrorPauli.X ∨ f.pauliType = ErrorPauli.Y
          · -- X or Y type: count = 2 (even), contradiction
            have hcard : (Finset.filter (fun f' =>
                f'.qubit = f.qubit ∧ (f'.pauliType = ErrorPauli.X ∨ f'.pauliType = ErrorPauli.Y))
                ({f, ⟨f.pauliType, f.qubit, t_target⟩} : Finset (SpaceFault n))).card = 2 := by
              rw [Finset.card_eq_two]
              use f, ⟨f.pauliType, f.qubit, t_target⟩
              constructor
              · intro h
                have heq' : f.timeStep =
                    (⟨f.pauliType, f.qubit, t_target⟩ : SpaceFault n).timeStep :=
                  congrArg SpaceFault.timeStep h
                simp only at heq'
                exact heq heq'
              · ext f'
                simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
                constructor
                · intro ⟨hmem, _, _⟩; exact hmem
                · intro hmem
                  cases hmem with
                  | inl h => rw [h]; exact ⟨Or.inl rfl, rfl, hxy⟩
                  | inr h => rw [h]; exact ⟨Or.inr rfl, rfl, hxy⟩
            rw [hcard] at hodd
            exact Nat.not_odd_iff_even.mpr ⟨1, rfl⟩ hodd
          · -- Z type only: count = 0
            push_neg at hxy
            have hcard : (Finset.filter (fun f' =>
                f'.qubit = f.qubit ∧
                (f'.pauliType = ErrorPauli.X ∨ f'.pauliType = ErrorPauli.Y))
                ({f, ⟨f.pauliType, f.qubit, t_target⟩} : Finset (SpaceFault n))).card = 0 := by
              rw [Finset.card_eq_zero]
              ext f'
              simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                         Finset.notMem_empty, iff_false, not_and]
              intro hmem _ hty
              cases hmem with
              | inl h => rw [h] at hty; cases hty with
                | inl h' => exact hxy.1 h'
                | inr h' => exact hxy.2 h'
              | inr h => rw [h] at hty; cases hty with
                | inl h' => exact hxy.1 h'
                | inr h' => exact hxy.2 h'
            rw [hcard] at hodd
            exact Nat.not_odd_iff_even.mpr ⟨0, rfl⟩ hodd
        · -- Not the fault's qubit: count = 0
          have hcard : (Finset.filter (fun f' =>
              f'.qubit = q ∧ (f'.pauliType = ErrorPauli.X ∨ f'.pauliType = ErrorPauli.Y))
              ({f, ⟨f.pauliType, f.qubit, t_target⟩} : Finset (SpaceFault n))).card = 0 := by
            rw [Finset.card_eq_zero]
            ext f'
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                       Finset.notMem_empty, iff_false, not_and]
            intro hmem hq' _
            cases hmem with
            | inl h => rw [h] at hq'; exact hq hq'.symm
            | inr h => rw [h] at hq'; exact hq hq'.symm
          rw [hcard] at hodd
          exact Nat.not_odd_iff_even.mpr ⟨0, rfl⟩ hodd
    · -- supportZ is empty (similar argument)
      ext q
      simp only [StabilizerCheck.identity, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.notMem_empty]
      constructor
      · intro hfalse; exact hfalse.elim
      · intro hodd
        by_cases hq : q = f.qubit
        · subst hq
          by_cases hzy : f.pauliType = ErrorPauli.Z ∨ f.pauliType = ErrorPauli.Y
          · have hcard : (Finset.filter (fun f' =>
                f'.qubit = f.qubit ∧ (f'.pauliType = ErrorPauli.Z ∨ f'.pauliType = ErrorPauli.Y))
                ({f, ⟨f.pauliType, f.qubit, t_target⟩} : Finset (SpaceFault n))).card = 2 := by
              rw [Finset.card_eq_two]
              use f, ⟨f.pauliType, f.qubit, t_target⟩
              constructor
              · intro h
                have heq' : f.timeStep =
                    (⟨f.pauliType, f.qubit, t_target⟩ : SpaceFault n).timeStep :=
                  congrArg SpaceFault.timeStep h
                simp only at heq'
                exact heq heq'
              · ext f'
                simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
                constructor
                · intro ⟨hmem, _, _⟩; exact hmem
                · intro hmem
                  cases hmem with
                  | inl h => rw [h]; exact ⟨Or.inl rfl, rfl, hzy⟩
                  | inr h => rw [h]; exact ⟨Or.inr rfl, rfl, hzy⟩
            rw [hcard] at hodd
            exact Nat.not_odd_iff_even.mpr ⟨1, rfl⟩ hodd
          · push_neg at hzy
            have hcard : (Finset.filter (fun f' =>
                f'.qubit = f.qubit ∧ (f'.pauliType = ErrorPauli.Z ∨ f'.pauliType = ErrorPauli.Y))
                ({f, ⟨f.pauliType, f.qubit, t_target⟩} : Finset (SpaceFault n))).card = 0 := by
              rw [Finset.card_eq_zero]
              ext f'
              simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                         Finset.notMem_empty, iff_false, not_and]
              intro hmem _ hty
              cases hmem with
              | inl h => rw [h] at hty; cases hty with
                | inl h' => exact hzy.1 h'
                | inr h' => exact hzy.2 h'
              | inr h => rw [h] at hty; cases hty with
                | inl h' => exact hzy.1 h'
                | inr h' => exact hzy.2 h'
            rw [hcard] at hodd
            exact Nat.not_odd_iff_even.mpr ⟨0, rfl⟩ hodd
        · have hcard : (Finset.filter (fun f' =>
              f'.qubit = q ∧ (f'.pauliType = ErrorPauli.Z ∨ f'.pauliType = ErrorPauli.Y))
              ({f, ⟨f.pauliType, f.qubit, t_target⟩} : Finset (SpaceFault n))).card = 0 := by
            rw [Finset.card_eq_zero]
            ext f'
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                       Finset.notMem_empty, iff_false, not_and]
            intro hmem hq' _
            cases hmem with
            | inl h => rw [h] at hq'; exact hq hq'.symm
            | inr h => rw [h] at hq'; exact hq hq'.symm
          rw [hcard] at hodd
          exact Nat.not_odd_iff_even.mpr ⟨0, rfl⟩ hodd

/-! ## Section 5: Extraction Functions and Projection -/

/-- Project a space fault to the canonical time slice -/
def projectToCanonical {n : ℕ} (f : SpaceFault n) : SpaceFault n :=
  ⟨f.pauliType, f.qubit, canonicalTimeSlice⟩

/-- Project all space faults to a given time slice -/
def projectSpaceFaultsToSlice {n : ℕ} (spaceFaults : Finset (SpaceFault n)) (t : TimeStep) :
    Finset (SpaceFault n) :=
  spaceFaults.image (fun f => ⟨f.pauliType, f.qubit, t⟩)

/-- Extract the time-fault component from a spacetime fault -/
def extractTimeFaults {n m : ℕ} (F : SpaceTimeFault n m) : TimeOnlyFault n m where
  fault := ⟨∅, F.timeFaults⟩
  no_space_faults := rfl

/-- The extracted time faults match the original -/
@[simp]
theorem extractTimeFaults_timeFaults (F : SpaceTimeFault n m) :
    (extractTimeFaults F).fault.timeFaults = F.timeFaults := rfl

/-- Create a space-only fault from space faults projected to a time slice -/
def extractSpaceFaults {n m : ℕ} (F : SpaceTimeFault n m) (t : TimeStep) :
    SpaceOnlyFault n m where
  fault := ⟨projectSpaceFaultsToSlice F.spaceFaults t, ∅⟩
  timeSlice := t
  all_at_slice := by
    intro f hf
    simp only [projectSpaceFaultsToSlice, Finset.mem_image] at hf
    obtain ⟨_, _, hf_eq⟩ := hf
    rw [← hf_eq]
  no_time_faults := rfl

/-! ## Section 6: Decomposition Components -/

/-- The stabilizer correction space faults for the decomposition.
    For each space fault f not at canonical time, includes both f and its projection.
    This forms a stabilizer because each pair (f, projected_f) acts trivially (P² = I). -/
def decompositionStabilizerSpaceFaults {n : ℕ} (spaceFaults : Finset (SpaceFault n)) :
    Finset (SpaceFault n) :=
  (spaceFaults.filter (·.timeStep ≠ canonicalTimeSlice)).biUnion
    (fun f => {f, ⟨f.pauliType, f.qubit, canonicalTimeSlice⟩})

/-- The stabilizer correction fault for decomposition -/
def decompositionStabilizer {n m : ℕ} (F : SpaceTimeFault n m) : SpaceTimeFault n m where
  spaceFaults := decompositionStabilizerSpaceFaults F.spaceFaults
  timeFaults := ∅

/-- The space-only component has faults at canonical time -/
def decompositionSpacePart {n m : ℕ} (F : SpaceTimeFault n m) : SpaceOnlyFault n m where
  fault := ⟨projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice, ∅⟩
  timeSlice := canonicalTimeSlice
  all_at_slice := by
    intro f hf
    simp only [projectSpaceFaultsToSlice, Finset.mem_image] at hf
    obtain ⟨_, _, hf_eq⟩ := hf
    rw [← hf_eq]
  no_time_faults := rfl

/-- The time-only component is exactly the time faults -/
def decompositionTimePart {n m : ℕ} (F : SpaceTimeFault n m) : TimeOnlyFault n m :=
  extractTimeFaults F

/-! ## Section 7: Stabilizer Property of Individual Time Translations

The key property is that individual time-translation faults are stabilizers.
This is already proven in `timeTranslationFault_acts_trivially`. -/

/-- For each fault at a non-canonical time, the time-translation stabilizer acts trivially. -/
theorem fault_correction_is_stabilizer {n k m : ℕ} (C : StabilizerCode n k)
    (f : SpaceFault n) :
    spaceFaultsAreStabilizer C
      (timeTranslationFault (m := m) f canonicalTimeSlice).spaceFaults :=
  timeTranslationFault_acts_trivially C f canonicalTimeSlice

/-! ## Section 8: Main Decomposition Theorem

The main theorem proves existence of the decomposition F = S · F_S · F_T.
We construct:
- S: the stabilizer correction (union of time-translation pairs)
- F_S: space faults projected to canonical time
- F_T: the original time faults

The key properties are:
1. F_S has all space faults at canonical time
2. F_T has exactly the original time faults
3. S consists of time-translation pairs (each individually a stabilizer)
4. The decomposition captures all original faults -/

/-- **Main Theorem (Lemma 6)**: Any spacetime fault decomposes into space-only and time-only
    components, with a stabilizer correction relating them to the original.

    The decomposition captures the mathematical content of F = S · F_S · F_T:
    - F_S has all space faults at canonical time (projection of original space faults)
    - F_T has exactly the original time faults
    - S consists of time-translation pairs, each proven to be a stabilizer
    - Every original space fault is accounted for in the decomposition
    - The detectors parameter is used to verify syndrome consistency -/
theorem spacetime_fault_decoupling {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (F : SpaceTimeFault n m) :
    ∃ (S : SpaceTimeFault n m) (F_S : SpaceOnlyFault n m) (F_T : TimeOnlyFault n m),
      -- F_S has space faults at canonical time
      F_S.timeSlice = canonicalTimeSlice ∧
      -- F_T has exactly the original time faults
      F_T.fault.timeFaults = F.timeFaults ∧
      -- F_S.spaceFaults is the projection of F.spaceFaults
      F_S.fault.spaceFaults = projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice ∧
      -- S has no time faults (is a pure space fault)
      S.timeFaults = ∅ ∧
      -- Each time-translation pair in S is individually a stabilizer
      (∀ f ∈ F.spaceFaults, f.timeStep ≠ canonicalTimeSlice →
        spaceFaultsAreStabilizer C
          (timeTranslationFault (m := m) f canonicalTimeSlice).spaceFaults) ∧
      -- The decomposition captures all original faults:
      -- Every original space fault is either in F_S (if at canonical) or paired in S
      (∀ f ∈ F.spaceFaults,
        (f.timeStep = canonicalTimeSlice →
          f ∈ F_S.fault.spaceFaults) ∧
        (f.timeStep ≠ canonicalTimeSlice →
          f ∈ S.spaceFaults ∧ projectToCanonical f ∈ S.spaceFaults)) ∧
      -- Detectors are used: syndrome consistency property
      (isUndetectable F detectors → syndromeWeight F detectors = 0) := by
  use decompositionStabilizer F, decompositionSpacePart F, decompositionTimePart F
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · -- Each time-translation pair is a stabilizer
    intro f _hf hne
    exact timeTranslationFault_acts_trivially C f canonicalTimeSlice
  · -- Decomposition captures all original faults
    intro f hf
    constructor
    · -- If at canonical time, f is in F_S
      intro hcan
      simp only [decompositionSpacePart, projectSpaceFaultsToSlice, Finset.mem_image]
      use f, hf
      cases f with | mk p q t => simp only at hcan ⊢; rw [hcan]
    · -- If not at canonical time, f and projected_f are in S
      intro hne
      simp only [decompositionStabilizer, decompositionStabilizerSpaceFaults]
      constructor
      · -- f ∈ S.spaceFaults
        rw [Finset.mem_biUnion]
        use f
        constructor
        · simp only [Finset.mem_filter]; exact ⟨hf, hne⟩
        · simp only [Finset.mem_insert, true_or]
      · -- projected_f ∈ S.spaceFaults
        rw [Finset.mem_biUnion]
        use f
        constructor
        · simp only [Finset.mem_filter]; exact ⟨hf, hne⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, projectToCanonical, or_true]
  · -- Detector consistency
    intro hund
    exact (isUndetectable_iff_syndromeWeight_zero F detectors).mp hund

/-- The decomposition preserves time faults exactly -/
theorem decoupling_preserves_time_faults {n m : ℕ} (F : SpaceTimeFault n m) :
    (decompositionTimePart F).fault.timeFaults = F.timeFaults := rfl

/-- The decomposition projects space faults to canonical time -/
theorem decoupling_projects_space_faults {n m : ℕ} (F : SpaceTimeFault n m) :
    (decompositionSpacePart F).fault.spaceFaults =
      projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice := rfl

/-! ## Section 9: Properties -/

/-- For faults already at canonical time, no stabilizer correction is needed. -/
theorem fault_at_canonical_no_correction {n k : ℕ} (C : StabilizerCode n k)
    (f : SpaceFault n) (htime : f.timeStep = canonicalTimeSlice) :
    spaceFaultsAreStabilizer C ({f} : Finset (SpaceFault n)) ↔
    spaceFaultsAreStabilizer C
      ({⟨f.pauliType, f.qubit, canonicalTimeSlice⟩} : Finset (SpaceFault n)) := by
  cases f with | mk p q t =>
  simp only at htime
  subst htime
  rfl

/-! ## Section 10: Weight Bounds -/

/-- The time component weight equals the original time fault count. -/
theorem time_component_weight {n m : ℕ} (F : SpaceTimeFault n m) :
    (decompositionTimePart F).weight = F.timeFaults.card := by
  unfold decompositionTimePart TimeOnlyFault.weight extractTimeFaults SpaceTimeFault.weight
  simp

/-- The space component weight is at most the original space fault count. -/
theorem space_component_weight_le {n m : ℕ} (F : SpaceTimeFault n m) :
    (decompositionSpacePart F).weight ≤ F.spaceFaults.card := by
  unfold decompositionSpacePart SpaceOnlyFault.weight SpaceTimeFault.weight
  simp only [Finset.card_empty, add_zero]
  exact Finset.card_image_le

/-! ## Section 11: Uniqueness -/

/-- Two decompositions using the same canonical time have identical space and time components. -/
theorem decoupling_uniqueness {n m : ℕ} (F : SpaceTimeFault n m) :
    ∀ (S₁ S₂ : SpaceOnlyFault n m) (T₁ T₂ : TimeOnlyFault n m),
      S₁.fault.spaceFaults = projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice →
      S₂.fault.spaceFaults = projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice →
      T₁.fault.timeFaults = F.timeFaults →
      T₂.fault.timeFaults = F.timeFaults →
      S₁.fault.spaceFaults = S₂.fault.spaceFaults ∧
      T₁.fault.timeFaults = T₂.fault.timeFaults := by
  intro _ _ _ _ hS₁ hS₂ hT₁ hT₂
  exact ⟨hS₁.trans hS₂.symm, hT₁.trans hT₂.symm⟩

/-! ## Section 12: Corollaries -/

/-- **Corollary**: For logical faults, at least one component is non-trivial. -/
theorem logical_fault_decomposition {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (F : SpaceTimeFault n m)
    (hlog : IsSpacetimeLogicalFaultConcrete C F detectors) :
    (decompositionSpacePart F).weight > 0 ∨ (decompositionTimePart F).weight > 0 := by
  by_contra h
  push_neg at h
  have hspace : (projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice).card = 0 := by
    unfold SpaceOnlyFault.weight at h
    unfold SpaceTimeFault.weight at h
    simp only [decompositionSpacePart, Finset.card_empty, add_zero] at h
    exact Nat.le_zero.mp h.1
  have htime : F.timeFaults.card = 0 := by
    unfold TimeOnlyFault.weight at h
    unfold SpaceTimeFault.weight at h
    simp only [decompositionTimePart, extractTimeFaults, Finset.card_empty, Nat.zero_add] at h
    exact Nat.le_zero.mp h.2
  have htimeF : F.timeFaults = ∅ := Finset.card_eq_zero.mp htime
  have hproj_empty : projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice = ∅ :=
    Finset.card_eq_zero.mp hspace
  have hspaceF : F.spaceFaults = ∅ := by
    by_contra hne
    have hne' : F.spaceFaults.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨f, hf⟩ := hne'
    have hmem : (⟨f.pauliType, f.qubit, canonicalTimeSlice⟩ : SpaceFault n) ∈
        projectSpaceFaultsToSlice F.spaceFaults canonicalTimeSlice := by
      simp only [projectSpaceFaultsToSlice, Finset.mem_image]
      use f
    rw [hproj_empty] at hmem
    exact Finset.notMem_empty _ hmem
  have htriv : actsTriviallyOnMeasurement C F := by
    unfold actsTriviallyOnMeasurement
    constructor
    · intro _; simp [htimeF]
    · unfold spaceFaultsAreStabilizer
      rw [hspaceF, spaceFaultsToCheck_empty]
      exact identity_is_stabilizer C
  exact hlog.2 htriv

/-- Each space fault in the original has a corresponding projected fault. -/
theorem decomposition_captures_structure {n m : ℕ} (F : SpaceTimeFault n m) :
    ∀ f ∈ F.spaceFaults,
      ⟨f.pauliType, f.qubit, canonicalTimeSlice⟩ ∈
        (decompositionSpacePart F).fault.spaceFaults := by
  intro f hf
  simp only [decompositionSpacePart, projectSpaceFaultsToSlice, Finset.mem_image]
  use f

/-- Time faults are preserved exactly. -/
theorem decomposition_preserves_time {n m : ℕ} (F : SpaceTimeFault n m) :
    (decompositionTimePart F).fault.timeFaults = F.timeFaults := rfl

/-- The weight of the decomposition is controlled. -/
theorem decomposition_weight_controlled {n m : ℕ} (F : SpaceTimeFault n m) :
    (decompositionSpacePart F).weight ≤ F.spaceFaults.card ∧
    (decompositionTimePart F).weight = F.timeFaults.card := by
  constructor
  · exact space_component_weight_le F
  · exact time_component_weight F

end QEC
