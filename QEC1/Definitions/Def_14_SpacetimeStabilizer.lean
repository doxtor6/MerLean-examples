import QEC1.Definitions.Def_1_StabilizerCode
import QEC1.Definitions.Def_13_SpacetimeLogicalFault

/-!
# Spacetime Stabilizer (Definition 14)

## Statement
A **spacetime stabilizer** is a collection of space and time faults that:
(i) Does not violate any detector: syn(F) = ∅
(ii) Does not affect the result of the gauging measurement procedure

Spacetime stabilizers are the "trivial" undetectable faults - they are errors that cancel out
and have no effect on the computation.

## Main Results
**Main Predicate** (`IsSpacetimeStabilizer`): When a fault is a spacetime stabilizer
**Main Structure** (`SpacetimeStabilizer`): Bundled spacetime stabilizer with proofs
**Key Theorem** (`stabilizer_vs_logical_dichotomy`): Undetectable = stabilizers ∪ logical faults

## File Structure
1. Time Fault Cancellation: Even count per measurement index
2. Space Fault Stabilizer Test: Space faults form a stabilizer element
3. Trivial Action Predicate: Combined condition for no effect on computation
4. Spacetime Stabilizer Predicate: Undetectable fault that acts trivially
5. Spacetime Stabilizer Structure: Bundled type with proofs
6. Dichotomy: Partition of undetectable faults into stabilizers and logical faults
7. Properties and Helper Lemmas

## Design Note
A spacetime stabilizer differs from a spacetime logical fault in its effect on computation:
- Both have empty syndrome (syn(F) = ∅)
- Stabilizers act trivially (no effect on logical measurement outcome)
- Logical faults flip logical measurement outcomes

The concrete characterization of "trivial action" captures BOTH:
1. Time faults occur in pairs that cancel out (even count per measurement index)
2. Space faults form a product of stabilizer generators (stabilizer element)

This ensures the fault has no observable effect on the computation.
-/

namespace QEC

/-! ## Section 1: Time Fault Cancellation

For stabilizer codes, time faults cancel if they occur in pairs on the same measurement.
Each pair of bit flips on the same measurement outcome cancels out. -/

/-- Time faults cancel if they occur an even number of times at each measurement index.
    This captures the condition that measurement errors come in pairs that cancel out. -/
def timeFaultsCancel {m : ℕ} (timeFaults : Finset (TimeFault m)) : Prop :=
  ∀ idx : Fin m, Even ((timeFaults.filter (fun f => f.measurementIndex = idx)).card)

/-- Time faults in the empty fault trivially cancel -/
@[simp]
theorem timeFaultsCancel_empty : timeFaultsCancel (∅ : Finset (TimeFault m)) := by
  intro _
  simp only [Finset.filter_empty, Finset.card_empty]
  exact ⟨0, rfl⟩

/-- Decidability of timeFaultsCancel -/
instance instDecidableTimeFaultsCancel {m : ℕ} (faults : Finset (TimeFault m)) :
    Decidable (timeFaultsCancel faults) :=
  inferInstanceAs (Decidable (∀ _, _))

/-! ## Section 2: Space Fault to Stabilizer Check Conversion

To check if space faults form a stabilizer element, we need to convert the collection
of space faults to a StabilizerCheck and verify it's in the stabilizer group. -/

/-- Convert a set of space faults to a StabilizerCheck by accumulating their Pauli operators.
    The resulting check has:
    - supportX: qubits with odd X/Y error count
    - supportZ: qubits with odd Z/Y error count
    - phase: Phase.one (we only care about Pauli action for stabilizer membership)

    This handles the case where multiple errors on the same qubit may cancel. -/
def spaceFaultsToCheck {n : ℕ} (spaceFaults : Finset (SpaceFault n)) : StabilizerCheck n :=
  { supportX := Finset.filter (fun q =>
      Odd ((spaceFaults.filter (fun f => f.qubit = q ∧
        (f.pauliType = ErrorPauli.X ∨ f.pauliType = ErrorPauli.Y))).card)) Finset.univ
    supportZ := Finset.filter (fun q =>
      Odd ((spaceFaults.filter (fun f => f.qubit = q ∧
        (f.pauliType = ErrorPauli.Z ∨ f.pauliType = ErrorPauli.Y))).card)) Finset.univ
    phase := Phase.one }

/-- Empty space faults convert to identity check -/
theorem spaceFaultsToCheck_empty {n : ℕ} :
    spaceFaultsToCheck (∅ : Finset (SpaceFault n)) = StabilizerCheck.identity n := by
  simp only [spaceFaultsToCheck, StabilizerCheck.identity]
  congr 1 <;> {
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.filter_empty,
               Finset.card_empty, Nat.odd_iff, Finset.notMem_empty, iff_false]
    omega
  }

/-! ## Section 3: Space Faults in Stabilizer Group

A collection of space faults acts trivially on the logical state if and only if
the resulting Pauli operator is in the stabilizer group (a product of generators). -/

/-- Space faults form a stabilizer element if their net effect is in the stabilizer group.
    This means the fault can be expressed as a product of stabilizer generators,
    so it acts trivially on the code space. -/
def spaceFaultsAreStabilizer {n k : ℕ} (C : StabilizerCode n k)
    (spaceFaults : Finset (SpaceFault n)) : Prop :=
  isStabilizerElement C (spaceFaultsToCheck spaceFaults)

/-- Empty space faults are always in the stabilizer group (identity is a stabilizer) -/
theorem spaceFaultsAreStabilizer_empty {n k : ℕ} (C : StabilizerCode n k) :
    spaceFaultsAreStabilizer C (∅ : Finset (SpaceFault n)) := by
  unfold spaceFaultsAreStabilizer
  rw [spaceFaultsToCheck_empty]
  exact identity_is_stabilizer C

/-! ## Section 4: Trivial Action on Gauging Measurement (Full Condition)

A spacetime fault acts **trivially** on the gauging measurement if BOTH:
1. Its time faults occur in canceling pairs (even count per measurement index)
2. Its space faults form a stabilizer element (product of generators)

Combined with being undetectable, this ensures the fault has no effect on the
logical computation result. -/

/-- A spacetime fault acts trivially on the gauging measurement if:
    1. Time faults cancel in pairs
    2. Space faults form a stabilizer element

    This captures condition (ii) of the spacetime stabilizer definition:
    "Does not affect the result of the gauging measurement procedure"

    The `code` parameter provides the stabilizer code structure needed to check
    if space faults are in the stabilizer group. -/
def actsTriviallyOnMeasurement {n k m : ℕ} (C : StabilizerCode n k)
    (F : SpaceTimeFault n m) : Prop :=
  timeFaultsCancel F.timeFaults ∧ spaceFaultsAreStabilizer C F.spaceFaults

/-- Empty fault acts trivially -/
@[simp]
theorem actsTrivially_empty {n k m : ℕ} (C : StabilizerCode n k) :
    actsTriviallyOnMeasurement C (SpaceTimeFault.empty : SpaceTimeFault n m) := by
  unfold actsTriviallyOnMeasurement
  constructor
  · intro _
    simp [SpaceTimeFault.empty]
  · exact spaceFaultsAreStabilizer_empty C

/-! ## Section 5: Spacetime Stabilizer Predicate -/

/-- A **spacetime stabilizer** is a spacetime fault that:
    (i) Does not violate any detector: syn(F) = ∅ (i.e., isUndetectable)
    (ii) Does not affect the result of the gauging measurement procedure
         - Time faults cancel in pairs
         - Space faults form a stabilizer element

    These are the "trivial" undetectable faults - errors that cancel out completely. -/
def IsSpacetimeStabilizer {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) : Prop :=
  isUndetectable F detectors ∧ actsTriviallyOnMeasurement C F

/-- A spacetime stabilizer is undetectable -/
theorem IsSpacetimeStabilizer.undetectable {n k m : ℕ}
    {C : StabilizerCode n k} {F : SpaceTimeFault n m} {detectors : Finset (Detector n)}
    (h : IsSpacetimeStabilizer C F detectors) : isUndetectable F detectors :=
  h.1

/-- A spacetime stabilizer acts trivially -/
theorem IsSpacetimeStabilizer.trivial {n k m : ℕ}
    {C : StabilizerCode n k} {F : SpaceTimeFault n m} {detectors : Finset (Detector n)}
    (h : IsSpacetimeStabilizer C F detectors) : actsTriviallyOnMeasurement C F :=
  h.2

/-- A spacetime stabilizer has time faults that cancel -/
theorem IsSpacetimeStabilizer.timeFaultsCancel {n k m : ℕ}
    {C : StabilizerCode n k} {F : SpaceTimeFault n m} {detectors : Finset (Detector n)}
    (h : IsSpacetimeStabilizer C F detectors) : timeFaultsCancel F.timeFaults :=
  h.2.1

/-- A spacetime stabilizer has space faults in the stabilizer group -/
theorem IsSpacetimeStabilizer.spaceFaultsAreStabilizer {n k m : ℕ}
    {C : StabilizerCode n k} {F : SpaceTimeFault n m} {detectors : Finset (Detector n)}
    (h : IsSpacetimeStabilizer C F detectors) : spaceFaultsAreStabilizer C F.spaceFaults :=
  h.2.2

/-! ## Section 6: Spacetime Stabilizer Structure -/

/-- Structure bundling a spacetime fault with proofs that it is a spacetime stabilizer.
    This packages together:
    - A spacetime fault F
    - Proof that F is undetectable (empty syndrome)
    - Proof that F acts trivially on the computation (both time and space conditions) -/
structure SpacetimeStabilizer (n k m : ℕ) (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) where
  /-- The underlying spacetime fault -/
  fault : SpaceTimeFault n m
  /-- The fault is undetectable (empty syndrome) -/
  undetectable : isUndetectable fault detectors
  /-- Time faults cancel in pairs -/
  timeCancel : timeFaultsCancel fault.timeFaults
  /-- Space faults are in the stabilizer group -/
  spaceStabilizer : spaceFaultsAreStabilizer C fault.spaceFaults

namespace SpacetimeStabilizer

variable {n k m : ℕ} {C : StabilizerCode n k} {detectors : Finset (Detector n)}

/-- A spacetime stabilizer acts trivially on measurement -/
theorem trivialAction (S : SpacetimeStabilizer n k m C detectors) :
    actsTriviallyOnMeasurement C S.fault :=
  ⟨S.timeCancel, S.spaceStabilizer⟩

/-- A spacetime stabilizer satisfies the predicate -/
theorem isStabilizer (S : SpacetimeStabilizer n k m C detectors) :
    IsSpacetimeStabilizer C S.fault detectors :=
  ⟨S.undetectable, S.trivialAction⟩

/-- The weight of a spacetime stabilizer -/
def weight (S : SpacetimeStabilizer n k m C detectors) : ℕ :=
  S.fault.weight

/-- Extract from a fault satisfying the predicate -/
def ofIsStabilizer {F : SpaceTimeFault n m}
    (h : IsSpacetimeStabilizer C F detectors) :
    SpacetimeStabilizer n k m C detectors where
  fault := F
  undetectable := h.1
  timeCancel := h.2.1
  spaceStabilizer := h.2.2

/-- The syndrome of a spacetime stabilizer is empty -/
@[simp]
theorem syndrome_empty (S : SpacetimeStabilizer n k m C detectors) :
    syndromeFinset S.fault detectors = ∅ :=
  S.undetectable

/-- A spacetime stabilizer has zero syndrome weight -/
@[simp]
theorem syndromeWeight_eq_zero (S : SpacetimeStabilizer n k m C detectors) :
    syndromeWeight S.fault detectors = 0 := by
  rw [← isUndetectable_iff_syndromeWeight_zero]
  exact S.undetectable

/-- A spacetime stabilizer violates no detector -/
theorem no_violation (S : SpacetimeStabilizer n k m C detectors) :
    ∀ D ∈ detectors, ¬violates S.fault D := by
  rw [← isUndetectable_iff_no_violation]
  exact S.undetectable

end SpacetimeStabilizer

/-! ## Section 7: Dichotomy - Stabilizers vs Logical Faults

The key insight: undetectable faults partition into two types:
1. Spacetime stabilizers: act trivially, no effect on computation
2. Spacetime logical faults: change the logical measurement outcome

This is the fundamental trichotomy in fault-tolerant QEC:
- Detectable errors (correctable by decoder)
- Undetectable but trivial (stabilizers - no harm)
- Undetectable and non-trivial (logical faults - corruption) -/

/-- Define when a fault is a spacetime logical fault using the concrete trivial action predicate.
    This is an undetectable fault that does NOT act trivially (either time faults don't cancel
    OR space faults are not in the stabilizer group). -/
def IsSpacetimeLogicalFaultConcrete {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) : Prop :=
  isUndetectable F detectors ∧ ¬actsTriviallyOnMeasurement C F

/-- Stabilizers and logical faults form a dichotomy of undetectable faults.
    An undetectable fault is EITHER a stabilizer OR a logical fault, never both. -/
theorem stabilizer_vs_logical_dichotomy {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m)
    (detectors : Finset (Detector n)) (h : isUndetectable F detectors) :
    IsSpacetimeStabilizer C F detectors ∨
    IsSpacetimeLogicalFaultConcrete C F detectors := by
  by_cases htriv : actsTriviallyOnMeasurement C F
  · left
    exact ⟨h, htriv⟩
  · right
    exact ⟨h, htriv⟩

/-- A fault cannot be both a stabilizer and a logical fault.
    This follows because stabilizers have trivial action and logical faults don't. -/
theorem not_both_stabilizer_and_logical_concrete {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) :
    ¬(IsSpacetimeStabilizer C F detectors ∧ IsSpacetimeLogicalFaultConcrete C F detectors) := by
  intro ⟨hStab, hLog⟩
  exact hLog.2 hStab.2

/-- Stabilizers and logical faults are mutually exclusive and exhaustive for undetectable faults -/
theorem stabilizer_xor_logical {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (h : isUndetectable F detectors) :
    Xor' (IsSpacetimeStabilizer C F detectors) (IsSpacetimeLogicalFaultConcrete C F detectors) := by
  unfold Xor'
  by_cases htriv : actsTriviallyOnMeasurement C F
  · left
    exact ⟨⟨h, htriv⟩, fun hlog => hlog.2 htriv⟩
  · right
    exact ⟨⟨h, htriv⟩, fun hstab => htriv hstab.2⟩

/-- The three-way classification of spacetime faults:
    1. Detectable (non-empty syndrome)
    2. Undetectable stabilizer (empty syndrome, trivial action)
    3. Undetectable logical fault (empty syndrome, non-trivial action) -/
theorem fault_trichotomy {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) :
    (¬isUndetectable F detectors) ∨
    IsSpacetimeStabilizer C F detectors ∨
    IsSpacetimeLogicalFaultConcrete C F detectors := by
  by_cases hund : isUndetectable F detectors
  · right
    exact stabilizer_vs_logical_dichotomy C F detectors hund
  · left
    exact hund

/-! ## Section 8: Empty Fault is a Stabilizer -/

/-- The empty fault is always a spacetime stabilizer.
    The empty fault:
    - Has empty syndrome (no detectors violated)
    - Time faults are empty (trivially cancel)
    - Space faults are empty (identity is in stabilizer group) -/
theorem empty_isStabilizer {n k m : ℕ} (C : StabilizerCode n k) (detectors : Finset (Detector n)) :
    IsSpacetimeStabilizer C (SpaceTimeFault.empty : SpaceTimeFault n m) detectors := by
  constructor
  · exact empty_isUndetectable detectors
  · exact actsTrivially_empty C

/-- Construct the empty spacetime stabilizer -/
def emptyStabilizer {n k m : ℕ} (C : StabilizerCode n k) (detectors : Finset (Detector n)) :
    SpacetimeStabilizer n k m C detectors where
  fault := SpaceTimeFault.empty
  undetectable := empty_isUndetectable detectors
  timeCancel := timeFaultsCancel_empty
  spaceStabilizer := spaceFaultsAreStabilizer_empty C

/-- The empty stabilizer has weight 0 -/
@[simp]
theorem emptyStabilizer_weight {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) :
    (emptyStabilizer C detectors : SpacetimeStabilizer n k m C detectors).weight = 0 := by
  simp [emptyStabilizer, SpacetimeStabilizer.weight]

/-! ## Section 9: Properties of Time Fault Cancellation -/

/-- Single time fault does not cancel (odd count) -/
theorem single_timeFault_not_cancel (f : TimeFault m) (_hm : 0 < m) :
    ¬timeFaultsCancel ({f} : Finset (TimeFault m)) := by
  intro h
  have hf := h f.measurementIndex
  simp only [Finset.filter_singleton] at hf
  simp only [↓reduceIte, Finset.card_singleton] at hf
  exact Nat.not_even_one hf

/-- Two time faults on the same measurement index with different rounds cancel -/
theorem pair_timeFaults_same_index_cancel (f₁ f₂ : TimeFault m)
    (heq_idx : f₁.measurementIndex = f₂.measurementIndex)
    (hne : f₁ ≠ f₂) :
    timeFaultsCancel ({f₁, f₂} : Finset (TimeFault m)) := by
  intro idx
  by_cases hidx : idx = f₁.measurementIndex
  · -- idx is the common index, we have 2 faults
    simp only [Finset.filter_insert, Finset.filter_singleton]
    rw [hidx, heq_idx]
    simp only [↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    · simp only [Finset.card_singleton]
      exact ⟨1, rfl⟩
    · simp only [Finset.mem_singleton]
      exact hne
  · -- idx is different, we have 0 faults
    have h1 : f₁.measurementIndex ≠ idx := fun heq' => hidx heq'.symm
    have h2 : f₂.measurementIndex ≠ idx := by
      intro heq'
      rw [heq_idx] at hidx
      exact hidx heq'.symm
    simp only [Finset.filter_insert, Finset.filter_singleton]
    rw [if_neg h1, if_neg h2]
    exact ⟨0, rfl⟩

/-- A fault with a single time fault is NOT a stabilizer
    (because time faults don't cancel) -/
theorem single_timeFault_not_stabilizer {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (f : TimeFault m) (hm : 0 < m) (hF : F.timeFaults = {f}) :
    ¬IsSpacetimeStabilizer C F detectors := by
  intro h
  have htriv := h.2.1
  rw [hF] at htriv
  exact single_timeFault_not_cancel f hm htriv

/-! ## Section 10: Stabilizer Weight Bounds -/

/-- The minimum weight stabilizer is the empty fault with weight 0 -/
theorem stabilizer_min_weight_zero {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) :
    ∃ S : SpacetimeStabilizer n k m C detectors, S.weight = 0 := by
  use emptyStabilizer C detectors
  rfl

/-- Stabilizer weight is bounded by fault weight -/
theorem stabilizer_weight_le_fault_weight {n k m : ℕ}
    {C : StabilizerCode n k} {detectors : Finset (Detector n)}
    (S : SpacetimeStabilizer n k m C detectors) :
    S.weight ≤ S.fault.weight := by
  rfl

/-! ## Section 11: Relationship with Def_13 Logical Fault -/

/-- The concrete stabilizer predicate is consistent with Def_13's logical fault:
    IsSpacetimeLogicalFault (using actsTriviallyOnMeasurement as the stabilizer test)
    is equivalent to IsSpacetimeLogicalFaultConcrete -/
theorem logical_fault_consistency {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) :
    IsSpacetimeLogicalFault (fun G _ => actsTriviallyOnMeasurement C G) F detectors ↔
    IsSpacetimeLogicalFaultConcrete C F detectors := by
  rfl

/-- Connecting to the parameterized version in Def_13:
    If we instantiate the stabilizer predicate with actsTriviallyOnMeasurement,
    we get our concrete definitions. -/
theorem stabilizer_consistency {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) :
    (fun G dets => isUndetectable G dets ∧ actsTriviallyOnMeasurement C G) F detectors ↔
    IsSpacetimeStabilizer C F detectors := by
  rfl

/-! ## Section 12: Helper Lemmas -/

/-- The weight of a stabilizer is non-negative -/
theorem stabilizer_weight_nonneg {n k m : ℕ} {C : StabilizerCode n k}
    {detectors : Finset (Detector n)} (S : SpacetimeStabilizer n k m C detectors) :
    0 ≤ S.weight :=
  Nat.zero_le _

/-- Two spacetime stabilizers with the same underlying fault are equal -/
theorem SpacetimeStabilizer_ext {n k m : ℕ} {C : StabilizerCode n k}
    {detectors : Finset (Detector n)}
    (S₁ S₂ : SpacetimeStabilizer n k m C detectors)
    (h : S₁.fault = S₂.fault) : S₁ = S₂ := by
  cases S₁
  cases S₂
  simp only at h
  subst h
  rfl

/-- If there are no detectors, every fault with trivial action is a stabilizer -/
theorem isStabilizer_of_empty_detectors {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m)
    (htriv : actsTriviallyOnMeasurement C F) :
    IsSpacetimeStabilizer C F (∅ : Finset (Detector n)) := by
  constructor
  · exact isUndetectable_of_empty_detectors F
  · exact htriv

/-- A fault with no faults at all acts trivially -/
theorem actsTrivially_of_no_faults {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m)
    (hspace : F.spaceFaults = ∅) (htime : F.timeFaults = ∅) :
    actsTriviallyOnMeasurement C F := by
  unfold actsTriviallyOnMeasurement
  constructor
  · -- Time faults cancel (they're empty)
    intro _
    simp [htime]
  · -- Space faults are in stabilizer group (empty = identity)
    unfold spaceFaultsAreStabilizer
    rw [hspace]
    rw [spaceFaultsToCheck_empty]
    exact identity_is_stabilizer C

/-- A fault with no faults and empty syndrome is a stabilizer -/
theorem isStabilizer_of_no_faults {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (hund : isUndetectable F detectors)
    (hspace : F.spaceFaults = ∅) (htime : F.timeFaults = ∅) :
    IsSpacetimeStabilizer C F detectors :=
  ⟨hund, actsTrivially_of_no_faults C F hspace htime⟩

/-! ## Section 13: Concrete Stabilizer Properties -/

/-- A spacetime stabilizer has even time fault counts at each measurement -/
theorem stabilizer_even_time_faults {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (h : IsSpacetimeStabilizer C F detectors) (idx : Fin m) :
    Even ((F.timeFaults.filter (fun f => f.measurementIndex = idx)).card) :=
  h.2.1 idx

/-- A spacetime stabilizer has space faults in the stabilizer group -/
theorem stabilizer_space_in_group {n k m : ℕ}
    (C : StabilizerCode n k) (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (h : IsSpacetimeStabilizer C F detectors) :
    spaceFaultsAreStabilizer C F.spaceFaults :=
  h.2.2

end QEC
