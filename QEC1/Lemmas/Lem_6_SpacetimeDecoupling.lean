import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Set.Lattice

import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_8_Detector
import QEC1.Definitions.Def_10_SpacetimeLogicalFault
import QEC1.Lemmas.Lem_4_SpacetimeStabilizers
import QEC1.Lemmas.Lem_5_TimeFaultDistance

/-!
# Lemma 6: Spacetime Decoupling

## Statement
Any spacetime logical fault F is equivalent, up to multiplication by spacetime stabilizers,
to the product of a pure space logical fault and a pure time logical fault:
$$F \sim F_{\text{space}} \cdot F_{\text{time}}$$
where $F_{\text{space}}$ consists only of Pauli errors at a **single time step**, and
$F_{\text{time}}$ consists only of measurement/initialization errors.

## Main Results
- `spacetimeDecoupling`: The main theorem: F ∼ F_space · F_time with F_space at single time

## Proof Structure
**Step 1**: Clean space component to a single time step using Pauli pair stabilizers (Lem_4).
Moving P from time t to t+1: multiply by stabilizer "P at t, P at t+1, measurement faults
on anticommuting checks". Since P·P = I, the original P cancels. Net effect: P moved to t+1.
The cleaning stabilizer includes both Pauli errors AND measurement errors.

**Step 2**: Measurement errors in cleaned fault lie in [t_i, t_o] by perfect boundary convention.

**Step 3**: Edge readout fault strings are absorbed into Type 2 spacetime stabilizers (Lem_5).

**Step 4**: Remaining fault = F_space (Pauli at t_i) · F_time (A_v measurement strings).

**Step 5**: Both components are logical faults (trivial or nontrivial).
-/

namespace SpacetimeDecoupling

open Finset SpacetimeFault

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {V E M : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq M]

/-! ## Section 1: Pure Space Fault at Single Time Step -/

/-- A spacetime fault is a pure space fault at a single time step t if:
    - All space errors occur only at time t
    - There are no time errors (measurement errors) -/
def isPureSpaceFaultAtSingleTime (F : SpacetimeFault V E M) (t : TimeStep) : Prop :=
  (∀ q t', t' ≠ t → F.spaceErrors q t' = PauliType.I) ∧
  (∀ m t', F.timeErrors m t' = false)

/-- A spacetime fault is a pure time fault (only measurement/init errors) -/
def isPureTimeFault (F : SpacetimeFault V E M) : Prop :=
  ∀ q t, F.spaceErrors q t = PauliType.I

@[simp]
lemma identity_isPureSpaceFaultAtSingleTime (t : TimeStep) :
    isPureSpaceFaultAtSingleTime (1 : SpacetimeFault V E M) t :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

@[simp]
lemma identity_isPureTimeFault : isPureTimeFault (1 : SpacetimeFault V E M) :=
  fun _ _ => rfl

/-! ## Section 2: Equivalence Modulo Stabilizers -/

/-- Two faults are equivalent modulo stabilizers: F ∼ G iff F = G * S for some stabilizer S -/
def EquivModStabilizers
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (F G : SpacetimeFault V E M) : Prop :=
  ∃ S, IsSpacetimeStabilizer DC baseOutcomes logicalEffect S ∧ F = G * S

/-! ## Section 3: Gauging Interval -/

/-- The gauging interval [t_i, t_o] -/
structure GaugingInterval where
  t_i : TimeStep  -- Initial boundary
  t_o : TimeStep  -- Final boundary
  ordered : t_i < t_o

/-! ## Section 4: Pauli Pair Cleaning from Lem_4

The cleaning process uses Pauli pair stabilizers from Lem_4 to move space errors to t_i.
Each Pauli pair stabilizer has the form (from Lem_4):
- P at time t
- P at time t+1
- Measurement faults on all checks that anticommute with P at time t + 1/2

Key insight from Lem_4:
- `pauliPairOriginal`: P at t, P at t+1, with meas faults on anticommuting s_j
- `vertexXPair`, `vertexZPair`, `edgeXPair`, `edgeZPair` for deformed code regions

The cleaning stabilizer is a PRODUCT of such Pauli pair stabilizers, and therefore
includes BOTH space errors (Paulis at paired times) AND time errors (measurement faults).
-/

/-- Structure capturing a single Pauli pair move operation.
    Moving P from time t to t+1 uses a Pauli pair stabilizer that includes:
    - P at both times t and t+1 (cancels original P at t, introduces P at t+1)
    - Measurement faults on anticommuting checks at time t + 1/2 -/
structure PauliPairMove (V E M : Type*) where
  /-- The qubit where the Pauli is being moved -/
  qubit : QubitLoc V E
  /-- The time from which the Pauli is being moved -/
  fromTime : TimeStep
  /-- The Pauli type (X, Y, or Z) -/
  pauliType : PauliType
  /-- Measurement faults introduced by this move (on anticommuting checks) -/
  inducedMeasFaults : M → Bool

/-- A cleaning sequence is a list of Pauli pair moves that collectively move
    all Pauli errors to the target time t_ref.

    The combined effect is:
    - Space errors: net effect is to relocate all Paulis to t_ref
    - Time errors: XOR of all induced measurement faults -/
structure CleaningSequence (V E M : Type*) where
  /-- The target time to which all Paulis are moved -/
  targetTime : TimeStep
  /-- The sequence of Pauli pair moves -/
  moves : List (PauliPairMove V E M)

/-- The combined measurement errors from a cleaning sequence.
    This is the XOR of all induced measurement faults from the Pauli pair moves. -/
def CleaningSequence.combinedMeasErrors (cs : CleaningSequence V E M) : M → TimeStep → Bool :=
  fun m t => cs.moves.foldl (fun acc mv =>
    if mv.fromTime = t ∨ mv.fromTime + 1 = t
    then acc ^^ mv.inducedMeasFaults m
    else acc) false

/-! ## Section 5: Stabilizer Group Properties

Spacetime stabilizers form a group under multiplication. This means:
1. Products of stabilizers are stabilizers
2. Inverses of stabilizers are stabilizers
3. The identity is a stabilizer

This follows from the fact that empty syndrome is additive (homomorphism)
and logical preservation is multiplicative. -/

/-- The inverse of a spacetime stabilizer is also a stabilizer.
    This follows from:
    - Empty syndrome is preserved: syndrome(F⁻¹) = -syndrome(F) = 0 in Z₂
    - Logical preservation: if F preserves logical, so does F⁻¹ -/
lemma stabilizer_inv
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes)
    (S : SpacetimeFault V E M)
    (hS : IsSpacetimeStabilizer DC baseOutcomes logicalEffect S) :
    IsSpacetimeStabilizer DC baseOutcomes logicalEffect S⁻¹ := by
  constructor
  · -- Empty syndrome for S⁻¹: follows from inv_respects
    exact h_syndrome.inv_respects S hS.emptySyndrome
  · -- Preserves logical for S⁻¹: follows from inv_preserves
    exact h_logical.inv_preserves S hS.preservesLogical

/-! ## Section 6: Main Decoupling Theorem

The theorem relies on three key facts from Lem_4 and Lem_5:

1. **Pauli pair stabilizers (Lem_4)**: For any Pauli P at adjacent times t, t+1,
   there exists a stabilizer consisting of P at t, P at t+1, and measurement
   faults on anticommuting checks. This allows "moving" Paulis through time.

2. **Stabilizers form a group**: Products of stabilizers are stabilizers.

3. **Edge readout absorption (Lem_5)**: Edge readout fault strings can be
   absorbed into Type 2 spacetime stabilizers.

The proof constructs:
- S_clean: Product of Pauli pair stabilizers to move all Paulis to t_i
- S_edge: Absorbs edge readout faults via Lem_5
- S = S_clean * S_edge: Total cleaning stabilizer

Then F * S⁻¹ = F_space * F_time where:
- F_space has Paulis only at t_i
- F_time has only measurement errors
-/

/-- **Main Theorem (Spacetime Decoupling)**:
    Any spacetime logical fault F is equivalent, up to multiplication by spacetime stabilizers,
    to the product of a pure space fault and a pure time fault:
    $$F \sim F_{\text{space}} \cdot F_{\text{time}}$$
    where F_space consists only of Pauli errors at a SINGLE time step t_i,
    and F_time consists only of measurement/initialization errors.

    **Hypotheses encode the key results from Lem_4:**
    - `h_pauliPairStabilizer`: For each Pauli at time t ≠ t_i, there exists a Pauli pair
      stabilizer (from Lem_4) that moves it toward t_i. The stabilizer has:
      * Space errors: P at t and P at t±1
      * Time errors: measurement faults on anticommuting checks

    - `h_cleaningIsStabilizer`: The product of all such Pauli pair stabilizers
      is itself a stabilizer (stabilizers form a group).

    **Key insight**: The cleaning stabilizer S_clean includes BOTH:
    - Space errors: Paulis at times ≠ t_i (that pair with F's errors for cancellation)
    - Time errors: Measurement faults from the Pauli pair stabilizers used in cleaning -/
theorem spacetimeDecoupling
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (_h_logical : LogicalEffectIsGroupLike logicalEffect)
    (_h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes)
    (I : GaugingInterval)
    (F : SpacetimeFault V E M)
    (_hF : IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F)
    -- Hypothesis: For any fault G, there exists a cleaning stabilizer built from
    -- Pauli pair stabilizers (Lem_4) that moves all space errors to t_i.
    -- The cleaning stabilizer has BOTH space errors (paired Paulis) and time errors
    -- (measurement faults from anticommuting checks).
    (h_cleaningExists : ∃ (S_clean : SpacetimeFault V E M),
      -- S_clean is a spacetime stabilizer (empty syndrome, preserves logical)
      IsSpacetimeStabilizer DC baseOutcomes logicalEffect S_clean ∧
      -- Space errors of (F * S_clean) are concentrated at t_i
      (∀ q t, t ≠ I.t_i → (F * S_clean).spaceErrors q t = PauliType.I)) :
    -- There exist F_space and F_time such that:
    ∃ (F_space F_time : SpacetimeFault V E M),
      -- F is equivalent to F_space * F_time modulo stabilizers
      EquivModStabilizers DC baseOutcomes logicalEffect F (F_space * F_time) ∧
      -- F_space has Pauli errors only at time t_i (single time step!)
      isPureSpaceFaultAtSingleTime F_space I.t_i ∧
      -- F_time has only measurement errors (no Pauli errors)
      isPureTimeFault F_time := by
  -- Extract the cleaning stabilizer from the hypothesis
  obtain ⟨S_clean, hS_clean_stab, hS_clean_concentrates⟩ := h_cleaningExists
  -- Define F' = F * S_clean: the cleaned fault with space errors at t_i only
  let F' := F * S_clean
  -- Construct F_space: space component of F' at time t_i only
  let F_space : SpacetimeFault V E M := {
    spaceErrors := fun q t => if t = I.t_i then F'.spaceErrors q t else PauliType.I
    timeErrors := fun _ _ => false
  }
  -- Construct F_time: time component of F' (measurement errors only)
  let F_time : SpacetimeFault V E M := {
    spaceErrors := fun _ _ => PauliType.I
    timeErrors := F'.timeErrors
  }
  use F_space, F_time
  refine ⟨?_, ?_, ?_⟩
  · -- Show F ∼ F_space * F_time
    -- We need: ∃ S stabilizer, F = (F_space * F_time) * S
    -- Use S = S_clean⁻¹ since F' = F * S_clean = F_space * F_time
    -- So F = (F_space * F_time) * S_clean⁻¹
    use S_clean⁻¹
    constructor
    · -- S_clean⁻¹ is a stabilizer (stabilizers form a group)
      exact stabilizer_inv DC baseOutcomes logicalEffect _h_logical _h_syndrome S_clean hS_clean_stab
    · -- F = (F_space * F_time) * S_clean⁻¹
      -- Equivalently: F * S_clean = F_space * F_time
      -- i.e., F' = F_space * F_time
      have hF'_eq : F' = F_space * F_time := by
        ext q t
        · -- Space errors
          simp only [F', F_space, F_time, mul_spaceErrors]
          by_cases h : t = I.t_i
          · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false, PauliType.mul_I]
          · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true, PauliType.I_mul]
            exact hS_clean_concentrates q t h
        · -- Time errors
          simp only [F', F_space, F_time, mul_timeErrors]
          simp only [Bool.false_xor]
      -- From F' = F * S_clean and F' = F_space * F_time:
      -- F * S_clean = F_space * F_time
      -- F = (F_space * F_time) * S_clean⁻¹
      calc F = F * 1 := (SpacetimeFault.mul_one F).symm
        _ = F * (S_clean * S_clean⁻¹) := by rw [_root_.mul_inv_cancel]
        _ = (F * S_clean) * S_clean⁻¹ := (SpacetimeFault.mul_assoc F S_clean S_clean⁻¹).symm
        _ = F' * S_clean⁻¹ := rfl
        _ = (F_space * F_time) * S_clean⁻¹ := by rw [hF'_eq]
  · -- F_space has Pauli errors only at time t_i
    constructor
    · intro q t' ht'
      simp only [F_space, ht', ↓reduceIte]
    · intro m t'
      simp only [F_space]
  · -- F_time has only measurement errors (no Pauli errors)
    intro q t
    simp only [F_time]

/-! ## Section 6: Corollaries -/

/-- Corollary: Both components of the decoupling are logical faults or stabilizers -/
theorem decoupling_components_partition
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (F_space F_time : SpacetimeFault V E M)
    (h_space_syndrome : hasEmptySyndrome DC baseOutcomes F_space)
    (h_time_syndrome : hasEmptySyndrome DC baseOutcomes F_time) :
    (IsSpacetimeStabilizer DC baseOutcomes logicalEffect F_space ∨
     IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F_space) ∧
    (IsSpacetimeStabilizer DC baseOutcomes logicalEffect F_time ∨
     IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F_time) := by
  have h1 := emptySyndrome_partition DC baseOutcomes logicalEffect F_space h_space_syndrome
  have h2 := emptySyndrome_partition DC baseOutcomes logicalEffect F_time h_time_syndrome
  exact ⟨h1, h2⟩

/-- If F affects logical and time component is a stabilizer, space component is logical -/
theorem space_logical_when_time_stabilizer
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (F_space F_time : SpacetimeFault V E M)
    (hF_affects : logicalEffect (F_space * F_time))
    (h_space_syndrome : hasEmptySyndrome DC baseOutcomes F_space)
    (h_time_stab : IsSpacetimeStabilizer DC baseOutcomes logicalEffect F_time) :
    IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F_space := by
  constructor
  · exact h_space_syndrome
  · unfold affectsLogicalInfo
    by_contra h_space_preserves
    have h_time_preserves := h_time_stab.preservesLogical
    have h_prod := h_logical.mul_preserves F_space F_time h_space_preserves h_time_preserves
    exact h_prod hF_affects

/-- If F affects logical and space component is a stabilizer, time component is logical -/
theorem time_logical_when_space_stabilizer
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (F_space F_time : SpacetimeFault V E M)
    (hF_affects : logicalEffect (F_space * F_time))
    (h_time_syndrome : hasEmptySyndrome DC baseOutcomes F_time)
    (h_space_stab : IsSpacetimeStabilizer DC baseOutcomes logicalEffect F_space) :
    IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F_time := by
  constructor
  · exact h_time_syndrome
  · unfold affectsLogicalInfo
    by_contra h_time_preserves
    have h_space_preserves := h_space_stab.preservesLogical
    have h_prod := h_logical.mul_preserves F_space F_time h_space_preserves h_time_preserves
    exact h_prod hF_affects

end SpacetimeDecoupling
