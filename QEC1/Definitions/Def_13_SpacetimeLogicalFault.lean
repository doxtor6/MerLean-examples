import QEC1.Definitions.Def_12_Detector

/-!
# Spacetime Logical Fault (Definition 13)

## Statement
A **spacetime logical fault** is a collection of space and time faults that:
(i) Does not violate any detector: syn(F) = ∅
(ii) Is not a spacetime stabilizer (see Def_14)

Intuitively, a spacetime logical fault is an undetectable error that affects the computation result.

## Main Results
**Main Definition** (`isUndetectable`): When a fault has empty syndrome
**Main Predicate** (`IsSpacetimeLogicalFault`): Predicate characterizing spacetime logical faults
**Main Structure** (`SpacetimeLogicalFault`): A spacetime fault that is undetectable but non-trivial

## File Structure
1. Undetectable Faults: Faults with empty syndrome
2. Spacetime Logical Fault: Undetectable faults that are not spacetime stabilizers
3. Helper Lemmas: Basic properties

## Design Note
The predicate `IsSpacetimeStabilizer` is taken as a parameter in this definition.
Definition 14 provides the concrete characterization of spacetime stabilizers
(faults that act trivially on the computation via generator decomposition).
This parameterization ensures faithfulness: the mathematical definition says
"not a spacetime stabilizer (see Def_14)" and we capture this by abstracting
over the stabilizer predicate.
-/

namespace QEC

/-! ## Section 1: Undetectable Faults -/

/-- A spacetime fault is **undetectable** if it does not violate any detector.
    This means syn(F) = ∅ - the syndrome is empty. -/
def isUndetectable {n m : ℕ} (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) : Prop :=
  syndromeFinset F detectors = ∅

/-- Equivalently, undetectable means the syndrome weight is zero -/
theorem isUndetectable_iff_syndromeWeight_zero {n m : ℕ} (F : SpaceTimeFault n m)
    (detectors : Finset (Detector n)) :
    isUndetectable F detectors ↔ syndromeWeight F detectors = 0 := by
  unfold isUndetectable syndromeWeight
  rw [Finset.card_eq_zero]

/-- Undetectable means no detector is violated -/
theorem isUndetectable_iff_no_violation {n m : ℕ} (F : SpaceTimeFault n m)
    (detectors : Finset (Detector n)) :
    isUndetectable F detectors ↔ ∀ D ∈ detectors, ¬violates F D := by
  unfold isUndetectable syndromeFinset
  simp only [Finset.filter_eq_empty_iff]

/-- The empty fault is undetectable -/
@[simp]
theorem empty_isUndetectable (detectors : Finset (Detector n)) :
    isUndetectable (SpaceTimeFault.empty : SpaceTimeFault n m) detectors := by
  unfold isUndetectable
  exact syndrome_empty detectors

/-! ## Section 2: Spacetime Logical Fault

A spacetime logical fault is an undetectable fault that is NOT a spacetime stabilizer.
The stabilizer predicate is provided as a parameter since its full characterization
is given in Definition 14 (involving generator decomposition and trivial action on
the computation). This design ensures faithful representation of the original
mathematical definition. -/

/-- A **spacetime logical fault** is a collection of space and time faults that:
    (i) Does not violate any detector: syn(F) = ∅
    (ii) Is not a spacetime stabilizer

    The stabilizer predicate `isStabilizer` determines which undetectable faults
    act trivially on the computation. Per Definition 14, this involves checking
    whether the fault can be decomposed into products of code stabilizer generators
    and matching time fault pairs. -/
def IsSpacetimeLogicalFault {n m : ℕ}
    (isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop)
    (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) : Prop :=
  isUndetectable F detectors ∧ ¬isStabilizer F detectors

/-- Structure bundling a spacetime fault with the property of being a logical fault.
    This packages together:
    - A spacetime fault F
    - Proof that F is undetectable
    - Proof that F is not a spacetime stabilizer

    The stabilizer predicate is provided as a parameter. -/
structure SpacetimeLogicalFault (n m : ℕ) (detectors : Finset (Detector n))
    (isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop) where
  /-- The underlying spacetime fault -/
  fault : SpaceTimeFault n m
  /-- The fault is undetectable (empty syndrome) -/
  undetectable : isUndetectable fault detectors
  /-- The fault is not a spacetime stabilizer -/
  notStabilizer : ¬isStabilizer fault detectors

namespace SpacetimeLogicalFault

variable {n m : ℕ} {detectors : Finset (Detector n)}
variable {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}

/-- A spacetime logical fault satisfies the predicate -/
theorem isLogicalFault (F : SpacetimeLogicalFault n m detectors isStabilizer) :
    IsSpacetimeLogicalFault isStabilizer F.fault detectors :=
  ⟨F.undetectable, F.notStabilizer⟩

/-- The weight of a spacetime logical fault -/
def weight (F : SpacetimeLogicalFault n m detectors isStabilizer) : ℕ :=
  F.fault.weight

/-- Extract from a fault satisfying the predicate -/
def ofIsLogicalFault {F : SpaceTimeFault n m}
    (h : IsSpacetimeLogicalFault isStabilizer F detectors) :
    SpacetimeLogicalFault n m detectors isStabilizer where
  fault := F
  undetectable := h.1
  notStabilizer := h.2

/-- The syndrome of a spacetime logical fault is empty -/
@[simp]
theorem syndrome_empty (F : SpacetimeLogicalFault n m detectors isStabilizer) :
    syndromeFinset F.fault detectors = ∅ :=
  F.undetectable

/-- A spacetime logical fault has zero syndrome weight -/
@[simp]
theorem syndromeWeight_eq_zero (F : SpacetimeLogicalFault n m detectors isStabilizer) :
    syndromeWeight F.fault detectors = 0 := by
  rw [← isUndetectable_iff_syndromeWeight_zero]
  exact F.undetectable

/-- A spacetime logical fault violates no detector -/
theorem no_violation (F : SpacetimeLogicalFault n m detectors isStabilizer) :
    ∀ D ∈ detectors, ¬violates F.fault D := by
  rw [← isUndetectable_iff_no_violation]
  exact F.undetectable

end SpacetimeLogicalFault

/-! ## Section 3: Properties of Logical Faults -/

/-- A fault cannot be both a spacetime stabilizer and a spacetime logical fault -/
theorem not_both_stabilizer_and_logical {n m : ℕ}
    {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}
    (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) :
    ¬(isStabilizer F detectors ∧ IsSpacetimeLogicalFault isStabilizer F detectors) := by
  intro ⟨hStab, hLog⟩
  exact hLog.2 hStab

/-- Undetectable faults partition into stabilizers and logical faults -/
theorem undetectable_stabilizer_or_logical {n m : ℕ}
    {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}
    (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (h : isUndetectable F detectors) :
    isStabilizer F detectors ∨ IsSpacetimeLogicalFault isStabilizer F detectors := by
  by_cases hStab : isStabilizer F detectors
  · left; exact hStab
  · right; exact ⟨h, hStab⟩

/-- The empty fault is a logical fault iff it is not a stabilizer -/
theorem empty_isLogicalFault_iff {n m : ℕ}
    {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}
    (detectors : Finset (Detector n)) :
    IsSpacetimeLogicalFault isStabilizer (SpaceTimeFault.empty : SpaceTimeFault n m) detectors ↔
    ¬isStabilizer SpaceTimeFault.empty detectors := by
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨empty_isUndetectable detectors, h⟩

/-! ## Section 4: Consistency Properties

These theorems establish basic consistency properties that any reasonable
instantiation of `isStabilizer` should satisfy. -/

/-- If the stabilizer predicate includes all undetectable faults, there are no logical faults -/
theorem no_logical_faults_if_all_undetectable_are_stabilizers {n m : ℕ}
    {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}
    (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (h : ∀ G, isUndetectable G detectors → isStabilizer G detectors) :
    ¬IsSpacetimeLogicalFault isStabilizer F detectors := by
  intro ⟨hUndet, hNotStab⟩
  exact hNotStab (h F hUndet)

/-- A stabilizer predicate that is trivially false makes all undetectable faults logical -/
theorem all_undetectable_logical_if_no_stabilizers {n m : ℕ}
    (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (h : isUndetectable F detectors) :
    IsSpacetimeLogicalFault (fun _ _ => False) F detectors := by
  exact ⟨h, fun hf => hf⟩

/-! ## Section 5: Fault Distance Motivation

The spacetime fault-distance will be defined (Def_15) as:
  d_ST = min{|F| : F is a spacetime logical fault}

This represents the minimum weight of an undetectable fault pattern that
is not equivalent to a spacetime stabilizer. -/

/-- The existence of a logical fault with weight w means d_ST ≤ w -/
theorem fault_distance_upper_bound {n m : ℕ}
    {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}
    (detectors : Finset (Detector n))
    (F : SpacetimeLogicalFault n m detectors isStabilizer) (w : ℕ) (hw : F.weight ≤ w) :
    ∃ (G : SpaceTimeFault n m), IsSpacetimeLogicalFault isStabilizer G detectors ∧ G.weight ≤ w :=
  ⟨F.fault, F.isLogicalFault, hw⟩

/-! ## Section 6: Helper Lemmas -/

/-- Decidability of isUndetectable -/
instance instDecidableIsUndetectable {n m : ℕ}
    (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) :
    Decidable (isUndetectable F detectors) :=
  inferInstanceAs (Decidable (_ = _))

/-- The weight of a logical fault is non-negative -/
theorem logical_fault_weight_nonneg {n m : ℕ} {detectors : Finset (Detector n)}
    {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}
    (F : SpacetimeLogicalFault n m detectors isStabilizer) :
    0 ≤ F.weight :=
  Nat.zero_le _

/-- If there are no detectors, every fault is undetectable -/
theorem isUndetectable_of_empty_detectors {n m : ℕ} (F : SpaceTimeFault n m) :
    isUndetectable F (∅ : Finset (Detector n)) := by
  unfold isUndetectable syndromeFinset
  simp

/-- Two spacetime logical faults with the same underlying fault are equal -/
theorem SpacetimeLogicalFault_ext {n m : ℕ} {detectors : Finset (Detector n)}
    {isStabilizer : SpaceTimeFault n m → Finset (Detector n) → Prop}
    (F G : SpacetimeLogicalFault n m detectors isStabilizer)
    (h : F.fault = G.fault) : F = G := by
  cases F
  cases G
  simp only at h
  subst h
  rfl

end QEC
