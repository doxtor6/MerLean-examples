import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_8_Detector

/-!
# Def_10: Spacetime Logical Fault

## Statement
A **spacetime logical fault** is a collection of space-faults and time-faults that:
1. Does not violate any detector (has empty syndrome), AND
2. Causes a logical error, i.e., changes the outcome of the gauging measurement or introduces
   a logical Pauli error on the encoded quantum information.

A **spacetime stabilizer** is a collection of space-faults and time-faults that:
1. Does not violate any detector (has empty syndrome), AND
2. Does NOT affect the logical information or measurement outcome.

Every fault with empty syndrome is either a spacetime stabilizer (trivial) or a spacetime logical
fault (non-trivial). The set of spacetime stabilizers forms a group, and two faults are
**equivalent** if they differ by a spacetime stabilizer.

## Main Definitions
- `Syndrome` : The set of detectors violated by a spacetime fault
- `hasEmptySyndrome` : Whether a fault has empty syndrome (violates no detectors)
- `IsSpacetimeStabilizer` : Faults with empty syndrome that don't affect logical information
- `IsSpacetimeLogicalFault` : Faults with empty syndrome that DO affect logical information
- `FaultEquivalent` : Equivalence relation where faults differ by a stabilizer

## Key Properties
- `spacetimeStabilizerSubgroup` : Spacetime stabilizers form a subgroup
- `emptySyndrome_partition` : Empty-syndrome faults partition into stabilizers and logical faults
- `faultEquivalent_equivalence` : Fault equivalence is an equivalence relation
-/

open Finset

set_option linter.unusedSectionVars false

/-! ## Syndrome

The syndrome of a spacetime fault is the set of detectors it violates. -/

variable {V E M : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq M]

/-- Apply a spacetime fault to measurement outcomes. Time-faults flip outcomes. -/
def applyFaultToOutcomes
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) : OutcomeAssignment M :=
  fun m t => if fault.timeErrors m t then baseOutcomes m t + 1 else baseOutcomes m t

/-- Compute the syndrome of a spacetime fault given a detector collection.
    The syndrome is the set of detectors violated by the fault. -/
def computeSyndrome
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) : Finset (Detector V E M) :=
  DC.detectors.filter fun D => D.isViolated (applyFaultToOutcomes baseOutcomes fault)

/-- The syndrome as a predicate on detectors -/
def inSyndrome
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M)
    (D : Detector V E M) : Prop :=
  D ∈ computeSyndrome DC baseOutcomes fault

/-- A fault has empty syndrome if it violates no detectors -/
def hasEmptySyndrome
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) : Prop :=
  computeSyndrome DC baseOutcomes fault = ∅

instance decHasEmptySyndrome
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) :
    Decidable (hasEmptySyndrome DC baseOutcomes fault) :=
  inferInstanceAs (Decidable (_ = ∅))

@[simp]
lemma hasEmptySyndrome_iff
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) :
    hasEmptySyndrome DC baseOutcomes fault ↔
    ∀ D ∈ DC.detectors, D.isSatisfied (applyFaultToOutcomes baseOutcomes fault) := by
  unfold hasEmptySyndrome computeSyndrome
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h D hD
    rw [Detector.satisfied_iff_not_violated]
    exact h hD
  · intro h D hD
    rw [← Detector.satisfied_iff_not_violated]
    exact h D hD

/-! ## Identity fault has empty syndrome -/

/-- The identity fault has empty syndrome (in any fault-free base outcome setting) -/
theorem identity_hasEmptySyndrome
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (h_base : DC.allSatisfied baseOutcomes) :
    hasEmptySyndrome DC baseOutcomes (1 : SpacetimeFault V E M) := by
  rw [hasEmptySyndrome_iff]
  intro D hD
  have heq : applyFaultToOutcomes baseOutcomes (1 : SpacetimeFault V E M) = baseOutcomes := by
    funext m t
    simp only [applyFaultToOutcomes, SpacetimeFault.one_timeErrors]
    rfl
  rw [heq]
  rw [DetectorCollection.allSatisfied_iff] at h_base
  exact h_base D hD

/-! ## Logical Effect Predicate

To distinguish spacetime stabilizers from logical faults, we need a notion of
"affecting logical information". We model this abstractly. -/

/-- Abstract predicate: whether a fault affects the logical information.
    This captures:
    - Changes to the gauging measurement outcome
    - Introduction of logical Pauli errors on encoded qubits

    In practice, this is determined by the code structure and logical operators. -/
def affectsLogicalInfo
    (logicalEffect : SpacetimeFault V E M → Prop) (fault : SpacetimeFault V E M) : Prop :=
  logicalEffect fault

/-- The negation: fault does NOT affect logical info -/
def preservesLogicalInfo
    (logicalEffect : SpacetimeFault V E M → Prop) (fault : SpacetimeFault V E M) : Prop :=
  ¬logicalEffect fault

/-! ## Spacetime Stabilizers

Spacetime stabilizers are faults with empty syndrome that preserve logical information. -/

/-- A spacetime stabilizer: empty syndrome AND preserves logical information -/
structure IsSpacetimeStabilizer
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (fault : SpacetimeFault V E M) : Prop where
  /-- The fault has empty syndrome (violates no detectors) -/
  emptySyndrome : hasEmptySyndrome DC baseOutcomes fault
  /-- The fault preserves logical information -/
  preservesLogical : preservesLogicalInfo logicalEffect fault

/-- The set of spacetime stabilizers as a set -/
def spacetimeStabilizerSet
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop) : Set (SpacetimeFault V E M) :=
  { f | IsSpacetimeStabilizer DC baseOutcomes logicalEffect f }

/-! ## Spacetime Logical Faults

Spacetime logical faults are faults with empty syndrome that DO affect logical information. -/

/-- A spacetime logical fault: empty syndrome AND affects logical information -/
structure IsSpacetimeLogicalFault
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (fault : SpacetimeFault V E M) : Prop where
  /-- The fault has empty syndrome (violates no detectors) -/
  emptySyndrome : hasEmptySyndrome DC baseOutcomes fault
  /-- The fault DOES affect logical information -/
  affectsLogical : affectsLogicalInfo logicalEffect fault

/-- The set of spacetime logical faults as a set -/
def spacetimeLogicalFaultSet
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop) : Set (SpacetimeFault V E M) :=
  { f | IsSpacetimeLogicalFault DC baseOutcomes logicalEffect f }

/-! ## Partition of Empty-Syndrome Faults

Every fault with empty syndrome is either a stabilizer or a logical fault. -/

/-- The set of faults with empty syndrome -/
def emptySyndromeSet
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M) : Set (SpacetimeFault V E M) :=
  { f | hasEmptySyndrome DC baseOutcomes f }

/-- Stabilizers and logical faults partition the empty-syndrome faults -/
theorem emptySyndrome_partition
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (f : SpacetimeFault V E M)
    (h_empty : hasEmptySyndrome DC baseOutcomes f) :
    IsSpacetimeStabilizer DC baseOutcomes logicalEffect f ∨
    IsSpacetimeLogicalFault DC baseOutcomes logicalEffect f := by
  by_cases hlog : logicalEffect f
  · right
    exact ⟨h_empty, hlog⟩
  · left
    exact ⟨h_empty, hlog⟩

/-- Stabilizers and logical faults are disjoint -/
theorem stabilizer_logicalFault_disjoint
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (f : SpacetimeFault V E M) :
    ¬(IsSpacetimeStabilizer DC baseOutcomes logicalEffect f ∧
      IsSpacetimeLogicalFault DC baseOutcomes logicalEffect f) := by
  intro ⟨hstab, hlog⟩
  exact hstab.preservesLogical hlog.affectsLogical

/-- Union of stabilizers and logical faults equals empty-syndrome set -/
theorem stabilizer_logicalFault_union
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop) :
    spacetimeStabilizerSet DC baseOutcomes logicalEffect ∪
    spacetimeLogicalFaultSet DC baseOutcomes logicalEffect =
    emptySyndromeSet DC baseOutcomes := by
  ext f
  simp only [Set.mem_union, spacetimeStabilizerSet, spacetimeLogicalFaultSet,
             emptySyndromeSet, Set.mem_setOf_eq]
  constructor
  · intro h
    cases h with
    | inl h => exact h.emptySyndrome
    | inr h => exact h.emptySyndrome
  · intro h_empty
    exact emptySyndrome_partition DC baseOutcomes logicalEffect f h_empty

/-! ## Spacetime Stabilizers Form a Subgroup

Under appropriate conditions on the logical effect predicate, spacetime stabilizers
form a subgroup of all spacetime faults. -/

/-- Condition: logical effect is preserved under product (group-like) -/
structure LogicalEffectIsGroupLike
    (logicalEffect : SpacetimeFault V E M → Prop) : Prop where
  /-- Identity preserves logical info -/
  identity_preserves : ¬logicalEffect (1 : SpacetimeFault V E M)
  /-- Product of two stabilizers is a stabilizer (closure under multiplication) -/
  mul_preserves : ∀ f g, ¬logicalEffect f → ¬logicalEffect g → ¬logicalEffect (f * g)
  /-- Inverse of a stabilizer is a stabilizer -/
  inv_preserves : ∀ f, ¬logicalEffect f → ¬logicalEffect f⁻¹

/-- Condition: syndrome computation respects the group structure -/
structure SyndromeIsGroupHomomorphism
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M) : Prop where
  /-- Identity has empty syndrome -/
  identity_empty : hasEmptySyndrome DC baseOutcomes (1 : SpacetimeFault V E M)
  /-- Product respects syndrome -/
  mul_respects : ∀ f g, hasEmptySyndrome DC baseOutcomes f → hasEmptySyndrome DC baseOutcomes g →
          hasEmptySyndrome DC baseOutcomes (f * g)
  /-- Inverse respects syndrome -/
  inv_respects : ∀ f, hasEmptySyndrome DC baseOutcomes f → hasEmptySyndrome DC baseOutcomes f⁻¹

/-- Spacetime stabilizers form a subgroup under the right conditions -/
def spacetimeStabilizerSubgroup
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes) :
    Subgroup (SpacetimeFault V E M) where
  carrier := spacetimeStabilizerSet DC baseOutcomes logicalEffect
  mul_mem' := by
    intro f g hf hg
    simp only [spacetimeStabilizerSet, Set.mem_setOf_eq] at *
    constructor
    · exact h_syndrome.mul_respects f g hf.emptySyndrome hg.emptySyndrome
    · exact h_logical.mul_preserves f g hf.preservesLogical hg.preservesLogical
  one_mem' := by
    simp only [spacetimeStabilizerSet, Set.mem_setOf_eq]
    constructor
    · exact h_syndrome.identity_empty
    · exact h_logical.identity_preserves
  inv_mem' := by
    intro f hf
    simp only [spacetimeStabilizerSet, Set.mem_setOf_eq] at *
    constructor
    · exact h_syndrome.inv_respects f hf.emptySyndrome
    · exact h_logical.inv_preserves f hf.preservesLogical

/-! ## Fault Equivalence

Two faults are equivalent if they differ by a spacetime stabilizer.
This forms an equivalence relation. -/

/-- Two faults are equivalent if they differ by a spacetime stabilizer -/
def FaultEquivalent
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (f g : SpacetimeFault V E M) : Prop :=
  IsSpacetimeStabilizer DC baseOutcomes logicalEffect (f⁻¹ * g)

/-- Fault equivalence is reflexive -/
theorem faultEquivalent_refl
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes)
    (f : SpacetimeFault V E M) :
    FaultEquivalent DC baseOutcomes logicalEffect f f := by
  unfold FaultEquivalent
  simp only [inv_mul_cancel]
  exact (spacetimeStabilizerSubgroup DC baseOutcomes logicalEffect h_logical h_syndrome).one_mem'

/-- Fault equivalence is symmetric -/
theorem faultEquivalent_symm
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes)
    (f g : SpacetimeFault V E M)
    (h : FaultEquivalent DC baseOutcomes logicalEffect f g) :
    FaultEquivalent DC baseOutcomes logicalEffect g f := by
  unfold FaultEquivalent at *
  have eq : (g⁻¹ * f) = (f⁻¹ * g)⁻¹ := by
    simp only [mul_inv_rev, inv_inv]
  rw [eq]
  exact (spacetimeStabilizerSubgroup DC baseOutcomes logicalEffect h_logical h_syndrome).inv_mem' h

/-- Fault equivalence is transitive -/
theorem faultEquivalent_trans
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes)
    (f g k : SpacetimeFault V E M)
    (hfg : FaultEquivalent DC baseOutcomes logicalEffect f g)
    (hgk : FaultEquivalent DC baseOutcomes logicalEffect g k) :
    FaultEquivalent DC baseOutcomes logicalEffect f k := by
  unfold FaultEquivalent at *
  have key : (f⁻¹ * k) = (f⁻¹ * g) * (g⁻¹ * k) := by
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [key]
  exact (spacetimeStabilizerSubgroup DC baseOutcomes logicalEffect h_logical h_syndrome).mul_mem' hfg hgk

/-- Fault equivalence is an equivalence relation -/
theorem faultEquivalent_equivalence
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes) :
    Equivalence (FaultEquivalent DC baseOutcomes logicalEffect) :=
  ⟨faultEquivalent_refl DC baseOutcomes logicalEffect h_logical h_syndrome,
   fun h => faultEquivalent_symm DC baseOutcomes logicalEffect h_logical h_syndrome _ _ h,
   fun h1 h2 => faultEquivalent_trans DC baseOutcomes logicalEffect h_logical h_syndrome _ _ _ h1 h2⟩

/-- Fault equivalence as a Setoid -/
def faultSetoid
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes) :
    Setoid (SpacetimeFault V E M) :=
  ⟨FaultEquivalent DC baseOutcomes logicalEffect,
   faultEquivalent_equivalence DC baseOutcomes logicalEffect h_logical h_syndrome⟩

/-! ## Equivalence Classes as Cosets

Fault equivalence classes correspond to cosets of the stabilizer subgroup. -/

/-- The quotient by fault equivalence is the quotient by the stabilizer subgroup -/
def FaultQuotient
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (h_syndrome : SyndromeIsGroupHomomorphism DC baseOutcomes) :=
  (SpacetimeFault V E M) ⧸
    (spacetimeStabilizerSubgroup DC baseOutcomes logicalEffect h_logical h_syndrome)

/-! ## Characterization: Logical Fault iff Non-trivial Coset

A fault is a logical fault iff it represents a non-trivial coset in the quotient. -/

/-- A fault with empty syndrome is a spacetime logical fault iff it's NOT a stabilizer -/
theorem isLogicalFault_iff_not_stabilizer
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (f : SpacetimeFault V E M)
    (h_empty : hasEmptySyndrome DC baseOutcomes f) :
    IsSpacetimeLogicalFault DC baseOutcomes logicalEffect f ↔
    ¬IsSpacetimeStabilizer DC baseOutcomes logicalEffect f := by
  constructor
  · intro hlog hstab
    exact hstab.preservesLogical hlog.affectsLogical
  · intro hnotStab
    constructor
    · exact h_empty
    · by_contra hnoEffect
      apply hnotStab
      exact ⟨h_empty, hnoEffect⟩

/-! ## Summary

This formalization captures:

1. **Syndrome**: The set of detectors violated by a fault.

2. **Spacetime Stabilizers**: Faults with empty syndrome that preserve logical information.
   These form a subgroup under appropriate conditions.

3. **Spacetime Logical Faults**: Faults with empty syndrome that DO affect logical information.

4. **Partition**: Every empty-syndrome fault is either a stabilizer or a logical fault.

5. **Fault Equivalence**: Two faults are equivalent if they differ by a stabilizer.
   This is an equivalence relation.
-/
