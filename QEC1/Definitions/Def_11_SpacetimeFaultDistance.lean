import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.WellFoundedSet

import QEC1.Definitions.Def_10_SpacetimeLogicalFault

/-!
# Def_11: Spacetime Fault-Distance

## Statement
The **spacetime fault-distance** of the fault-tolerant gauging measurement procedure is defined as:
$$d_{\text{spacetime}} = \min\{|F| : F \text{ is a spacetime logical fault}\}$$
where $|F|$ denotes the weight of $F$, counted as the total number of:
- Single-qubit Pauli errors (each $X$, $Y$, or $Z$ error on one qubit at one time counts as weight 1), plus
- Single measurement errors (each incorrectly reported measurement counts as weight 1), plus
- Single initialization errors (each faulty initialization counts as weight 1).

Intuitively, $d_{\text{spacetime}}$ is the minimum number of independent faults required to cause a
logical error without being detected.

## Main Definitions
- `logicalFaultWeights` : The set of weights of all spacetime logical faults
- `hasLogicalFault` : Predicate that there exists at least one spacetime logical fault
- `spacetimeFaultDistance` : The minimum weight d_ST of any spacetime logical fault

## Key Properties
- `spacetimeFaultDistance_le_weight` : d_ST ≤ weight of any logical fault
- `spacetimeFaultDistance_is_min` : d_ST is achieved by some logical fault
- `not_logical_of_weight_lt` : Faults with weight < d_ST cannot be logical faults
- `spacetimeFaultDistance_pos_iff` : Characterization of when d_ST > 0
-/

open Finset

set_option linter.unusedSectionVars false

variable {V E M : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq M]

/-! ## Section 1: Set of Logical Fault Weights

We define the set of weights of all spacetime logical faults. The spacetime fault-distance
is the minimum of this set. -/

/-- The set of weights of spacetime logical faults.
    W = {|F| : F is a spacetime logical fault} -/
def logicalFaultWeights
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep) : Set ℕ :=
  { w | ∃ F : SpacetimeFault V E M,
        IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F ∧ F.weight times = w }

/-- The set of weights of all empty-syndrome (undetectable) non-stabilizer faults -/
def undetectableNonStabilizerWeights
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep) : Set ℕ :=
  { w | ∃ F : SpacetimeFault V E M,
        hasEmptySyndrome DC baseOutcomes F ∧
        affectsLogicalInfo logicalEffect F ∧
        F.weight times = w }

/-- The two weight sets are equal by definition of logical fault -/
theorem logicalFaultWeights_eq_undetectableNonStabilizer
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep) :
    logicalFaultWeights DC baseOutcomes logicalEffect times =
    undetectableNonStabilizerWeights DC baseOutcomes logicalEffect times := by
  ext w
  simp only [logicalFaultWeights, undetectableNonStabilizerWeights,
             IsSpacetimeLogicalFault, Set.mem_setOf_eq]
  constructor
  · intro ⟨F, ⟨hF_empty, hF_logical⟩, heq⟩
    exact ⟨F, hF_empty, hF_logical, heq⟩
  · intro ⟨F, hF_empty, hF_logical, heq⟩
    exact ⟨F, ⟨hF_empty, hF_logical⟩, heq⟩

/-! ## Section 2: Predicate for Existence of Logical Faults -/

/-- Predicate: there exists at least one spacetime logical fault -/
def hasLogicalFault
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop) : Prop :=
  ∃ F : SpacetimeFault V E M, IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F

/-- Nonemptiness of logical fault weights implies existence of logical faults -/
lemma hasLogicalFault_of_weights_nonempty
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (h : (logicalFaultWeights DC baseOutcomes logicalEffect times).Nonempty) :
    hasLogicalFault DC baseOutcomes logicalEffect := by
  obtain ⟨w, F, hF, _⟩ := h
  exact ⟨F, hF⟩

/-- Existence of logical faults implies nonemptiness of weights -/
lemma weights_nonempty_of_hasLogicalFault
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (h : hasLogicalFault DC baseOutcomes logicalEffect) :
    (logicalFaultWeights DC baseOutcomes logicalEffect times).Nonempty := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.weight times, F, hF, rfl⟩

/-! ## Section 3: Spacetime Fault Distance Definition

The spacetime fault-distance is the minimum weight of any spacetime logical fault. -/

/-- The spacetime fault-distance d_ST as a natural number.
    d_ST = min{|F| : F is a spacetime logical fault}

    If no logical faults exist (which would mean perfect error correction),
    we return 0 as a sentinel value. In practice, interesting codes always
    have logical faults, so d_ST > 0.

    We define this using WellFounded.min on the set of logical fault weights. -/
noncomputable def spacetimeFaultDistance
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep) : ℕ :=
  @dite _ (hasLogicalFault DC baseOutcomes logicalEffect) (Classical.dec _)
    (fun h => WellFounded.min Nat.lt_wfRel.wf
      (logicalFaultWeights DC baseOutcomes logicalEffect times)
      (weights_nonempty_of_hasLogicalFault DC baseOutcomes logicalEffect times h))
    (fun _ => 0)

/-! ## Section 4: Main Properties -/

/-- The spacetime fault distance is at most the weight of any logical fault -/
theorem spacetimeFaultDistance_le_weight
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (F : SpacetimeFault V E M)
    (hF : IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F) :
    spacetimeFaultDistance DC baseOutcomes logicalEffect times ≤ F.weight times := by
  unfold spacetimeFaultDistance
  have hhas : hasLogicalFault DC baseOutcomes logicalEffect := ⟨F, hF⟩
  rw [dif_pos hhas]
  apply WellFounded.min_le
  exact ⟨F, hF, rfl⟩

/-- The spacetime fault distance is a lower bound: all logical faults have weight ≥ d_ST -/
theorem weight_ge_spacetimeFaultDistance
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (F : SpacetimeFault V E M)
    (hF : IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F) :
    F.weight times ≥ spacetimeFaultDistance DC baseOutcomes logicalEffect times :=
  spacetimeFaultDistance_le_weight DC baseOutcomes logicalEffect times F hF

/-- If logical faults exist, the minimum is achieved -/
theorem spacetimeFaultDistance_is_min
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (h : hasLogicalFault DC baseOutcomes logicalEffect) :
    ∃ F : SpacetimeFault V E M,
      IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F ∧
      F.weight times = spacetimeFaultDistance DC baseOutcomes logicalEffect times := by
  unfold spacetimeFaultDistance
  rw [dif_pos h]
  have hne : (logicalFaultWeights DC baseOutcomes logicalEffect times).Nonempty :=
    weights_nonempty_of_hasLogicalFault DC baseOutcomes logicalEffect times h
  have hmin := WellFounded.min_mem Nat.lt_wfRel.wf
    (logicalFaultWeights DC baseOutcomes logicalEffect times) hne
  obtain ⟨F, hFlog, hFw⟩ := hmin
  exact ⟨F, hFlog, hFw⟩

/-- If no logical faults exist, d_ST = 0 -/
theorem spacetimeFaultDistance_zero_of_no_logical
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (h : ¬hasLogicalFault DC baseOutcomes logicalEffect) :
    spacetimeFaultDistance DC baseOutcomes logicalEffect times = 0 := by
  unfold spacetimeFaultDistance
  rw [dif_neg h]

/-! ## Section 5: Faults Below Distance Cannot Be Logical -/

/-- A fault with weight < d_ST cannot be a logical fault -/
theorem not_logical_of_weight_lt
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (F : SpacetimeFault V E M)
    (hF : F.weight times < spacetimeFaultDistance DC baseOutcomes logicalEffect times) :
    ¬IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F := by
  intro hlog
  have hge := spacetimeFaultDistance_le_weight DC baseOutcomes logicalEffect times F hlog
  omega

/-- A fault with weight < d_ST is either detectable or a stabilizer -/
theorem detectable_or_stabilizer_if_weight_lt
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (F : SpacetimeFault V E M)
    (hF : F.weight times < spacetimeFaultDistance DC baseOutcomes logicalEffect times) :
    ¬hasEmptySyndrome DC baseOutcomes F ∨
    ¬affectsLogicalInfo logicalEffect F := by
  by_contra h
  push_neg at h
  have hlog : IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F := ⟨h.1, h.2⟩
  exact not_logical_of_weight_lt DC baseOutcomes logicalEffect times F hF hlog

/-! ## Section 6: Characterization of Positive Distance -/

/-- d_ST > 0 iff there exist logical faults and all have positive weight -/
theorem spacetimeFaultDistance_pos_iff
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep) :
    0 < spacetimeFaultDistance DC baseOutcomes logicalEffect times ↔
    hasLogicalFault DC baseOutcomes logicalEffect ∧
    ∀ F : SpacetimeFault V E M,
      IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F → 0 < F.weight times := by
  constructor
  · intro hpos
    constructor
    · by_contra h
      rw [spacetimeFaultDistance_zero_of_no_logical DC baseOutcomes logicalEffect times h] at hpos
      exact Nat.not_lt_zero 0 hpos
    · intro F hF
      have hge := spacetimeFaultDistance_le_weight DC baseOutcomes logicalEffect times F hF
      omega
  · intro ⟨hhas, hpos⟩
    obtain ⟨F, hF, heq⟩ := spacetimeFaultDistance_is_min DC baseOutcomes logicalEffect times hhas
    rw [← heq]
    exact hpos F hF

/-! ## Section 7: Helper Lemmas -/

/-- The spacetime fault distance is non-negative -/
@[simp]
theorem spacetimeFaultDistance_nonneg
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep) :
    0 ≤ spacetimeFaultDistance DC baseOutcomes logicalEffect times :=
  Nat.zero_le _

/-- Logical fault weights are bounded below by d_ST -/
theorem logicalFaultWeights_bounded_below
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep) :
    ∀ w ∈ logicalFaultWeights DC baseOutcomes logicalEffect times,
      spacetimeFaultDistance DC baseOutcomes logicalEffect times ≤ w := by
  intro w hw
  obtain ⟨F, hF, heq⟩ := hw
  rw [← heq]
  exact spacetimeFaultDistance_le_weight DC baseOutcomes logicalEffect times F hF

/-- d_ST ∈ logicalFaultWeights when logical faults exist -/
theorem spacetimeFaultDistance_mem_weights
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (h : hasLogicalFault DC baseOutcomes logicalEffect) :
    spacetimeFaultDistance DC baseOutcomes logicalEffect times ∈
      logicalFaultWeights DC baseOutcomes logicalEffect times := by
  obtain ⟨F, hF, heq⟩ := spacetimeFaultDistance_is_min DC baseOutcomes logicalEffect times h
  exact ⟨F, hF, heq⟩

/-- A fault of weight exactly d_ST exists when logical faults exist -/
theorem exists_logical_of_exact_distance
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (h : hasLogicalFault DC baseOutcomes logicalEffect) :
    ∃ F : SpacetimeFault V E M,
      IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F ∧
      F.weight times = spacetimeFaultDistance DC baseOutcomes logicalEffect times :=
  spacetimeFaultDistance_is_min DC baseOutcomes logicalEffect times h

/-! ## Section 8: Fault Tolerance Threshold

A code can tolerate faults of weight t if t < d_ST.
This section establishes the relationship between fault tolerance and d_ST. -/

/-- A code can tolerate weight-t faults if t < d_ST -/
def canTolerateFaults
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (t : ℕ) : Prop :=
  t < spacetimeFaultDistance DC baseOutcomes logicalEffect times

/-- If the code can tolerate weight t, any fault of weight ≤ t is correctable or stabilizer -/
theorem tolerable_implies_correctable
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (t : ℕ)
    (htol : canTolerateFaults DC baseOutcomes logicalEffect times t)
    (F : SpacetimeFault V E M) (hF : F.weight times ≤ t) :
    ¬hasEmptySyndrome DC baseOutcomes F ∨
    ¬affectsLogicalInfo logicalEffect F := by
  have hlt : F.weight times < spacetimeFaultDistance DC baseOutcomes logicalEffect times := by
    unfold canTolerateFaults at htol
    omega
  exact detectable_or_stabilizer_if_weight_lt DC baseOutcomes logicalEffect times F hlt

/-- The maximum tolerable fault weight is d_ST - 1 (when d_ST > 0) -/
theorem max_tolerable_weight
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (hpos : 0 < spacetimeFaultDistance DC baseOutcomes logicalEffect times) :
    canTolerateFaults DC baseOutcomes logicalEffect times
      (spacetimeFaultDistance DC baseOutcomes logicalEffect times - 1) := by
  unfold canTolerateFaults
  omega

/-! ## Section 9: Intuitive Interpretation

The spacetime fault-distance d_ST is the minimum number of independent faults required
to cause a logical error without being detected. -/

/-- If d_ST > 0, weight-0 undetectable faults must be stabilizers -/
theorem distance_pos_means_nontrivial
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (hpos : 0 < spacetimeFaultDistance DC baseOutcomes logicalEffect times) :
    ∀ F : SpacetimeFault V E M,
      F.weight times = 0 → hasEmptySyndrome DC baseOutcomes F →
      ¬affectsLogicalInfo logicalEffect F := by
  intro F hw hund
  by_contra hnottriv
  have hlog : IsSpacetimeLogicalFault DC baseOutcomes logicalEffect F := ⟨hund, hnottriv⟩
  have hge := spacetimeFaultDistance_le_weight DC baseOutcomes logicalEffect times F hlog
  omega

/-- The identity fault has weight 0 and empty syndrome, so it's a stabilizer -/
theorem identity_not_logical
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (h_logical : LogicalEffectIsGroupLike logicalEffect)
    (_h_base : DC.allSatisfied baseOutcomes) :
    ¬IsSpacetimeLogicalFault DC baseOutcomes logicalEffect (1 : SpacetimeFault V E M) := by
  intro hlog
  have hpres := h_logical.identity_preserves
  exact hpres hlog.affectsLogical

/-! ## Section 10: Distance as Infimum Characterization

Alternative characterization of spacetime fault distance using infimum. -/

/-- The spacetime fault distance satisfies the infimum property:
    it's the greatest lower bound of logical fault weights -/
theorem spacetimeFaultDistance_is_glb
    [Fintype V] [Fintype E] [Fintype M]
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (logicalEffect : SpacetimeFault V E M → Prop)
    (times : Finset TimeStep)
    (h : hasLogicalFault DC baseOutcomes logicalEffect) :
    IsGLB (logicalFaultWeights DC baseOutcomes logicalEffect times)
          (spacetimeFaultDistance DC baseOutcomes logicalEffect times) := by
  constructor
  · -- d_ST is a lower bound
    intro w hw
    exact logicalFaultWeights_bounded_below DC baseOutcomes logicalEffect times w hw
  · -- d_ST is the greatest lower bound
    intro n hn
    obtain ⟨F, hF, heq⟩ := spacetimeFaultDistance_is_min DC baseOutcomes logicalEffect times h
    have hmem : F.weight times ∈ logicalFaultWeights DC baseOutcomes logicalEffect times :=
      ⟨F, hF, rfl⟩
    have hle := hn hmem
    rw [← heq]
    exact hle

/-! ## Summary

This formalization captures the spacetime fault-distance from fault-tolerant quantum
error correction:

1. **Logical Fault Weights**: The set W = {|F| : F is a spacetime logical fault} where
   weight counts single-qubit Pauli errors + measurement errors + initialization errors.

2. **Spacetime Fault Distance**: d_ST = min(W), the minimum weight of any logical fault.
   If no logical faults exist, d_ST = 0 as a sentinel value.

3. **Fault Tolerance**: Faults with weight < d_ST cannot be logical faults. They are either:
   - Detectable (non-empty syndrome), or
   - Stabilizers (don't affect logical information)

4. **Intuition**: d_ST is the minimum number of independent faults required to cause a
   logical error without being detected.

Key properties proven:
- d_ST ≤ weight of any logical fault (it's a lower bound)
- The minimum is achieved when logical faults exist
- Faults with weight < d_ST cannot be logical faults
- d_ST > 0 iff logical faults exist and all have positive weight
- d_ST is the greatest lower bound (infimum) of logical fault weights
-/
