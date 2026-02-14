import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_10_FaultTolerantGaugingProcedure
import QEC1.Definitions.Def_11_SpacetimeLogicalFault
import QEC1.Lemmas.Lem_4_SpacetimeCodeDetectors
import Mathlib.Tactic

/-!
# Definition 12: Spacetime Fault-Distance

## Statement
The **spacetime fault-distance** of the fault-tolerant gauging measurement procedure (Def 10)
is the minimum weight of a spacetime logical fault (Def 11).

The weight |F| of a spacetime fault F is the total number of elementary fault events:
- Each single-qubit Pauli error (space-fault) counts as weight 1
- Each measurement error (time-fault) counts as weight 1
- Each initialization error (time-fault) counts as weight 1

Formally:
  d_spacetime = min { |F| : F is a spacetime logical fault }

Returns 0 if no spacetime logical faults exist.

## Main Results
- `spacetimeFaultDistance`: The spacetime fault-distance d_spacetime
- `spacetimeFaultDistance_le_of_logicalFault`: d_spacetime ≤ |F| for any logical fault F
- `spacetimeFaultDistance_pos`: d_spacetime > 0 when logical faults exist and empty is a stabilizer

## Corollaries
- `spacetimeFaultDistance_eq_zero_of_no_logicalFaults`: d_spacetime = 0 if no logical faults
- `not_logicalFault_of_weight_lt`: Fault of weight < d_spacetime cannot be logical
- `syndromeFree_weight_lt_is_stabilizer`: Syndrome-free fault of weight < d_spacetime is stabilizer
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset PauliOp GaussFlux DeformedCode DeformedOperator SpacetimeLogicalFault
  FaultTolerantGaugingProcedure

namespace SpacetimeFaultDistance

/-! ## Generic Spacetime Fault-Distance

Defined for an arbitrary collection of detectors and an outcome-preserving predicate.
This follows the same `sInf` pattern as `StabilizerCode.distance` (Rem_3). -/

variable {Q T : Type*}
  {I : Type*} [Fintype I] [DecidableEq I]
  {M : Type*} [DecidableEq M] [DecidableEq (TimeFault M)]

/-- The set of weights of spacetime logical faults. -/
def logicalFaultWeights
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop) : Set ℕ :=
  { w : ℕ | ∃ F : SpacetimeFault Q T M,
    IsSpacetimeLogicalFault detectors outcomePreserving F ∧ F.weight = w }

/-- The **spacetime fault-distance**: minimum weight of a spacetime logical fault.
    Returns 0 if no spacetime logical faults exist. -/
noncomputable def spacetimeFaultDistance
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop) : ℕ :=
  sInf (logicalFaultWeights detectors outcomePreserving)

/-! ## Basic Properties -/

/-- d_spacetime ≤ |F| for any spacetime logical fault F. -/
theorem spacetimeFaultDistance_le_of_logicalFault
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (hlog : IsSpacetimeLogicalFault detectors outcomePreserving F) :
    spacetimeFaultDistance detectors outcomePreserving ≤ F.weight := by
  apply Nat.sInf_le
  exact ⟨F, hlog, rfl⟩

/-- If no spacetime logical faults exist, d_spacetime = 0. -/
theorem spacetimeFaultDistance_eq_zero_of_no_logicalFaults
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (hno : ∀ F : SpacetimeFault Q T M,
      ¬IsSpacetimeLogicalFault detectors outcomePreserving F) :
    spacetimeFaultDistance detectors outcomePreserving = 0 := by
  have hempty : logicalFaultWeights detectors outcomePreserving = ∅ := by
    ext w
    simp only [logicalFaultWeights, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨F, hlog, _⟩
    exact absurd hlog (hno F)
  unfold spacetimeFaultDistance
  rw [hempty]
  exact Nat.sInf_empty

/-- d_spacetime > 0 when logical faults exist and the empty fault is outcome-preserving. -/
theorem spacetimeFaultDistance_pos
    [DecidableEq Q] [DecidableEq T] [DecidableEq (SpaceFault Q T)]
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    (hempty : outcomePreserving SpacetimeFault.empty)
    (hexists : ∃ F : SpacetimeFault Q T M,
      IsSpacetimeLogicalFault detectors outcomePreserving F) :
    0 < spacetimeFaultDistance detectors outcomePreserving := by
  have hzero : (0 : ℕ) ∉ logicalFaultWeights detectors outcomePreserving := by
    intro ⟨F, hlog, hw⟩
    have := IsSpacetimeLogicalFault.weight_pos hlog hempty
    omega
  obtain ⟨F, hlog⟩ := hexists
  have hne : (logicalFaultWeights detectors outcomePreserving).Nonempty :=
    ⟨F.weight, F, hlog, rfl⟩
  rw [Nat.pos_iff_ne_zero]
  intro h
  unfold spacetimeFaultDistance at h
  rw [Nat.sInf_eq_zero] at h
  rcases h with h0 | hempt
  · exact hzero h0
  · exact hne.ne_empty hempt

/-! ## Characterization Lemmas -/

/-- A fault of weight < d_spacetime cannot be a logical fault. -/
theorem not_logicalFault_of_weight_lt
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (hw : F.weight < spacetimeFaultDistance detectors outcomePreserving) :
    ¬IsSpacetimeLogicalFault detectors outcomePreserving F := by
  intro hlog
  have hle := spacetimeFaultDistance_le_of_logicalFault hlog
  omega

/-- Any syndrome-free fault of weight < d_spacetime is a spacetime stabilizer. -/
theorem syndromeFree_weight_lt_is_stabilizer
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (hfree : IsSyndromeFree detectors F)
    (hw : F.weight < spacetimeFaultDistance detectors outcomePreserving) :
    IsSpacetimeStabilizer detectors outcomePreserving F := by
  have hnotlog := not_logicalFault_of_weight_lt hw
  exact (syndromeFree_stabilizer_iff_not_logicalFault detectors outcomePreserving F hfree).mpr
    hnotlog

/-- d_spacetime ≤ spaceWeight + timeWeight for any logical fault. -/
theorem spacetimeFaultDistance_le_space_plus_time
    [DecidableEq Q] [DecidableEq T] [DecidableEq (SpaceFault Q T)]
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (hlog : IsSpacetimeLogicalFault detectors outcomePreserving F) :
    spacetimeFaultDistance detectors outcomePreserving ≤
    F.spaceWeight + F.timeWeight := by
  have h := spacetimeFaultDistance_le_of_logicalFault hlog
  simp only [SpacetimeFault.weight, SpacetimeFault.spaceWeight, SpacetimeFault.timeWeight]
  simp only [SpacetimeFault.weight] at h
  exact h

/-! ## Instantiation for the Gauging Procedure

The spacetime fault-distance of the fault-tolerant gauging procedure (Def 10)
uses the gauging-specific logical fault definition (IsGaugingLogicalFault from Def 11)
and the detectors from Lemma 4. -/

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  {cycles : C → Set G.edgeSet} [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  {checks : J → PauliOp V}

variable (proc : FaultTolerantGaugingProcedure G cycles checks)

/-- The set of weights of gauging logical faults. -/
def gaugingLogicalFaultWeights
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop) : Set ℕ :=
  { w : ℕ | ∃ F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel,
    IsGaugingLogicalFault proc detectors outcomePreserving F ∧ F.weight = w }

/-- The **spacetime fault-distance of the gauging procedure**:
    minimum weight of a gauging logical fault. -/
noncomputable def gaugingSpacetimeFaultDistance
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop) : ℕ :=
  sInf (gaugingLogicalFaultWeights proc detectors outcomePreserving)

/-- d_spacetime ≤ |F| for any gauging logical fault F. -/
theorem gaugingSpacetimeFaultDistance_le
    {detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel}
    {outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop}
    {F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel}
    (hlog : IsGaugingLogicalFault proc detectors outcomePreserving F) :
    gaugingSpacetimeFaultDistance proc detectors outcomePreserving ≤ F.weight := by
  apply Nat.sInf_le
  exact ⟨F, hlog, rfl⟩

/-- If no gauging logical faults exist, d_spacetime = 0. -/
theorem gaugingSpacetimeFaultDistance_eq_zero_of_no_faults
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (hno : ∀ F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel,
      ¬IsGaugingLogicalFault proc detectors outcomePreserving F) :
    gaugingSpacetimeFaultDistance proc detectors outcomePreserving = 0 := by
  have hempty : gaugingLogicalFaultWeights proc detectors outcomePreserving = ∅ := by
    ext w
    simp only [gaugingLogicalFaultWeights, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨F, hlog, _⟩
    exact absurd hlog (hno F)
  unfold gaugingSpacetimeFaultDistance
  rw [hempty]
  exact Nat.sInf_empty

/-- d_spacetime > 0 when gauging logical faults exist and empty is outcome-preserving. -/
theorem gaugingSpacetimeFaultDistance_pos
    {detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel}
    {outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop}
    (hempty : outcomePreserving SpacetimeFault.empty)
    (hexists : ∃ F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel,
      IsGaugingLogicalFault proc detectors outcomePreserving F) :
    0 < gaugingSpacetimeFaultDistance proc detectors outcomePreserving := by
  have hzero : (0 : ℕ) ∉ gaugingLogicalFaultWeights proc detectors outcomePreserving := by
    intro ⟨F, hlog, hw⟩
    -- weight = 0 means both finsets empty, so F = empty, contradicting outcome change
    unfold SpacetimeFault.weight at hw
    have hs : F.spaceFaults = ∅ := Finset.card_eq_zero.mp (by omega)
    have ht : F.timeFaults = ∅ := Finset.card_eq_zero.mp (by omega)
    have heq : F = SpacetimeFault.empty := by
      cases F; simp_all [SpacetimeFault.empty]
    rw [heq] at hlog
    exact hlog.2 hempty
  obtain ⟨F, hlog⟩ := hexists
  have hne : (gaugingLogicalFaultWeights proc detectors outcomePreserving).Nonempty :=
    ⟨F.weight, F, hlog, rfl⟩
  rw [Nat.pos_iff_ne_zero]
  intro h
  unfold gaugingSpacetimeFaultDistance at h
  rw [Nat.sInf_eq_zero] at h
  rcases h with h0 | hempt
  · exact hzero h0
  · exact hne.ne_empty hempt

/-- Any gauging fault of weight < d_spacetime cannot be a gauging logical fault. -/
theorem not_gaugingLogicalFault_of_weight_lt
    {detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel}
    {outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop}
    {F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel}
    (hw : F.weight < gaugingSpacetimeFaultDistance proc detectors outcomePreserving) :
    ¬IsGaugingLogicalFault proc detectors outcomePreserving F := by
  intro hlog
  have hle := gaugingSpacetimeFaultDistance_le proc hlog
  omega

/-- Any syndrome-free gauging fault of weight < d_spacetime is a gauging stabilizer. -/
theorem syndromeFree_gauging_weight_lt_is_stabilizer
    {detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel}
    {outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop}
    {F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel}
    (hfree : IsSyndromeFreeGauging proc detectors F)
    (hw : F.weight < gaugingSpacetimeFaultDistance proc detectors outcomePreserving) :
    IsGaugingStabilizer proc detectors outcomePreserving F := by
  have hnotlog := not_gaugingLogicalFault_of_weight_lt proc hw
  exact ⟨hfree, by_contra fun hnp => hnotlog ⟨hfree, hnp⟩⟩

/-- d_spacetime ≤ |F| for any specific gauging logical fault (explicit weight bound). -/
theorem gaugingSpacetimeFaultDistance_le_weight
    {detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel}
    {outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop}
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hlog : IsGaugingLogicalFault proc detectors outcomePreserving F) :
    gaugingSpacetimeFaultDistance proc detectors outcomePreserving ≤ F.weight :=
  gaugingSpacetimeFaultDistance_le proc hlog

/-- d_spacetime ≤ spaceWeight + timeWeight for any gauging logical fault. -/
theorem gaugingSpacetimeFaultDistance_le_space_plus_time
    {detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel}
    {outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop}
    {F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel}
    (hlog : IsGaugingLogicalFault proc detectors outcomePreserving F) :
    gaugingSpacetimeFaultDistance proc detectors outcomePreserving ≤
    F.spaceWeight + F.timeWeight := by
  have h := gaugingSpacetimeFaultDistance_le proc hlog
  simp only [SpacetimeFault.weight, SpacetimeFault.spaceWeight, SpacetimeFault.timeWeight]
  simp only [SpacetimeFault.weight] at h
  exact h

end SpacetimeFaultDistance
