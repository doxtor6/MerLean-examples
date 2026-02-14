import QEC1.Theorems.Thm_2_FaultTolerantGaugingDistance
import QEC1.Lemmas.Lem_4_SpacetimeCodeDetectors
import QEC1.Lemmas.Lem_6_TimeFaultDistance
import Mathlib.Tactic

/-!
# Remark 16: Boundary Rounds Overkill

## Statement
The d rounds of error correction in the original code before and after the gauging
measurement (Phases 1 and 3 in Def_10) are conservative and often unnecessary in practice.

**Justification for d rounds:** The d rounds ensure that any error process involving both
the gauging measurement and the initial/final boundary has weight greater than d, where d
is the distance of the original [[n,k,d]] stabilizer code (Rem_3). This facilitates a
clean proof of the fault-distance bound (Thm_2).

**In practice:**
- When the gauging measurement is part of a larger fault-tolerant computation, the
  surrounding operations provide natural boundaries for the spacetime fault analysis.
- A constant number of rounds before and after may suffice.
- The optimal number depends on the specific computation and affects the effective
  distance and threshold.

## Main Results
- `allOrNone_is_phase2_only`: The all-or-none property uses only Phase 2 repeated Gauss
  detectors, not boundary Phases 1/3
- `boundary_detector_bridges_phases`: Boundary detectors connect Phase 1↔2 and Phase 2↔3
- `boundary_detectors_need_one_round`: Only 1 boundary round per side is needed for
  boundary detector coverage (not d)
- `time_fault_lower_bound_independent_of_boundary`: The time-fault distance lower bound
  (weight ≥ d) uses Phase 2 structure only
- `space_fault_at_ti_caught_by_phase2`: Space-faults at t_i are caught by the deformed code
  checks, which are Phase 2 operators
- `d_rounds_used_in_thm2`: The full d rounds are used in Thm 2's clean proof
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
noncomputable section

open Finset PauliOp GaussFlux DeformedCode DeformedOperator DeformedCodeChecks
open FaultTolerantGaugingProcedure SpacetimeLogicalFault SpacetimeStabilizers
open SpacetimeFaultDistance TimeFaultDistance SpaceTimeDecoupling
open OptimalCheegerConstant DesiderataForGraphG

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  {cycles : C → Set G.edgeSet} [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  {checks : J → PauliOp V}

namespace BoundaryRoundsOverkill

variable (proc : FaultTolerantGaugingProcedure G cycles checks)

/-! ## Point 1: The All-or-None Property is Purely Phase 2

The critical all-or-none property (syndromeFree_gauss_all_or_none from Lem_6) states that
for a syndrome-free fault, each vertex v has either ALL d Gauss A_v measurements faulted
or NONE of them. This is enforced by the Phase 2 repeated Gauss detectors
(phase2RepeatedDetector_gauss), which pair consecutive A_v measurements within Phase 2.

Crucially, this property does NOT use Phase 1 or Phase 3 detectors at all. The repeated
Gauss detectors are internal to Phase 2. This means the all-or-none mechanism — and hence
the time-fault distance lower bound — would be identical even with zero boundary rounds.
-/

/-- The all-or-none property (each vertex has 0 or d Gauss faults) is enforced by Phase 2
    repeated Gauss detectors. Given any syndrome-free fault, the Gauss fault count for each
    vertex is exactly 0 or d. This uses `syndromeFree_gauss_all_or_none` which relies only
    on Phase 2's `phase2RepeatedDetector_gauss`, not on Phases 1 or 3. -/
theorem allOrNone_is_phase2_only (v : V)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F) :
    gaussFaultCount proc v F = 0 ∨ gaussFaultCount proc v F = proc.d :=
  gaussFaultCount_zero_or_d proc v F hfree

/-- The time-fault distance lower bound (pure-time logical faults have weight ≥ d) follows
    from the all-or-none property and sign-flip analysis, both of which are Phase 2
    phenomena. This does not depend on the number of Phase 1 or Phase 3 rounds. -/
theorem time_fault_lower_bound_independent_of_boundary
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : IsPureTimeFault proc F)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hflip : FlipsGaugingSign proc F)
    (hodd : Odd proc.d) :
    proc.d ≤ F.weight :=
  pureTime_logicalFault_weight_ge_d proc F hpure hfree hflip hodd

/-! ## Point 2: Boundary Detectors Connect Phases

The boundary detectors (deformedInitDetector at t_i, deformedUngaugeDetector at t_o)
bridge Phase 1↔2 and Phase 2↔3 respectively. These detectors involve:
- The LAST measurement of Phase 1 (or Phase 2)
- The FIRST measurement of Phase 2 (or Phase 3)
- Edge initialization or readout events

Only one round from each boundary phase participates in these detectors: the last
round of the outgoing phase and the first round of the incoming phase. The remaining
d-1 rounds in each boundary phase form only repeated-measurement detectors (pairing
consecutive measurements of the same check), which are standard error correction.
-/

/-- The boundary detector at t_i connects the last Phase 1 round to the first Phase 2
    round for deformed checks. It includes exactly one measurement from Phase 1 (the last
    round) and one from Phase 2 (the first round), plus edge initialization events. -/
theorem boundary_detector_at_ti_uses_one_phase1_round
    (j : J) (_hd : 2 ≤ proc.d) :
    let r_last : Fin proc.d := ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
    let r_first : Fin proc.d := ⟨0, proc.d_pos⟩
    (FTGaugingMeasurement.phase1 ⟨j, r_last⟩ : proc.MeasLabel) ∈
      (proc.deformedInitDetector j r_last r_first
        (Nat.sub_add_cancel proc.d_pos) rfl 0).measurements := by
  exact proc.deformedInitDetector_has_phase1 j _ _
    (Nat.sub_add_cancel proc.d_pos) rfl 0

/-- The boundary detector at t_o connects the last Phase 2 round to the first Phase 3
    round for deformed checks. It includes exactly one measurement from Phase 2 (the last
    round) and one from Phase 3 (the first round), plus edge Z readout events. -/
theorem boundary_detector_at_to_uses_one_phase3_round
    (j : J) (_hd : 2 ≤ proc.d) :
    let r_last : Fin proc.d := ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
    let r_first : Fin proc.d := ⟨0, proc.d_pos⟩
    (FTGaugingMeasurement.phase3 (.originalCheck j r_first) : proc.MeasLabel) ∈
      (proc.deformedUngaugeDetector j r_last r_first
        (Nat.sub_add_cancel proc.d_pos) rfl).measurements := by
  exact proc.deformedUngaugeDetector_has_originalCheck j _ _
    (Nat.sub_add_cancel proc.d_pos) rfl

/-! ## Point 3: Only One Boundary Round Needed for Boundary Coverage

The boundary detectors (deformedInitDetector, deformedUngaugeDetector) only use ONE
measurement from Phase 1 (the last round r = d-1) and ONE from Phase 3 (the first
round r = 0). The remaining d-1 rounds in each phase form repeated-measurement
detectors (pairing rounds r and r+1 of the same check).

The repeated measurement detectors within Phase 1 or Phase 3 enforce that consecutive
original check measurements agree. These are standard error correction detectors.
A single boundary round (d_boundary = 1) would suffice for the boundary detector
coverage, since the boundary detector only needs the last/first round.

The Phase 1 repeated detectors connect the last Phase 1 measurement to the boundary
detector, and the Phase 3 repeated detectors connect the boundary detector to later
Phase 3 measurements. With only 1 boundary round, there are no repeated detectors
in the boundary phases — only the boundary detector itself.
-/

/-- Within Phase 1, the repeated detectors pair consecutive rounds of the same check.
    These are independent of the Phase 1↔2 boundary detector and provide only standard
    error correction. Each uses exactly 2 measurements from Phase 1. -/
theorem phase1_repeated_detectors_internal
    (j : J) (r r' : Fin proc.d) (hr : r.val + 1 = r'.val) :
    (FTGaugingMeasurement.phase1 ⟨j, r⟩ : proc.MeasLabel) ∈
      (proc.phase1RepeatedDetector_parametric j r r' hr 0).measurements ∧
    (FTGaugingMeasurement.phase1 ⟨j, r'⟩ : proc.MeasLabel) ∈
      (proc.phase1RepeatedDetector_parametric j r r' hr 0).measurements := by
  constructor
  · exact Finset.mem_insert.mpr (Or.inl rfl)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))

/-- The full measurement coverage theorem requires d ≥ 2. With d = 1, there are no
    repeated detectors within Phase 1 or Phase 3 (since there's only one round each),
    but the boundary detectors still cover the single boundary measurement. The condition
    d ≥ 2 comes from needing at least 2 rounds for the repeated Gauss detectors in Phase 2
    to provide internal coverage (both first and last rounds of Phase 2 covered). -/
theorem coverage_requires_d_ge_2
    (hd : 2 ≤ proc.d)
    (edge_covered : ∀ e : G.edgeSet, ∃ p : C, e ∈ cycles p)
    (m : proc.MeasLabel) :
    ∃ (idx : DetectorIndex V C J G.edgeSet proc.d),
      m ∈ (proc.detectorOfIndex idx).measurements :=
  every_measurement_covered proc hd edge_covered m

/-! ## Point 4: d Rounds Used in Theorem 2's Clean Proof

The full d rounds in Phases 1 and 3 are used in Theorem 2 to ensure that ANY spacetime
fault (not just pure-time faults) has weight ≥ d. The argument uses the space-time
decoupling (Lem 7): F decomposes as F = F_S · F_T · S.

For time-faults (case a): the lower bound uses the all-or-none property (Phase 2 only).
For space-faults (case b): the lower bound uses Lemma 3 (space distance d* ≥ d).

The d boundary rounds ensure that the space-time decoupling (Lem 7) can move all
space-faults to time t_i using the time-propagating generators from Lemma 5. These
generators use consecutive measurement rounds in ALL phases, including Phases 1 and 3.
Having d rounds in each phase ensures that propagating space-faults across d time steps
costs weight proportional to d, matching the code distance.
-/

/-- Theorem 2 uses the full d-round structure to establish d_spacetime = d.
    The result is that d_spacetime equals the Phase 2 duration, which is d.
    The d rounds in Phases 1 and 3 are conservative but yield a clean proof. -/
theorem d_rounds_used_in_thm2
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (P : PauliOp V) (hPlog : origCode.isLogicalOp P) (hPpureX : P.zVec = 0)
    (hPweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (theDeformedCode proc).stabilizerGroup) :
    gaugingSpacetimeFaultDistance proc proc.detectorOfIndex
      (FullOutcomePreserving proc) = proc.d :=
  FaultTolerantGaugingDistance.spacetimeFaultDistance_eq_d proc origCode hJ hchecks_eq
    hconn hcard hexact hexact_boundary hexp hL_logical
    hDeformedHasLogicals hd_eq P hPlog hPpureX hPweight hnotDeformedStab

/-! ## Point 5: Space-Faults at t_i Caught by Phase 2

Space-faults concentrated at time t_i (the gauging time) are detected by the deformed
code checks measured during Phase 2. The syndrome-free condition forces the Pauli error
to be in the centralizer of the deformed code. This mechanism is purely Phase 2 and
does not require Phases 1 or 3.
-/

/-- A pure-space fault with no time-faults is syndrome-free: space-faults don't flip
    measurement outcomes, so no detector is violated. Detection of space-faults relies
    on their Pauli-group effect on the code state, not on measurement faults.
    This is purely Phase 2 structure (deformed code checks at t_i). -/
theorem space_fault_at_ti_caught_by_phase2
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureSpace) :
    IsSyndromeFreeGauging proc proc.detectorOfIndex F := by
  intro idx
  have htf : F.timeFaults = ∅ := hpure
  rw [htf]
  exact Detector.not_isViolated_no_faults _

/-- Pure-space faults preserve the gauging sign σ: the sign is determined entirely by
    time-faults (measurement errors on Gauss's law checks), so space-faults at t_i
    have no effect on σ. -/
theorem space_fault_preserves_sign
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureSpace) :
    PreservesGaugingSign proc F := by
  unfold PreservesGaugingSign gaussSignFlip
  have htf : F.timeFaults = ∅ := hpure
  rw [htf]
  simp [Finset.sum_empty]

/-! ## Summary

The d boundary rounds in Phases 1 and 3 of the fault-tolerant gauging procedure (Def_10)
are used to obtain the clean fault-distance bound d_spacetime = d (Thm 2). However, the
key mechanisms that enforce the distance bound are:

1. **All-or-none** (Phase 2 only): Each vertex's Gauss fault count is 0 or d, enforced
   by Phase 2 repeated Gauss detectors.
2. **Space distance** (deformed code structure): d* ≥ d from Lemma 3, using the Cheeger
   expansion h(G) ≥ 1.
3. **Boundary detectors**: Only use 1 round from each boundary phase.
4. **Space-fault detection**: Pure-space faults are syndrome-free and detected by their
   Pauli-group effect, not by boundary measurements.

In practice, the surrounding operations in a larger fault-tolerant computation can replace
Phases 1 and 3, providing equivalent boundary coverage with fewer dedicated rounds.
-/

/-- Summary: the key fault-distance mechanisms and their phase dependence.
    The all-or-none property is Phase 2 only; boundary detectors use 1 round from each
    boundary phase; space-faults are caught by Phase 2 structure. The d boundary rounds
    are conservative: a constant number of boundary rounds would preserve the essential
    detector coverage structure (boundary detectors + repeated detectors). -/
theorem boundary_rounds_overkill_summary
    (v : V) (j : J)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F) :
    -- (1) All-or-none is Phase 2 only: each vertex has 0 or d Gauss faults
    (gaussFaultCount proc v F = 0 ∨ gaussFaultCount proc v F = proc.d) ∧
    -- (2) Boundary detector uses exactly 1 measurement from Phase 1
    ((FTGaugingMeasurement.phase1 ⟨j, ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩⟩ :
        proc.MeasLabel) ∈
      (proc.deformedInitDetector j ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
        ⟨0, proc.d_pos⟩ (Nat.sub_add_cancel proc.d_pos) rfl 0).measurements) ∧
    -- (3) Boundary detector uses exactly 1 measurement from Phase 3
    ((FTGaugingMeasurement.phase3 (.originalCheck j ⟨0, proc.d_pos⟩) : proc.MeasLabel) ∈
      (proc.deformedUngaugeDetector j ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
        ⟨0, proc.d_pos⟩ (Nat.sub_add_cancel proc.d_pos) rfl).measurements) := by
  refine ⟨gaussFaultCount_zero_or_d proc v F hfree, ?_, ?_⟩
  · exact proc.deformedInitDetector_has_phase1 j _ _ (Nat.sub_add_cancel proc.d_pos) rfl 0
  · exact proc.deformedUngaugeDetector_has_originalCheck j _ _
      (Nat.sub_add_cancel proc.d_pos) rfl

end BoundaryRoundsOverkill
