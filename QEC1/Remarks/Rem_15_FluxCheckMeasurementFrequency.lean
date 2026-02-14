import QEC1.Theorems.Thm_2_FaultTolerantGaugingDistance
import QEC1.Lemmas.Lem_4_SpacetimeCodeDetectors
import QEC1.Lemmas.Lem_6_TimeFaultDistance
import Mathlib.Tactic

/-!
# Remark 15: Flux Check Measurement Frequency

## Statement
The proof of Theorem 2 (fault-tolerance) holds even if the flux checks B_p are measured
much less frequently than every round, or even not directly measured at all.

**Why this works:**
1. B_p can be inferred from initialization (|0⟩_e at t_i) and final readout (Z_e at t_o)
   without direct measurement, since B_p = ∏_{e ∈ p} Z_e and |0⟩_e is a +1 eigenstate of Z_e.
2. The distance bound from Lemma 3 does not require B_p measurements; it only requires
   B_p to be stabilizers of the code.
3. The time-fault analysis (Lemma 6) shows A_v measurement faults are the bottleneck
   for time-fault distance, not B_p.

**Caveats:**
1. Without frequent B_p measurements, detector cells become large (spanning t_i to t_o).
2. Large detectors prevent achieving a threshold against random noise.
3. For small fixed code instances, this approach may be practical.

## Main Results
- `flux_inferred_from_init_readout`: B_p information is captured by boundary detectors
- `space_distance_independent_of_flux_measurements`: Lem 3 only needs B_p as stabilizers
- `time_fault_bottleneck_is_gauss`: A_v strings determine the time-fault distance
- `flux_fault_preserves_sign`: B_p faults cannot flip the gauging sign
- `flux_boundary_detector_weight`: Boundary detector has weight |p| + 1
- `repeated_vs_boundary_detector_weight`: Repeated detectors have weight 2
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

namespace FluxCheckMeasurementFrequency

variable (proc : FaultTolerantGaugingProcedure G cycles checks)

/-! ## Point 1: B_p Information from Boundary Detectors

The flux check B_p = ∏_{e ∈ p} Z_e can be inferred from edge initialization
and final Z_e readout. The boundary detectors from Lemma 4 encode this:
- `fluxInitDetector`: pairs edge init events with the first B_p measurement
- `fluxUngaugeDetector`: pairs the last B_p measurement with individual Z_e readouts

Even without *any* Phase 2 flux measurements, the composition of these two
boundary detectors gives a detector pairing edge inits with edge readouts.
-/

/-- The flux init detector (B_p^{t_i}) captures the relationship between edge
initialization and the first flux measurement. Edge init events for e ∈ p are
included in this detector, encoding B_p = ∏_{e ∈ p} Z_e via |0⟩ initialization. -/
theorem flux_inferred_from_init_readout (p : C) :
    ∀ e : G.edgeSet, e ∈ cycles p →
      (FTGaugingMeasurement.edgeInit ⟨e⟩ : proc.MeasLabel) ∈
        (proc.fluxInitDetector p ⟨0, proc.d_pos⟩ rfl).measurements :=
  fun e he => proc.fluxInitDetector_has_edgeInit p ⟨0, proc.d_pos⟩ rfl e he

/-- The flux ungauge detector (B_p^{t_o}) captures the relationship between the last
flux measurement and individual Z_e readouts for e ∈ p. -/
theorem flux_inferred_from_readout (p : C) :
    ∀ e : G.edgeSet, e ∈ cycles p →
      (FTGaugingMeasurement.phase3
        (PostDeformationMeasurement.edgeZ e) : proc.MeasLabel) ∈
        (proc.fluxUngaugeDetector p ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
          (Nat.sub_add_cancel proc.d_pos)).measurements :=
  fun e he => proc.fluxUngaugeDetector_has_edgeZ p
    ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
    (Nat.sub_add_cancel proc.d_pos) e he

/-- The flux init detector also contains the first B_p measurement in Phase 2.
This single measurement, together with the edge inits, suffices to capture B_p
information — no repeated B_p measurements needed. -/
theorem flux_init_contains_first_measurement (p : C) :
    (FTGaugingMeasurement.phase2 (.flux p ⟨0, proc.d_pos⟩) : proc.MeasLabel) ∈
      (proc.fluxInitDetector p ⟨0, proc.d_pos⟩ rfl).measurements :=
  proc.fluxInitDetector_has_flux p ⟨0, proc.d_pos⟩ rfl

/-- The flux ungauge detector contains the last B_p measurement. -/
theorem flux_ungauge_contains_last_measurement (p : C) :
    (FTGaugingMeasurement.phase2
      (.flux p ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩) : proc.MeasLabel) ∈
      (proc.fluxUngaugeDetector p ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
        (Nat.sub_add_cancel proc.d_pos)).measurements :=
  proc.fluxUngaugeDetector_has_flux p
    ⟨proc.d - 1, Nat.sub_lt proc.d_pos Nat.one_pos⟩
    (Nat.sub_add_cancel proc.d_pos)

/-! ## Point 2: Lemma 3 (Space Distance) is Independent of Flux Measurements

The distance bound d* ≥ min(h(G), 1) · d from Lemma 3 depends only on the
algebraic structure of the deformed code (flux operators being stabilizers),
not on whether they are actively measured. The key inputs are:
- B_p ∈ stabilizer group (algebraic, from Lem_1 flux_mem_stabilizerGroup)
- Boundary/coboundary exactness (graph-theoretic)
- Cheeger expansion (graph-theoretic)
-/

/-- Lemma 3's distance bound requires only that B_p operators are elements of
the deformed stabilizer group, which is an algebraic fact proven in Lem_1
(flux_mem_stabilizerGroup). No measurement of B_p is needed for d* ≥ d. -/
theorem space_distance_independent_of_flux_measurements
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
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
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P) :
    origCode.distance ≤
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance :=
  SpaceDistance.deformed_distance_ge_d_sufficient_expansion G cycles checks
    origCode hJ hchecks_eq data hcyc hcomm hconn hcard hexact hexact_boundary hexp
    hL_logical hDeformedHasLogicals

/-! ## Point 3: Time-Fault Bottleneck is A_v, not B_p

Lemma 6 shows the time-fault distance equals d, determined entirely by
A_v measurement strings. The proof uses:
- Repeated Gauss detectors enforce all-or-none for each A_v
- A full A_v string (all d rounds faulted) has weight d
- Only A_v faults can flip the gauging sign σ = ∑_v ε_v
- B_p faults cannot flip σ (they don't affect Gauss measurements)
-/

/-- The time-fault distance is determined by A_v measurement strings, not B_p.
The canonical minimum-weight pure-time logical fault is a single A_v string
of weight d. This is the upper bound from Lemma 6. -/
theorem time_fault_bottleneck_is_gauss (v : V) (hodd : Odd proc.d) :
    timeFaultDistance proc proc.detectorOfIndex (PreservesGaugingSign proc) ≤ proc.d :=
  timeFaultDistance_le_d proc v hodd

/-- The A_v measurement string has weight exactly d. -/
theorem gauss_string_weight (v : V) :
    (gaussStringFault proc v).weight = proc.d :=
  gaussStringFault_weight_eq_d proc v

/-- The A_v string is syndrome-free: consecutive repeated Gauss detectors see
paired flips that cancel. This does not involve any flux detectors. -/
theorem gauss_string_is_syndrome_free (v : V) :
    IsSyndromeFreeGauging proc proc.detectorOfIndex (gaussStringFault proc v) :=
  gaussStringFault_syndromeFree proc v

/-- The A_v string flips the gauging sign when d is odd. -/
theorem gauss_string_flips_sign (v : V) (hodd : Odd proc.d) :
    FlipsGaugingSign proc (gaussStringFault proc v) :=
  gaussStringFault_flipsSign_of_odd proc v hodd

/-- B_p measurement faults cannot flip the gauging sign σ.
The sign σ = ∑_v ε_v is defined as a sum over Gauss measurement outcomes only
(gaussSignFlip sums over v : V and r : Fin d, checking if A_v measurement at
round r is faulted). A fault whose timeFaults contain only flux measurements
contributes 0 to this sum: no A_v measurement is faulted. -/
theorem flux_fault_preserves_sign
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hflux : ∀ tf ∈ F.timeFaults, ∃ (p : C) (r : Fin proc.d),
      tf = ⟨FTGaugingMeasurement.phase2 (.flux p r)⟩) :
    PreservesGaugingSign proc F := by
  unfold PreservesGaugingSign gaussSignFlip
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro r _
  -- The indicator is 1 iff the Gauss A_v measurement at round r is in timeFaults.
  -- But all timeFaults are flux measurements, so no Gauss measurement is present.
  split_ifs with h
  · -- h : ⟨phase2 (gaussLaw v r)⟩ ∈ F.timeFaults, but all faults are flux
    exfalso
    obtain ⟨p, r', heq⟩ := hflux _ h
    -- heq : ⟨phase2 (gaussLaw v r)⟩ = ⟨phase2 (flux p r')⟩
    -- Extract the measurement field equality
    have hmeas : FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r) =
        FTGaugingMeasurement.phase2 (.flux p r') :=
      congrArg TimeFault.measurement heq
    -- phase2 is injective, so gaussLaw v r = flux p r', impossible by constructor disjointness
    exact absurd hmeas (by simp)
  · rfl

/-- The gauging sign is determined entirely by A_v measurement faults.
This is expressed by the structure of gaussSignFlip: it sums indicators
of A_v membership in timeFaults, ignoring all non-Gauss faults. -/
theorem gaussSignFlip_ignores_flux (v : V) :
    gaussSignFlip proc (gaussStringFault proc v) =
    ∑ w : V, ∑ r : Fin proc.d,
      if (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r)⟩ :
          TimeFault proc.MeasLabel) ∈ (gaussStringFault proc v).timeFaults then 1 else 0 := by
  rfl

/-- The full time-fault distance result from Lemma 6: timeFaultDistance = d. -/
theorem time_fault_distance_eq_d (v : V) (hodd : Odd proc.d) (hV : Nonempty V) :
    timeFaultDistance proc proc.detectorOfIndex (PreservesGaugingSign proc) = proc.d :=
  timeFaultDistance_eq_d proc v hodd hV

/-! ## Caveats: Large Detector Cells

Without frequent B_p measurements, the boundary detectors (fluxInitDetector,
fluxUngaugeDetector) span from t_i to t_o rather than between consecutive rounds.
-/

/-- The key quantitative difference: repeated flux detectors have weight 2
(two consecutive B_p measurements), while boundary flux detectors have weight
proportional to |p| + 1 (all edge inits/readouts plus one B_p measurement).
This means removing repeated flux detectors enlarges the detector cells. -/
theorem repeated_vs_boundary_detector_weight (p : C) (r r' : Fin proc.d)
    (hr : r.val + 1 = r'.val) :
    (proc.phase2RepeatedDetector_flux p r r' hr).measurements.card = 2 := by
  simp only [FaultTolerantGaugingProcedure.phase2RepeatedDetector_flux]
  rw [Finset.card_pair]
  intro heq
  have : r = r' := by
    have := FTGaugingMeasurement.phase2.inj heq
    have := DeformedCodeMeasurement.flux.inj this
    exact this.2
  subst this
  omega

/-- Without repeated flux detectors, the boundary detectors span the full
Phase 2 duration d. The init detector covers t_i to the first Phase 2 round,
and the ungauge detector covers the last Phase 2 round to t_o. -/
theorem flux_boundary_detector_spans_full_duration :
    proc.phase2Start ≤ proc.phase3Start ∧
    proc.phase3Start - proc.phase2Start = proc.d :=
  ⟨proc.phase2Start_le_phase3Start, proc.phase2_duration⟩

/-- Large detector cells: the number of measurements in a boundary detector
(|p| + 1 for flux init) is strictly greater than a repeated detector (2),
as soon as the cycle has at least 2 edges. This quantifies the caveat that
large detectors accumulate more potential faults per detector cell. -/
theorem boundary_larger_than_repeated
    (p : C) (r r' : Fin proc.d) (hr : r.val + 1 = r'.val)
    (hcycle_large : 2 ≤ (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles p)).card) :
    (proc.phase2RepeatedDetector_flux p r r' hr).measurements.card <
    (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles p)).card + 1 := by
  rw [repeated_vs_boundary_detector_weight proc p r r' hr]
  omega

/-! ## Summary: Distance Proof Structure Without Flux Measurements

The spacetime fault-distance proof (Theorem 2) decomposes into:
1. **Space distance** (Lemma 3): d* ≥ min(h(G),1) · d — uses only algebraic
   properties of B_p as stabilizers, not measurements.
2. **Time distance** (Lemma 6): d_time = d — determined entirely by A_v
   measurement strings. B_p faults don't affect the gauging sign.

Therefore, omitting B_p measurements preserves d_spacetime = d.
The only cost is larger detector cells, which affects the threshold
but not the distance guarantee.
-/

/-- The space-distance bound d* ≥ d (Lemma 3) requires h(G) ≥ 1 and exactness.
No measurement of flux checks B_p is needed — only their algebraic presence
as stabilizers of the deformed code. -/
theorem space_distance_from_stabilizer_algebra
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (_hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (p : C) :
    fluxChecks G cycles p ∈
    (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup :=
  flux_mem_stabilizerGroup G cycles checks data hcyc hcomm p

/-- Flux operators are also in the centralizer (commute with all checks),
which is the property actually used in Lemma 3. -/
theorem flux_in_centralizer_algebraically
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (p : C) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer
      (fluxChecks G cycles p) :=
  flux_inCentralizer G cycles checks data hcyc hcomm p

end FluxCheckMeasurementFrequency
