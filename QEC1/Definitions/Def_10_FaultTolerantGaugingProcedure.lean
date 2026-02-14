import QEC1.Definitions.Def_4_DeformedCode
import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_8_Detectors
import QEC1.Definitions.Def_9_Syndrome
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import Mathlib.Tactic

/-!
# Definition 10: Fault-Tolerant Gauging Procedure

## Statement
The fault-tolerant gauging measurement procedure for measuring a logical operator L
in an [[n,k,d]] stabilizer code using a connected graph G = (V, E) consists of three phases:

1. **Phase 1 (Pre-deformation)**: Measure original stabilizer checks for d rounds
2. **Phase 2 (Deformed code)**: Initialize edge qubits, measure Gauss's law, flux, and
   deformed checks for d rounds
3. **Phase 3 (Post-deformation)**: Measure Z_e on edge qubits to ungauge, resume
   original checks for d rounds

## Main Results
- `FaultTolerantGaugingProcedure`: The procedure data with all three phases
- `GaugingPhase`: The three phases as an inductive type
- `phaseOf`: Which phase a given time step belongs to
- `FTGaugingMeasurement`: The type of all measurements across the procedure
- `measurementPhase`, `measurementTime`: Phase/time assignment for measurements
- Phase timing and measurement counting theorems
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ## Phase Type -/

/-- The three phases of the fault-tolerant gauging procedure. -/
inductive GaugingPhase where
  | preDeformation   : GaugingPhase
  | deformedCode     : GaugingPhase
  | postDeformation  : GaugingPhase
  deriving DecidableEq, Repr

namespace GaugingPhase

instance : Fintype GaugingPhase where
  elems := {preDeformation, deformedCode, postDeformation}
  complete := by intro x; cases x <;> simp

theorem card_eq : Fintype.card GaugingPhase = 3 := by decide

end GaugingPhase

/-! ## Measurement Labels -/

/-- Phase 1 measurement: original check j at round r. -/
structure PreDeformationMeasurement (J : Type*) (d : ℕ) where
  checkIdx : J
  round : Fin d
  deriving DecidableEq

instance {J : Type*} [Fintype J] {d : ℕ} : Fintype (PreDeformationMeasurement J d) :=
  Fintype.ofEquiv (J × Fin d)
    ⟨fun ⟨j, r⟩ => ⟨j, r⟩, fun m => ⟨m.checkIdx, m.round⟩,
     fun _ => rfl, fun ⟨_, _⟩ => rfl⟩

/-- Phase 2 measurement: Gauss (V), flux (C), or deformed (J) at round r. -/
inductive DeformedCodeMeasurement (V : Type*) (C : Type*) (J : Type*) (d : ℕ) where
  | gaussLaw (v : V) (round : Fin d)
  | flux (p : C) (round : Fin d)
  | deformed (j : J) (round : Fin d)
  deriving DecidableEq

instance {V C J : Type*} [Fintype V] [Fintype C] [Fintype J] {d : ℕ} :
    Fintype (DeformedCodeMeasurement V C J d) :=
  Fintype.ofEquiv ((V × Fin d) ⊕ (C × Fin d) ⊕ (J × Fin d))
    ⟨fun s => match s with
      | Sum.inl (v, r) => .gaussLaw v r
      | Sum.inr (Sum.inl (p, r)) => .flux p r
      | Sum.inr (Sum.inr (j, r)) => .deformed j r,
     fun m => match m with
      | .gaussLaw v r => Sum.inl (v, r)
      | .flux p r => Sum.inr (Sum.inl (p, r))
      | .deformed j r => Sum.inr (Sum.inr (j, r)),
     fun s => by rcases s with ⟨v, r⟩ | ⟨p, r⟩ | ⟨j, r⟩ <;> rfl,
     fun m => by cases m <;> rfl⟩

/-- Phase 3 measurement: edge Z or original check at round r. -/
inductive PostDeformationMeasurement (J : Type*) (E : Type*) (d : ℕ) where
  | edgeZ (e : E)
  | originalCheck (j : J) (round : Fin d)
  deriving DecidableEq

/-- Edge qubit initialization in |0⟩ (treated as measurement per Def 7). -/
structure EdgeInitialization (E : Type*) where
  edge : E
  deriving DecidableEq

instance {E : Type*} [Fintype E] : Fintype (EdgeInitialization E) :=
  Fintype.ofEquiv E ⟨fun e => ⟨e⟩, fun ei => ei.edge, fun _ => rfl, fun ⟨_⟩ => rfl⟩

/-- All measurement labels across the entire procedure. -/
inductive FTGaugingMeasurement (V : Type*) (C : Type*) (J : Type*) (E : Type*) (d : ℕ) where
  | phase1 (m : PreDeformationMeasurement J d)
  | edgeInit (init : EdgeInitialization E)
  | phase2 (m : DeformedCodeMeasurement V C J d)
  | phase3 (m : PostDeformationMeasurement J E d)
  deriving DecidableEq

/-! ## Time Steps -/

/-- Determine which phase a time step belongs to. -/
def phaseOf (d : ℕ) (t : ℕ) : GaugingPhase :=
  if t < d then GaugingPhase.preDeformation
  else if t < 2 * d then GaugingPhase.deformedCode
  else GaugingPhase.postDeformation

@[simp] theorem phaseOf_preDeformation {d t : ℕ} (ht : t < d) :
    phaseOf d t = GaugingPhase.preDeformation := by
  unfold phaseOf; simp [ht]

@[simp] theorem phaseOf_deformedCode {d t : ℕ} (h1 : d ≤ t) (h2 : t < 2 * d) :
    phaseOf d t = GaugingPhase.deformedCode := by
  simp only [phaseOf, show ¬(t < d) from by omega, ite_false, h2, ite_true]

@[simp] theorem phaseOf_postDeformation {d t : ℕ} (ht : 2 * d ≤ t) :
    phaseOf d t = GaugingPhase.postDeformation := by
  simp only [phaseOf, show ¬(t < d) from by omega, ite_false, show ¬(t < 2 * d) from by omega]

/-! ## Fault-Tolerant Gauging Procedure -/

variable {V : Type*} [Fintype V] [DecidableEq V]

open Finset PauliOp GaussFlux DeformedCode DeformedOperator

/-- The fault-tolerant gauging measurement procedure for measuring a logical
    operator L in an [[n,k,d]] stabilizer code using a connected graph G.
    Bundles: code distance d, original code data, gauging input, deformed code data,
    and cycle parity condition. -/
structure FaultTolerantGaugingProcedure
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {C : Type*} [Fintype C] [DecidableEq C]
    (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
    {J : Type*} [Fintype J] [DecidableEq J]
    (checks : J → PauliOp V) where
  /-- The code distance d: number of rounds per phase -/
  d : ℕ
  /-- d ≥ 1 (meaningful code distance) -/
  d_pos : 0 < d
  /-- The original stabilizer code checks pairwise commute -/
  checks_commute : ∀ i j : J, PauliCommute (checks i) (checks j)
  /-- The gauging input: base vertex and connectivity -/
  gaugingInput : GaugingMeasurement.GaugingInput G
  /-- The deformed code data: edge-paths satisfying boundary conditions -/
  deformedData : DeformedCodeData G checks
  /-- Cycle parity: each vertex incident to even edges in each cycle -/
  cycleParity : ∀ (c : C) (v : V),
    Even (Finset.univ.filter
      (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card

namespace FaultTolerantGaugingProcedure

variable {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  {cycles : C → Set G.edgeSet} [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  {checks : J → PauliOp V}
  (proc : FaultTolerantGaugingProcedure G cycles checks)

/-! ## Phase Timing -/

/-- Phase 2 begins at time d. -/
def phase2Start : ℕ := proc.d

/-- Phase 3 begins at time 2d. -/
def phase3Start : ℕ := 2 * proc.d

/-- The procedure ends at time 3d. -/
def procedureEnd : ℕ := 3 * proc.d

@[simp] theorem phase2Start_eq : proc.phase2Start = proc.d := rfl
@[simp] theorem phase3Start_eq : proc.phase3Start = 2 * proc.d := rfl
@[simp] theorem procedureEnd_eq : proc.procedureEnd = 3 * proc.d := rfl

theorem phase1_duration : proc.phase2Start = proc.d := rfl

theorem phase2_duration : proc.phase3Start - proc.phase2Start = proc.d := by
  unfold phase3Start phase2Start; omega

theorem phase3_duration : proc.procedureEnd - proc.phase3Start = proc.d := by
  unfold procedureEnd phase3Start; omega

theorem total_duration : proc.procedureEnd = 3 * proc.d := rfl

theorem phase2Start_le_phase3Start : proc.phase2Start ≤ proc.phase3Start := by
  unfold phase2Start phase3Start; omega

theorem phase3Start_le_procedureEnd : proc.phase3Start ≤ proc.procedureEnd := by
  unfold phase3Start procedureEnd; omega

/-! ## Measurement Label Type -/

/-- The full measurement label type for this procedure. -/
abbrev MeasLabel := FTGaugingMeasurement V C J G.edgeSet proc.d

/-! ## Measurement Phase Assignment -/

/-- Which phase a measurement belongs to. -/
def measurementPhase : proc.MeasLabel → GaugingPhase
  | .phase1 _ => .preDeformation
  | .edgeInit _ => .deformedCode
  | .phase2 _ => .deformedCode
  | .phase3 _ => .postDeformation

@[simp] theorem measurementPhase_phase1 (m : PreDeformationMeasurement J proc.d) :
    proc.measurementPhase (.phase1 m) = .preDeformation := rfl

@[simp] theorem measurementPhase_edgeInit (ei : EdgeInitialization G.edgeSet) :
    proc.measurementPhase (.edgeInit ei) = .deformedCode := rfl

@[simp] theorem measurementPhase_phase2 (m : DeformedCodeMeasurement V C J proc.d) :
    proc.measurementPhase (.phase2 m) = .deformedCode := rfl

@[simp] theorem measurementPhase_phase3
    (m : PostDeformationMeasurement J G.edgeSet proc.d) :
    proc.measurementPhase (.phase3 m) = .postDeformation := rfl

/-! ## Integer Time Assignment -/

/-- The integer time associated with a measurement. -/
def measurementTime : proc.MeasLabel → ℕ
  | .phase1 pm => pm.round.val
  | .edgeInit _ => proc.d
  | .phase2 dm => proc.d + match dm with
    | .gaussLaw _ r => r.val
    | .flux _ r => r.val
    | .deformed _ r => r.val
  | .phase3 pm => 2 * proc.d + match pm with
    | .edgeZ _ => 0
    | .originalCheck _ r => r.val

theorem measurementTime_phase1_lt (pm : PreDeformationMeasurement J proc.d) :
    proc.measurementTime (.phase1 pm) < proc.d := by
  unfold measurementTime; exact pm.round.isLt

theorem measurementTime_phase2_ge (dm : DeformedCodeMeasurement V C J proc.d) :
    proc.d ≤ proc.measurementTime (.phase2 dm) := by
  cases dm <;> simp [measurementTime]

theorem measurementTime_phase2_lt (dm : DeformedCodeMeasurement V C J proc.d) :
    proc.measurementTime (.phase2 dm) < 2 * proc.d := by
  cases dm <;> simp [measurementTime] <;> omega

theorem measurementTime_phase3_ge
    (pm : PostDeformationMeasurement J G.edgeSet proc.d) :
    2 * proc.d ≤ proc.measurementTime (.phase3 pm) := by
  cases pm <;> simp [measurementTime]

theorem measurementTime_phase3_lt
    (pm : PostDeformationMeasurement J G.edgeSet proc.d) :
    proc.measurementTime (.phase3 pm) < 3 * proc.d := by
  cases pm with
  | edgeZ _ => simp [measurementTime]; have := proc.d_pos; omega
  | originalCheck _ r => simp [measurementTime]; omega

theorem measurementTime_edgeInit (ei : EdgeInitialization G.edgeSet) :
    proc.measurementTime (.edgeInit ei) = proc.d := by
  unfold measurementTime; rfl

/-- Measurement time is consistent with phase assignment. -/
theorem measurementTime_consistent_with_phase (m : proc.MeasLabel) :
    phaseOf proc.d (proc.measurementTime m) = proc.measurementPhase m := by
  cases m with
  | phase1 pm =>
    simp only [measurementPhase_phase1]
    exact phaseOf_preDeformation (measurementTime_phase1_lt proc pm)
  | edgeInit ei =>
    simp only [measurementPhase_edgeInit, measurementTime]
    apply phaseOf_deformedCode (le_refl _)
    have := proc.d_pos; omega
  | phase2 dm =>
    simp only [measurementPhase_phase2]
    exact phaseOf_deformedCode (measurementTime_phase2_ge proc dm)
      (measurementTime_phase2_lt proc dm)
  | phase3 pm =>
    simp only [measurementPhase_phase3]
    exact phaseOf_postDeformation (measurementTime_phase3_ge proc pm)

/-! ## Phase Predicates -/

/-- A measurement label belongs to Phase 1. -/
def isPhase1 : proc.MeasLabel → Bool
  | .phase1 _ => true
  | _ => false

/-- A measurement label belongs to Phase 2. -/
def isPhase2 : proc.MeasLabel → Bool
  | .phase2 _ => true
  | .edgeInit _ => true
  | _ => false

/-- A measurement label belongs to Phase 3. -/
def isPhase3 : proc.MeasLabel → Bool
  | .phase3 _ => true
  | _ => false

/-! ## Qubit Types -/

/-- The qubit type for the procedure: extended system V ⊕ E(G). -/
abbrev ProcedureQubits := GaussFlux.ExtQubit G

/-! ## Operators Being Measured in Phase 2 -/

/-- The Pauli operator for a Phase 2 measurement. -/
def phase2Operator (dm : DeformedCodeMeasurement V C J proc.d) :
    PauliOp (GaussFlux.ExtQubit G) :=
  match dm with
  | .gaussLaw v _ => gaussLawChecks G v
  | .flux p _ => fluxChecks G cycles p
  | .deformed j _ => deformedOriginalChecks G checks proc.deformedData j

/-- Each Phase 2 operator is a check of the deformed code. -/
theorem phase2Operator_is_allChecks
    (dm : DeformedCodeMeasurement V C J proc.d) :
    ∃ ci : CheckIndex V C J,
      proc.phase2Operator dm =
        allChecks G cycles checks proc.deformedData ci := by
  match dm with
  | .gaussLaw v _ => exact ⟨.gaussLaw v, rfl⟩
  | .flux p _ => exact ⟨.flux p, rfl⟩
  | .deformed j _ => exact ⟨.deformed j, rfl⟩

/-- All Phase 2 measurements pairwise commute. -/
theorem phase2Operators_commute
    (dm₁ dm₂ : DeformedCodeMeasurement V C J proc.d) :
    PauliCommute (proc.phase2Operator dm₁)
                 (proc.phase2Operator dm₂) := by
  obtain ⟨ci₁, h1⟩ := proc.phase2Operator_is_allChecks dm₁
  obtain ⟨ci₂, h2⟩ := proc.phase2Operator_is_allChecks dm₂
  rw [h1, h2]
  exact allChecks_commute G cycles checks proc.deformedData proc.cycleParity
    proc.checks_commute ci₁ ci₂

/-- All Phase 2 operators are self-inverse. -/
theorem phase2Operators_selfInverse
    (dm : DeformedCodeMeasurement V C J proc.d) :
    proc.phase2Operator dm * proc.phase2Operator dm = 1 := by
  obtain ⟨ci, h⟩ := proc.phase2Operator_is_allChecks dm
  rw [h]
  exact allChecks_self_inverse G cycles checks proc.deformedData ci

/-! ## Phase 2 Check Identification -/

theorem phase2_gaussLaw_eq (v : V) (r : Fin proc.d) :
    proc.phase2Operator (.gaussLaw v r) = gaussLawChecks G v := rfl

theorem phase2_flux_eq (p : C) (r : Fin proc.d) :
    proc.phase2Operator (.flux p r) = fluxChecks G cycles p := rfl

theorem phase2_deformed_eq (j : J) (r : Fin proc.d) :
    proc.phase2Operator (.deformed j r) =
    deformedOriginalChecks G checks proc.deformedData j := rfl

/-- The product of all Gauss's law operators equals the logical L. -/
theorem phase2_gauss_product_eq_logical :
    ∏ v : V, proc.phase2Operator
      (.gaussLaw v (⟨0, proc.d_pos⟩ : Fin proc.d)) =
    GaussFlux.logicalOp G := by
  simp only [phase2Operator, gaussLawChecks]
  exact GaussFlux.gaussLaw_product G

/-! ## Detectors -/

/-- Repeated measurement detector for consecutive Phase 1 rounds. -/
def phase1RepeatedDetector
    (j : J) (r r' : Fin proc.d) (_hr : r.val + 1 = r'.val) :
    Detector proc.MeasLabel where
  measurements := {.phase1 ⟨j, r⟩, .phase1 ⟨j, r'⟩}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-- Repeated measurement detector for Gauss's law in Phase 2. -/
def phase2RepeatedDetector_gauss
    (v : V) (r r' : Fin proc.d) (_hr : r.val + 1 = r'.val) :
    Detector proc.MeasLabel where
  measurements := {.phase2 (.gaussLaw v r), .phase2 (.gaussLaw v r')}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-- Repeated measurement detector for flux in Phase 2. -/
def phase2RepeatedDetector_flux
    (p : C) (r r' : Fin proc.d) (_hr : r.val + 1 = r'.val) :
    Detector proc.MeasLabel where
  measurements := {.phase2 (.flux p r), .phase2 (.flux p r')}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-- Repeated measurement detector for deformed checks in Phase 2. -/
def phase2RepeatedDetector_deformed
    (j : J) (r r' : Fin proc.d) (_hr : r.val + 1 = r'.val) :
    Detector proc.MeasLabel where
  measurements := {.phase2 (.deformed j r), .phase2 (.deformed j r')}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-- Edge initialization detector: init |0⟩ at t_i and Z_e measurement at t_o. -/
def edgeInitDetector (e : G.edgeSet) :
    Detector proc.MeasLabel where
  measurements := {.edgeInit ⟨e⟩, .phase3 (.edgeZ e)}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-- Boundary detector: last Phase 1 round to first Phase 2 round. -/
def phase1_to_phase2_detector
    (j : J) (r_last : Fin proc.d) (r_first : Fin proc.d)
    (_h_last : r_last.val + 1 = proc.d) (_h_first : r_first.val = 0) :
    Detector proc.MeasLabel where
  measurements := {.phase1 ⟨j, r_last⟩, .phase2 (.deformed j r_first)}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-- Boundary detector: last Phase 2 round to first Phase 3 round. -/
def phase2_to_phase3_detector
    (j : J) (r_last : Fin proc.d) (r_first : Fin proc.d)
    (_h_last : r_last.val + 1 = proc.d) (_h_first : r_first.val = 0) :
    Detector proc.MeasLabel where
  measurements := {.phase2 (.deformed j r_last), .phase3 (.originalCheck j r_first)}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-! ## Key Properties -/

/-- Phase 1 has |J| · d measurements. -/
theorem phase1_measurement_count :
    Fintype.card (PreDeformationMeasurement J proc.d) =
    Fintype.card J * proc.d := by
  rw [show Fintype.card (PreDeformationMeasurement J proc.d) =
    Fintype.card (J × Fin proc.d) from Fintype.card_congr
      ⟨fun m => (m.checkIdx, m.round), fun ⟨j, r⟩ => ⟨j, r⟩,
       fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩]
  rw [Fintype.card_prod, Fintype.card_fin]

/-- Phase 2 has (|V| + |C| + |J|) · d measurements. -/
theorem phase2_measurement_count :
    Fintype.card (DeformedCodeMeasurement V C J proc.d) =
    (Fintype.card V + Fintype.card C + Fintype.card J) * proc.d := by
  rw [show Fintype.card (DeformedCodeMeasurement V C J proc.d) =
    Fintype.card ((V × Fin proc.d) ⊕ (C × Fin proc.d) ⊕ (J × Fin proc.d)) from
    Fintype.card_congr
      ⟨fun m => match m with
        | .gaussLaw v r => Sum.inl (v, r)
        | .flux p r => Sum.inr (Sum.inl (p, r))
        | .deformed j r => Sum.inr (Sum.inr (j, r)),
       fun s => match s with
        | Sum.inl (v, r) => .gaussLaw v r
        | Sum.inr (Sum.inl (p, r)) => .flux p r
        | Sum.inr (Sum.inr (j, r)) => .deformed j r,
       fun m => by cases m <;> rfl,
       fun s => by rcases s with ⟨v, r⟩ | ⟨p, r⟩ | ⟨j, r⟩ <;> rfl⟩]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; ring

/-- Edge initialization count is |E|. -/
theorem edgeInit_count :
    Fintype.card (EdgeInitialization G.edgeSet) = Fintype.card G.edgeSet :=
  Fintype.card_congr ⟨fun ei => ei.edge, fun e => ⟨e⟩, fun ⟨_⟩ => rfl, fun _ => rfl⟩

/-! ## Gauging Sign -/

/-- The gauging measurement sign from Phase 2 Gauss outcomes. -/
def gaugingSign (gaussOutcomes : V → ZMod 2) : ZMod 2 :=
  ∑ v : V, gaussOutcomes v

private lemma zmod2_dichotomy (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem gaugingSign_zero_or_one (gaussOutcomes : V → ZMod 2) :
    gaugingSign gaussOutcomes = 0 ∨ gaugingSign gaussOutcomes = 1 :=
  zmod2_dichotomy _

/-- The sign from the FT procedure agrees with the Def 5 measurement sign. -/
theorem gaugingSign_eq_measurementSign
    (gaussOutcomes : V → ZMod 2)
    (edgeOutcomes : G.edgeSet → ZMod 2) :
    gaugingSign gaussOutcomes =
    GaugingMeasurement.measurementSign G
      ⟨gaussOutcomes, edgeOutcomes⟩ := by
  simp [gaugingSign, GaugingMeasurement.measurementSign]

/-! ## Spacetime Fault Model -/

/-- A spacetime fault in the fault-tolerant gauging procedure. -/
abbrev ProcedureFault :=
  SpacetimeFault (GaussFlux.ExtQubit G) ℕ proc.MeasLabel

/-! ## Phase 2 Consistency -/

/-- Gauss's law checks in Phase 2 are pure X-type. -/
theorem phase2_gaussLaw_pure_X (v : V) (r : Fin proc.d) :
    (proc.phase2Operator (.gaussLaw v r)).zVec = 0 :=
  GaussFlux.gaussLawOp_zVec G v

/-- Flux checks in Phase 2 are pure Z-type. -/
theorem phase2_flux_pure_Z (p : C) (r : Fin proc.d) :
    (proc.phase2Operator (.flux p r)).xVec = 0 :=
  GaussFlux.fluxOp_xVec G cycles p

/-- Deformed checks in Phase 2 have no X-support on edge qubits. -/
theorem phase2_deformed_noXOnEdges (j : J) (r : Fin proc.d)
    (e : G.edgeSet) :
    (proc.phase2Operator (.deformed j r)).xVec (Sum.inr e) = 0 :=
  DeformedOperator.deformedOpExt_xVec_edge G (checks j) (proc.deformedData.edgePath j) e

end FaultTolerantGaugingProcedure
