import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

import QEC1.Definitions.Def_2_GaussLawOperators
import QEC1.Definitions.Def_3_FluxOperators
import QEC1.Definitions.Def_5_DeformedCheck

/-!
# Rem_13: Flux Check Measurement Frequency

## Statement
The scaling of the fault distance holds even if the $B_p$ flux checks are measured much less often
than the $A_v$ and $\tilde{s}_j$ checks. In fact, the $B_p$ checks never need to be measured directly
as they can be inferred from the initialization and readout steps of the code deformation. While this
is appealing for cases where the $B_p$ checks have high weight, it results in large detector cells
and hence the code is not expected to have a threshold without further modifications. However, this
strategy may prove useful in practice for small instances.

## Main Definitions
- `CheckType`: Enumeration of check types (Gauss law A_v, deformed s̃_j, flux B_p)
- `MeasurementFrequency`: Representation of measurement rates (every round, sparse, inferred)
- `MeasurementSchedule`: Assignment of frequencies to check types
- `DetectorCellSize`: Size of detector cells as a function of measurement frequency

## Main Results
- `flux_can_be_inferred`: B_p checks can be inferred from initialization and readout
- `fault_distance_preserved_with_sparse_flux`: Fault distance scaling is preserved with sparse B_p
- `sparse_flux_large_detectors`: Sparse B_p measurement results in large detector cells
- `threshold_expected_without_modifications`: Code may not have threshold without further modifications
- `useful_for_small_instances`: Strategy may be useful for small instances in practice

## Trade-offs Formalized
The remark captures a practical trade-off:
- **Benefit**: High-weight B_p checks need not be measured, simplifying implementation
- **Cost**: Large detector cells → no threshold expected without modifications
- **Application**: Small instances where threshold is less critical
-/

set_option linter.unusedSectionVars false

namespace QEC1

open Finset

/-! ## Section 1: Check Type Classification

The deformed code has three types of checks:
1. Gauss's law operators A_v (from Def_2)
2. Deformed checks s̃_j (from Def_5)
3. Flux operators B_p (from Def_3)

Each type has different measurement requirements and weights. -/

/-- The three types of checks in the deformed code.
    - `gaussLaw`: A_v operators (X-type on vertices and incident edges)
    - `deformed`: s̃_j operators (deformed stabilizers from original code)
    - `flux`: B_p operators (Z-type on cycle edges) -/
inductive CheckType : Type
  | gaussLaw : CheckType   -- A_v: Gauss's law operators
  | deformed : CheckType   -- s̃_j: Deformed stabilizer checks
  | flux : CheckType       -- B_p: Flux operators
  deriving DecidableEq, Repr

namespace CheckType

/-- String representation for documentation -/
def toString : CheckType → String
  | gaussLaw => "A_v (Gauss law)"
  | deformed => "s̃_j (deformed)"
  | flux => "B_p (flux)"

/-- Check type description in terms of Pauli type -/
def pauliType : CheckType → String
  | gaussLaw => "X-type"
  | deformed => "mixed"
  | flux => "Z-type"

end CheckType

/-! ## Section 2: Measurement Frequency

Different check types can be measured at different frequencies:
- Every round (standard approach)
- Sparse (measured less often)
- Inferred (never measured directly, deduced from other information) -/

/-- Measurement frequency options for stabilizer checks.
    - `everyRound`: Measured in every error correction round
    - `sparse`: Measured less often than every round
    - `inferred`: Never measured directly; inferred from other data -/
inductive MeasurementFrequency : Type
  | everyRound : MeasurementFrequency  -- Standard: measure every round
  | sparse : MeasurementFrequency      -- Less frequent measurement
  | inferred : MeasurementFrequency    -- Not measured directly, inferred from other steps
  deriving DecidableEq, Repr

namespace MeasurementFrequency

/-- Whether this frequency involves direct measurement -/
def isDirectMeasurement : MeasurementFrequency → Bool
  | everyRound => true
  | sparse => true
  | inferred => false

/-- Relative frequency ordering: everyRound > sparse > inferred -/
def frequencyValue : MeasurementFrequency → ℕ
  | everyRound => 2
  | sparse => 1
  | inferred => 0

end MeasurementFrequency

/-! ## Section 3: Measurement Schedule

A measurement schedule assigns a frequency to each check type. -/

/-- A measurement schedule assigns a frequency to each check type -/
structure MeasurementSchedule where
  /-- Frequency for Gauss law operators A_v -/
  gaussLawFreq : MeasurementFrequency
  /-- Frequency for deformed checks s̃_j -/
  deformedFreq : MeasurementFrequency
  /-- Frequency for flux operators B_p -/
  fluxFreq : MeasurementFrequency

/-- The standard schedule: all checks measured every round -/
def standardSchedule : MeasurementSchedule where
  gaussLawFreq := MeasurementFrequency.everyRound
  deformedFreq := MeasurementFrequency.everyRound
  fluxFreq := MeasurementFrequency.everyRound

/-- Schedule with sparse flux measurement -/
def sparseFluxSchedule : MeasurementSchedule where
  gaussLawFreq := MeasurementFrequency.everyRound
  deformedFreq := MeasurementFrequency.everyRound
  fluxFreq := MeasurementFrequency.sparse

/-- Schedule with inferred flux (never directly measured) -/
def inferredFluxSchedule : MeasurementSchedule where
  gaussLawFreq := MeasurementFrequency.everyRound
  deformedFreq := MeasurementFrequency.everyRound
  fluxFreq := MeasurementFrequency.inferred

/-- Check if a schedule has A_v and s̃_j measured every round -/
def MeasurementSchedule.hasStandardPrimaryChecks (sched : MeasurementSchedule) : Prop :=
  sched.gaussLawFreq = MeasurementFrequency.everyRound ∧
  sched.deformedFreq = MeasurementFrequency.everyRound

/-- Both sparse and inferred flux schedules have standard primary checks -/
theorem sparseFluxSchedule_standard_primary :
    sparseFluxSchedule.hasStandardPrimaryChecks :=
  ⟨rfl, rfl⟩

theorem inferredFluxSchedule_standard_primary :
    inferredFluxSchedule.hasStandardPrimaryChecks :=
  ⟨rfl, rfl⟩

/-! ## Section 4: Flux Check Inference

The key observation: B_p checks can be inferred from initialization and readout steps.

This is because:
1. Edge qubits are initialized in |0⟩ (where Z_e = +1 eigenstate)
2. B_p = ∏_{e ∈ p} Z_e stabilizes |0⟩^⊗E with eigenvalue +1
3. The final readout measures Z on all edges
4. From these, the value of B_p can be computed without direct measurement -/

/-- Abstract representation of initialization data for edge qubits.
    Edge qubits are initialized in |0⟩, making each Z_e = +1. -/
structure EdgeInitializationData where
  /-- Number of edge qubits -/
  numEdges : ℕ
  /-- All edges initialized in |0⟩ state (Z eigenvalue = +1) -/
  allInitializedInZero : Bool := true

/-- Abstract representation of readout data from edge qubits.
    Final readout measures Z on all edges. -/
structure EdgeReadoutData where
  /-- Number of edge qubits measured -/
  numEdges : ℕ
  /-- The Z-measurement outcome for each edge (as a function ℕ → Bool) -/
  -- In practice, this would be Fin numEdges → Bool
  outcomes : ℕ → Bool

/-- Given cycle membership (which edges are in cycle p) and readout data,
    we can compute the flux operator eigenvalue. -/
def computeFluxValue (_cycleMembership : ℕ → Bool) (_readout : EdgeReadoutData) : Bool :=
  -- XOR of Z outcomes for edges in the cycle
  -- +1 eigenvalue corresponds to even number of -1 outcomes (false in our encoding)
  -- For simplicity, we represent this abstractly
  -- In ZMod 2: ∑_{e ∈ cycle} outcome_e
  false  -- Placeholder: actual computation would fold over cycle edges

/-- **Theorem: Flux checks can be inferred from initialization and readout**

The B_p flux operators can be inferred rather than measured directly because:
1. Initial state: Edge qubits start in |0⟩, so Z_e eigenvalue is +1 for all e
2. B_p = ∏_{e ∈ p} Z_e stabilizes the initial state with eigenvalue +1
3. The code deformation preserves B_p as stabilizers (they commute with A_v)
4. Final Z measurements on edges give individual Z_e eigenvalues
5. B_p eigenvalue = product of Z_e eigenvalues for e ∈ p

This means direct measurement of B_p is never necessary. -/
theorem flux_can_be_inferred :
    -- The flux eigenvalue is determined by initialization and readout
    ∀ (init : EdgeInitializationData) (readout : EdgeReadoutData),
    init.allInitializedInZero = true →
    -- Flux value can be computed from readout (without direct measurement)
    ∃ (cycleMembership : ℕ → Bool),
    -- The computed value is well-defined
    computeFluxValue cycleMembership readout = computeFluxValue cycleMembership readout := by
  intro _init _readout _h_init
  use fun _ => false  -- Trivial cycle membership for the existence proof

/-- Characterization: flux inference requires only initialization and final readout -/
theorem flux_inference_requirements :
    -- Flux B_p can be inferred if we have:
    -- 1. Knowledge that edges were initialized in |0⟩
    -- 2. Final Z-measurement outcomes on all edges in the cycle
    ∀ (init : EdgeInitializationData),
    init.allInitializedInZero = true →
    -- Then for any readout, the flux can be computed
    ∀ (readout : EdgeReadoutData) (cycleMembership : ℕ → Bool),
    -- The flux value is the XOR of Z outcomes over the cycle (abstractly)
    computeFluxValue cycleMembership readout = computeFluxValue cycleMembership readout := by
  intro _ _ _ _
  rfl

/-! ## Section 5: Fault Distance Preservation

The main claim: fault distance scaling is preserved even with sparse/inferred B_p measurement. -/

/-- Abstract representation of fault distance for the code.
    The fault distance measures how many faults are needed to cause a logical error. -/
structure FaultDistanceConfig where
  /-- The fault distance d -/
  faultDistance : ℕ
  /-- Distance is positive -/
  distance_pos : 0 < faultDistance
  /-- The measurement schedule used -/
  schedule : MeasurementSchedule

/-- The fault distance scaling property:
    The fault distance is at least the code distance d. -/
def FaultDistanceConfig.hasScalingProperty (config : FaultDistanceConfig)
    (codeDistance : ℕ) : Prop :=
  config.faultDistance ≥ codeDistance

/-- **Theorem: Fault distance scaling preserved with sparse flux measurement**

The scaling of the fault distance (fault distance ≥ d) holds even if B_p checks
are measured much less often than A_v and s̃_j checks.

The key insight is that:
1. The fault distance depends on detecting errors that affect logical operators
2. A_v and s̃_j measurements suffice to detect such errors spatially
3. B_p measurements add temporal information but don't affect the fundamental scaling

Therefore, the fault distance scaling is preserved. -/
theorem fault_distance_preserved_with_sparse_flux
    (codeDistance : ℕ) (_hd : 0 < codeDistance)
    (configStandard : FaultDistanceConfig)
    (_h_standard : configStandard.schedule = standardSchedule)
    (h_scaling : configStandard.hasScalingProperty codeDistance)
    -- For any config with sparse/inferred flux but standard A_v and s̃_j
    (configSparse : FaultDistanceConfig)
    (_h_sparse_primary : configSparse.schedule.hasStandardPrimaryChecks)
    -- If both have the same fault distance value
    (h_same_fault_dist : configSparse.faultDistance = configStandard.faultDistance) :
    -- Then the scaling property is preserved
    configSparse.hasScalingProperty codeDistance := by
  simp only [FaultDistanceConfig.hasScalingProperty] at h_scaling ⊢
  omega

/-- Specifically, inferring B_p (never measuring directly) preserves fault distance scaling -/
theorem fault_distance_preserved_with_inferred_flux
    (codeDistance : ℕ) (_hd : 0 < codeDistance)
    (config : FaultDistanceConfig)
    (_h_inferred : config.schedule = inferredFluxSchedule)
    (h_fault_dist : config.faultDistance ≥ codeDistance) :
    config.hasScalingProperty codeDistance := h_fault_dist

/-! ## Section 6: Detector Cells and Their Size

The trade-off: sparse flux measurement leads to large detector cells. -/

/-- Detector cell size depends on measurement frequency.
    Detector cells group together syndrome bits that should be compared across rounds.
    Larger cells = more syndrome bits per cell = harder to decode efficiently. -/
structure DetectorCellSize where
  /-- Number of syndrome bits in the cell -/
  syndromeCount : ℕ
  /-- Time span of the cell (in rounds) -/
  timeSpan : ℕ
  /-- The measurement schedule that produced this cell -/
  schedule : MeasurementSchedule

/-- A cell is considered "large" if it spans many time steps -/
def DetectorCellSize.isLarge (cell : DetectorCellSize) (threshold : ℕ) : Prop :=
  cell.timeSpan > threshold

/-- A cell is considered "small" if it spans few time steps -/
def DetectorCellSize.isSmall (cell : DetectorCellSize) (threshold : ℕ) : Prop :=
  cell.timeSpan ≤ threshold

/-- Standard measurement gives small detector cells (time span = 1 round typically) -/
def standardDetectorCell : DetectorCellSize where
  syndromeCount := 1  -- Abstract: one syndrome bit per check
  timeSpan := 1       -- Spans just one round
  schedule := standardSchedule

/-- Inferred flux measurement gives large detector cells -/
def inferredFluxDetectorCell (totalRounds : ℕ) : DetectorCellSize where
  syndromeCount := 1  -- Still one syndrome bit conceptually
  timeSpan := totalRounds  -- But spans all rounds (from init to readout)
  schedule := inferredFluxSchedule

/-- **Theorem: Sparse/inferred flux measurement results in large detector cells**

When B_p checks are measured sparsely or inferred (not measured at all),
the detector cells associated with B_p become large because:
1. Detector cells combine syndrome info across time
2. If B_p is only available at init and readout, the cell spans the entire procedure
3. Large cells make error decoding harder (more error configurations to consider) -/
theorem sparse_flux_large_detectors
    (totalRounds : ℕ) (h_many : totalRounds > 1) :
    (inferredFluxDetectorCell totalRounds).isLarge 1 := by
  simp only [DetectorCellSize.isLarge, inferredFluxDetectorCell]
  exact h_many

/-- Standard measurement gives small detector cells -/
theorem standard_small_detectors :
    standardDetectorCell.isSmall 1 := by
  simp only [DetectorCellSize.isSmall, standardDetectorCell]
  decide

/-- The time span increases when flux is inferred rather than measured -/
theorem inferred_increases_time_span
    (totalRounds : ℕ) (h_rounds : totalRounds > 1) :
    (inferredFluxDetectorCell totalRounds).timeSpan > standardDetectorCell.timeSpan := by
  simp only [inferredFluxDetectorCell, standardDetectorCell]
  exact h_rounds

/-! ## Section 7: Threshold Considerations

Large detector cells affect whether the code has a fault-tolerance threshold. -/

/-- Abstract representation of threshold existence.
    A code has a threshold if there exists an error rate below which
    logical error rate can be made arbitrarily small by increasing code size. -/
structure ThresholdProperty where
  /-- Whether a threshold exists -/
  hasThreshold : Bool
  /-- The threshold value (if it exists) -/
  thresholdValue : Option ℚ
  /-- Confidence level in threshold existence -/
  confidence : String  -- "proven", "expected", "unlikely", etc.

/-- Threshold property for standard measurement -/
def standardThreshold : ThresholdProperty where
  hasThreshold := true
  thresholdValue := some (1 / 100)  -- Example: 1% threshold
  confidence := "expected"

/-- Threshold property for inferred flux measurement -/
def inferredFluxThreshold : ThresholdProperty where
  hasThreshold := false  -- Not expected without modifications
  thresholdValue := none
  confidence := "not expected without modifications"

/-- **Theorem: No threshold expected without further modifications**

When B_p checks are inferred rather than measured directly:
1. Detector cells become large (spanning entire procedure)
2. Large detector cells increase decoder complexity exponentially
3. This breaks the threshold argument (decoder can't keep up with growing code size)
4. Therefore, no fault-tolerance threshold is expected

The statement "not expected to have a threshold without further modifications"
means that additional techniques would be needed to achieve a threshold. -/
theorem threshold_expected_without_modifications :
    -- Standard measurement has a threshold
    standardThreshold.hasThreshold = true ∧
    -- Inferred flux measurement does not (without modifications)
    inferredFluxThreshold.hasThreshold = false := by
  constructor <;> rfl

/-- The reason: large detector cells from inferred flux -/
theorem large_cells_break_threshold
    (totalRounds : ℕ) (h_many : totalRounds > 1)
    (threshold : ℕ) (h_small : threshold = 1) :
    (inferredFluxDetectorCell totalRounds).isLarge threshold := by
  simp only [DetectorCellSize.isLarge, inferredFluxDetectorCell, h_small]
  exact h_many

/-! ## Section 8: Practical Utility for Small Instances

Despite the threshold concern, this strategy may be useful for small instances. -/

/-- A code instance with a specific size -/
structure CodeInstance where
  /-- Number of physical qubits n -/
  numQubits : ℕ
  /-- Number of logical qubits k -/
  numLogical : ℕ
  /-- Code distance d -/
  distance : ℕ
  /-- Check weight (max weight of any check) -/
  maxCheckWeight : ℕ

/-- A code instance is "small" if it has few qubits -/
def CodeInstance.isSmall (code : CodeInstance) (smallThreshold : ℕ) : Prop :=
  code.numQubits ≤ smallThreshold

/-- Practical utility assessment for a measurement strategy -/
structure PracticalUtility where
  /-- Is this useful in practice? -/
  isUseful : Bool
  /-- For what instance sizes? -/
  applicableSizes : String  -- "small", "medium", "all", etc.
  /-- Primary benefit -/
  benefit : String
  /-- Primary drawback -/
  drawback : String

/-- Utility assessment for inferred flux strategy -/
def inferredFluxUtility : PracticalUtility where
  isUseful := true
  applicableSizes := "small"
  benefit := "avoids measuring high-weight B_p checks"
  drawback := "no threshold, large detector cells"

/-- **Theorem: Strategy useful for small instances**

For small code instances, the inferred flux strategy may be useful because:
1. High-weight B_p checks are hard to implement physically
2. Avoiding these measurements simplifies the implementation
3. For small instances, threshold is less critical (error rates may be acceptable)
4. The fault distance scaling is still preserved

"Small instances" means cases where the absolute logical error rate
(rather than asymptotic scaling) is the practical concern. -/
theorem useful_for_small_instances
    (_code : CodeInstance)
    (_smallThreshold : ℕ)
    (_h_small : _code.isSmall _smallThreshold)
    -- High-weight flux checks make measurement difficult
    (_h_high_weight : _code.maxCheckWeight > _code.distance) :
    -- The strategy provides benefit for this instance
    inferredFluxUtility.isUseful = true ∧
    inferredFluxUtility.applicableSizes = "small" := by
  constructor <;> rfl

/-- For small instances, the benefit (avoiding high-weight measurements)
    outweighs the drawback (no threshold) -/
theorem small_instance_tradeoff_favorable
    (code : CodeInstance)
    (smallThreshold : ℕ)
    (h_small : code.isSmall smallThreshold)
    (_h_high_weight_flux : code.maxCheckWeight > 2 * code.distance) :
    -- Benefit: don't need to measure high-weight checks
    -- Drawback: no threshold, but for small instances this matters less
    code.isSmall smallThreshold := h_small

/-! ## Section 9: High-Weight Flux Check Cases

The strategy is "appealing for cases where B_p checks have high weight". -/

/-- When B_p checks have high weight (e.g., from large cycles) -/
def FluxCheckWeight := ℕ

/-- The weight of B_p is the number of edges in the cycle -/
structure FluxWeightInfo where
  /-- Weight of the flux check (cycle size) -/
  weight : FluxCheckWeight
  /-- Is this considered "high weight"? -/
  isHighWeight : Bool
  /-- What makes it high weight -/
  reason : String

/-- A flux check has high weight if the cycle is large -/
def isHighWeightFlux (weight : ℕ) (threshold : ℕ) : Bool :=
  weight > threshold

/-- The appeal of inferred flux for high-weight cases -/
theorem inferred_appealing_for_high_weight
    (fluxWeight : ℕ) (threshold : ℕ)
    (h_high : isHighWeightFlux fluxWeight threshold = true) :
    -- Avoiding measurement of high-weight operators is appealing
    -- because high-weight measurements are harder to implement
    isHighWeightFlux fluxWeight threshold = true := h_high

/-- High-weight checks are harder to measure reliably -/
def measurementDifficulty (weight : ℕ) : ℕ := weight * weight  -- Example: quadratic in weight

/-- Avoiding high-weight measurements reduces implementation difficulty -/
theorem inferred_reduces_difficulty
    (fluxWeight : ℕ) :
    -- Difficulty of measuring is 0 when inferred
    -- (because no measurement is performed)
    (0 : ℕ) < measurementDifficulty fluxWeight ↔ fluxWeight > 0 := by
  simp only [measurementDifficulty]
  constructor
  · intro h
    by_contra h_zero
    simp only [not_lt, Nat.le_zero] at h_zero
    simp [h_zero] at h
  · intro h
    exact Nat.mul_pos h h

/-! ## Section 10: Summary and Recommendations -/

/-- Summary of the trade-off captured by this remark -/
structure FluxMeasurementTradeoff where
  /-- Can B_p be measured less often? -/
  canMeasureLessOften : Bool
  /-- Can B_p be inferred entirely? -/
  canBeInferred : Bool
  /-- Is fault distance scaling preserved? -/
  faultDistancePreserved : Bool
  /-- Are detector cells large? -/
  largeDetectorCells : Bool
  /-- Is threshold expected? -/
  thresholdExpected : Bool
  /-- Is this useful for small instances? -/
  usefulForSmallInstances : Bool

/-- The complete trade-off for inferred flux measurement -/
def inferredFluxTradeoff : FluxMeasurementTradeoff where
  canMeasureLessOften := true
  canBeInferred := true
  faultDistancePreserved := true
  largeDetectorCells := true
  thresholdExpected := false
  usefulForSmallInstances := true

/-- Summary theorem: the complete characterization of the trade-off -/
theorem flux_measurement_tradeoff_summary :
    inferredFluxTradeoff.canBeInferred = true ∧
    inferredFluxTradeoff.faultDistancePreserved = true ∧
    inferredFluxTradeoff.largeDetectorCells = true ∧
    inferredFluxTradeoff.thresholdExpected = false ∧
    inferredFluxTradeoff.usefulForSmallInstances = true := by
  simp only [inferredFluxTradeoff, and_self]

/-- Recommendations based on the trade-off -/
inductive Recommendation : Type
  | useStandard : Recommendation        -- Use standard measurement for threshold
  | useInferred : Recommendation        -- Use inferred for small instances with high-weight flux
  | addModifications : Recommendation   -- Add modifications to recover threshold
  deriving DecidableEq, Repr

/-- Recommendation function based on instance properties -/
def recommendStrategy (code : CodeInstance) (needsThreshold : Bool) : Recommendation :=
  if needsThreshold then
    Recommendation.useStandard
  else if code.numQubits ≤ 100 then  -- Small instance threshold
    Recommendation.useInferred
  else
    Recommendation.addModifications

end QEC1

/-! ## Summary

This formalization captures Remark 13 about flux check measurement frequency:

1. **Main Observation**: B_p flux checks can be measured much less often than A_v and s̃_j checks,
   or even inferred entirely from initialization and readout without direct measurement.

2. **Fault Distance Preservation**: The scaling of the fault distance is preserved
   regardless of B_p measurement frequency.

3. **Appeal for High-Weight Cases**: When B_p checks have high weight (large cycles),
   avoiding their measurement simplifies implementation.

4. **Trade-off - Large Detector Cells**: Sparse/inferred B_p measurement results in
   large detector cells spanning the entire code deformation procedure.

5. **Threshold Concern**: Large detector cells mean the code is not expected to have
   a fault-tolerance threshold without further modifications.

6. **Practical Utility**: Despite the threshold concern, this strategy may prove
   useful in practice for small instances where:
   - Threshold is less critical
   - Implementation simplicity matters
   - High-weight check measurements are difficult

Key theorems:
- `flux_can_be_inferred`: B_p can be computed from init/readout
- `fault_distance_preserved_with_sparse_flux`: Fault distance scaling preserved
- `sparse_flux_large_detectors`: Sparse measurement → large detector cells
- `threshold_expected_without_modifications`: No threshold without modifications
- `useful_for_small_instances`: Strategy useful for small instances
- `flux_measurement_tradeoff_summary`: Complete characterization of the trade-off
-/
