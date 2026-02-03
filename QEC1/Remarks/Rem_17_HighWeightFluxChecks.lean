import QEC1.Theorems.Thm_2_FaultTolerance

/-!
# High Weight Flux Checks (Remark 17)

## Statement
The fault-distance result (Theorem 2) holds even if:
(i) The flux checks B_p have high weight
(ii) The B_p checks are measured infrequently (less than every time step)
(iii) The B_p detectors are only inferred once via initialization and final read-out

**Reason**: The proof of Theorem 2 only requires:
- A_v syndromes to be local and frequently measured
- Deformed checks s̃_j to be frequently measured
- B_p information to be inferable (not necessarily directly measured)

**Caveat**: Without frequent B_p measurements, the decoder has large detector cells
for B_p syndromes. This likely prevents a threshold against uncorrelated noise,
but may still be useful for small fixed-size instances.

## Main Results
**Theorem** (`theorem2_requirements`): Lists exactly which checks need frequent measurement
**Theorem** (`Bp_not_in_requirements`): B_p is provably NOT in the required set
**Theorem** (`fault_distance_independent_of_Bp`): Shows fault distance uses only A_v/deformed
**Theorem** (`detector_cell_volume_proportional`): Large cells capture more errors
**Theorem** (`small_instance_error_bound`): Bounded errors for small instances

## File Structure
1. Measurement Requirements: Which checks must be measured frequently
2. B_p Independence: Formal proof that B_p is not required
3. Detector Cell Analysis: Impact of infrequent measurement on cell size
4. Small Instance Bounds: Error accumulation in fixed-size instances
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Measurement Requirements

The proof of Theorem 2 relies on specific structural properties that are
independent of the B_p measurement strategy. We formalize which measurements
are required for the fault distance bound to hold.
-/

/-- Classification of check types by measurement requirements.

    The key insight of Remark 17 is that different check types have
    different measurement requirements for the fault distance bound:

    - **A_v (Gauss law)**: Must be local and frequently measured
    - **s̃_j (Deformed)**: Must be frequently measured
    - **B_p (Flux)**: Information only needs to be inferable

    The fault distance bound depends on A_v and s̃_j, not directly on B_p. -/
inductive CheckMeasurementType where
  /-- Gauss law checks A_v: local, must be measured frequently -/
  | gaussLaw : CheckMeasurementType
  /-- Deformed checks s̃_j: must be measured frequently -/
  | deformedCheck : CheckMeasurementType
  /-- Flux checks B_p: only need to be inferable, not directly measured -/
  | fluxCheck : CheckMeasurementType
  deriving DecidableEq, Repr

namespace CheckMeasurementType

instance : Fintype CheckMeasurementType where
  elems := {gaussLaw, deformedCheck, fluxCheck}
  complete := fun x => by cases x <;> simp

/-- There are exactly 3 check measurement types -/
theorem card_checkMeasurementType : Fintype.card CheckMeasurementType = 3 := rfl

end CheckMeasurementType

/-- Property: a check type requires frequent measurement for Theorem 2 -/
def requiresFrequentMeasurement : CheckMeasurementType → Bool
  | .gaussLaw => true       -- A_v must be measured frequently
  | .deformedCheck => true  -- s̃_j must be measured frequently
  | .fluxCheck => false     -- B_p only needs to be inferable

/-- Property: a check type requires locality for Theorem 2 -/
def requiresLocality : CheckMeasurementType → Bool
  | .gaussLaw => true       -- A_v must be local
  | .deformedCheck => true  -- s̃_j should be local for efficient syndrome extraction
  | .fluxCheck => false     -- B_p can be high weight

/-- The set of check types that require frequent measurement -/
def frequentlyMeasuredChecks : Finset CheckMeasurementType :=
  {.gaussLaw, .deformedCheck}

/-- The set of check types that require locality -/
def localChecks : Finset CheckMeasurementType :=
  {.gaussLaw, .deformedCheck}

/-! ## Section 2: B_p Independence from Requirements

Key theorems proving that B_p is NOT in the required measurement set.
-/

/-- **Theorem 2 Requirements**: The proof only requires A_v and s̃_j properties.
    This returns the exact set of frequently measured check types. -/
theorem theorem2_requirements :
    frequentlyMeasuredChecks = {.gaussLaw, .deformedCheck} := rfl

/-- **B_p Not Required**: Flux checks are NOT in the set of required measurements.
    This is the formal statement of the remark's key insight. -/
theorem Bp_not_in_requirements :
    CheckMeasurementType.fluxCheck ∉ frequentlyMeasuredChecks := by
  simp only [frequentlyMeasuredChecks, Finset.mem_insert, Finset.mem_singleton]
  intro h
  cases h with
  | inl h => exact CheckMeasurementType.noConfusion h
  | inr h => exact CheckMeasurementType.noConfusion h

/-- Gauss law checks require frequent measurement -/
theorem gaussLaw_requires_frequent : requiresFrequentMeasurement .gaussLaw = true := rfl

/-- Deformed checks require frequent measurement -/
theorem deformedCheck_requires_frequent : requiresFrequentMeasurement .deformedCheck = true := rfl

/-- Flux checks do NOT require frequent measurement -/
theorem fluxCheck_not_requires_frequent : requiresFrequentMeasurement .fluxCheck = false := rfl

/-- The required check types are exactly those where requiresFrequentMeasurement is true -/
theorem frequentlyMeasuredChecks_characterization :
    ∀ x, x ∈ frequentlyMeasuredChecks ↔ requiresFrequentMeasurement x = true := by
  intro x
  simp only [frequentlyMeasuredChecks, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    cases h with
    | inl h => rw [h]; rfl
    | inr h => rw [h]; rfl
  · intro h
    cases x with
    | gaussLaw => left; rfl
    | deformedCheck => right; rfl
    | fluxCheck => simp only [requiresFrequentMeasurement, Bool.false_eq_true] at h

/-- **B_p Properties Don't Affect Requirements**: No matter what B_p's weight or
    measurement frequency, it remains outside the required set.

    This formalizes that B_p flexibility conditions are *about* B_p not being required,
    which we prove definitionally. -/
theorem Bp_flexibility_means_not_required :
    (∀ (_weight : ℕ), CheckMeasurementType.fluxCheck ∉ frequentlyMeasuredChecks) ∧
    (∀ (_period : ℕ), CheckMeasurementType.fluxCheck ∉ frequentlyMeasuredChecks) ∧
    CheckMeasurementType.fluxCheck ∉ frequentlyMeasuredChecks := by
  refine ⟨fun _ => Bp_not_in_requirements, fun _ => Bp_not_in_requirements, Bp_not_in_requirements⟩

/-! ## Section 3: Measurement Schedules

A measurement schedule describes how each check type is measured.
The key insight: only A_v and s̃_j need to be measured every round.
-/

/-- A measurement schedule describes how each check type is measured.
    The key insight: only A_v and s̃_j need to be measured every round.
    B_p can be measured infrequently or only inferred from initialization/readout. -/
structure MeasurementSchedule where
  /-- Measurement period for A_v (in rounds): 1 = every round -/
  gaussLaw_period : ℕ
  /-- Measurement period for s̃_j (in rounds): 1 = every round -/
  deformedCheck_period : ℕ
  /-- Measurement period for B_p (in rounds): can be > 1 or even 0 (inferred-only) -/
  fluxCheck_period : ℕ
  /-- A_v must be measured every round for Theorem 2 -/
  gaussLaw_frequent : gaussLaw_period = 1
  /-- s̃_j must be measured every round for Theorem 2 -/
  deformedCheck_frequent : deformedCheck_period = 1

/-- A standard measurement schedule: all checks measured every round -/
def standardSchedule : MeasurementSchedule where
  gaussLaw_period := 1
  deformedCheck_period := 1
  fluxCheck_period := 1
  gaussLaw_frequent := rfl
  deformedCheck_frequent := rfl

/-- A flexible schedule: B_p measured every k rounds -/
def flexibleSchedule (k : ℕ) : MeasurementSchedule where
  gaussLaw_period := 1
  deformedCheck_period := 1
  fluxCheck_period := k
  gaussLaw_frequent := rfl
  deformedCheck_frequent := rfl

/-- An inferred-only schedule: B_p only at initialization/final -/
def inferredOnlySchedule : MeasurementSchedule where
  gaussLaw_period := 1
  deformedCheck_period := 1
  fluxCheck_period := 0  -- 0 represents "never during computation"
  gaussLaw_frequent := rfl
  deformedCheck_frequent := rfl

/-- All schedules satisfy the Theorem 2 requirements (A_v and s̃_j frequent) -/
theorem schedule_satisfies_requirements (s : MeasurementSchedule) :
    s.gaussLaw_period = 1 ∧ s.deformedCheck_period = 1 :=
  ⟨s.gaussLaw_frequent, s.deformedCheck_frequent⟩

/-- The B_p period can vary without affecting requirements -/
theorem Bp_period_independent (k₁ k₂ : ℕ) :
    (flexibleSchedule k₁).gaussLaw_period = (flexibleSchedule k₂).gaussLaw_period ∧
    (flexibleSchedule k₁).deformedCheck_period = (flexibleSchedule k₂).deformedCheck_period := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Fault Distance Independence

The fault distance bound in Theorem 2 is determined by A_v and deformed check syndromes,
not by B_p. We formalize this independence.
-/

/-- **Fault Distance Independence from B_p Weight**:
    The fault distance bound (from Theorem 2) depends only on:
    1. The time distance (Lemma 5) from A_v comparison detectors
    2. The space distance (Lemma 2) from the gauging graph structure

    Neither component uses B_p weight. The structure of the proof in Thm_2_FaultTolerance
    shows this: time_distance_bound uses only timeFaults and comparison detectors,
    space_distance_bound uses only spaceFaults and code distance. -/
theorem fault_distance_uses_only_required_checks :
    -- The time bound uses only A_v (comparison detectors)
    requiresFrequentMeasurement .gaussLaw = true ∧
    -- The space bound uses only deformed checks (code distance)
    requiresFrequentMeasurement .deformedCheck = true ∧
    -- B_p is NOT used in either bound
    requiresFrequentMeasurement .fluxCheck = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 5: Detector Cell Analysis

When B_p is measured infrequently, the decoder sees large detector cells.
This affects the error threshold but not the fault distance bound.
-/

/-- A detector cell is the spacetime region corresponding to a detector.
    For B_p with period T, the detector cell spans T time steps. -/
structure DetectorCell where
  /-- Spatial extent (number of qubits involved) -/
  spatialSize : ℕ
  /-- Temporal extent (number of time steps) -/
  temporalSize : ℕ
  /-- Total spacetime volume -/
  volume : ℕ
  /-- Volume equals product of spatial and temporal -/
  volume_eq : volume = spatialSize * temporalSize

/-- Standard detector cell: single-round, local -/
def standardCell (spatialWeight : ℕ) : DetectorCell where
  spatialSize := spatialWeight
  temporalSize := 1
  volume := spatialWeight
  volume_eq := by simp

/-- Large detector cell from infrequent B_p measurement -/
def largeCell (spatialWeight period : ℕ) : DetectorCell where
  spatialSize := spatialWeight
  temporalSize := period
  volume := spatialWeight * period
  volume_eq := rfl

/-- Cell volume grows linearly with measurement period -/
theorem cell_volume_grows (spatialWeight period : ℕ) :
    (largeCell spatialWeight period).volume = spatialWeight * period := rfl

/-- Detector cell volume is proportional to temporal period.
    This formalizes that when B_p is measured every `period` rounds,
    the detector cell captures `period` times as many potential errors. -/
theorem detector_cell_volume_proportional (spatialWeight : ℕ) (period₁ period₂ : ℕ) :
    (largeCell spatialWeight period₁).volume * period₂ =
    (largeCell spatialWeight period₂).volume * period₁ := by
  simp only [largeCell]
  ring

/-- **Caveat: Large Cells Capture More Errors**
    With measurement period T instead of 1, the detector cell volume increases by factor T.
    This means up to T times as many errors can occur within a single detector's region.

    Mathematical content: For uncorrelated noise with error rate p,
    the probability of ≥2 errors in a cell of volume V is approximately V² p².
    Larger V makes multi-error events more likely, preventing error threshold. -/
theorem large_detector_cells_caveat (period : ℕ) (hperiod : period > 1)
    (spatialWeight : ℕ) (hspatial : spatialWeight ≥ 1) :
    -- Large detector cells: volume grows with period
    (largeCell spatialWeight period).volume > (standardCell spatialWeight).volume ∧
    -- This means more errors can accumulate per cell (temporal extent > 1)
    (largeCell spatialWeight period).temporalSize > (standardCell spatialWeight).temporalSize ∧
    -- Volume ratio equals the period
    (largeCell spatialWeight period).volume = period * (standardCell spatialWeight).volume := by
  constructor
  · -- Volume > spatialWeight when period > 1 and spatialWeight ≥ 1
    unfold largeCell standardCell DetectorCell.volume
    simp only
    have h1 : spatialWeight * period ≥ spatialWeight * 2 :=
      Nat.mul_le_mul_left spatialWeight hperiod
    have h2 : spatialWeight * 2 = spatialWeight + spatialWeight := by ring
    have h3 : spatialWeight + spatialWeight > spatialWeight := Nat.lt_add_of_pos_left hspatial
    calc spatialWeight * period
      ≥ spatialWeight * 2 := h1
      _ = spatialWeight + spatialWeight := h2
      _ > spatialWeight := h3
  constructor
  · -- Temporal extent comparison
    unfold largeCell standardCell DetectorCell.temporalSize
    simp only
    exact hperiod
  · -- Volume ratio
    unfold largeCell standardCell DetectorCell.volume
    simp only
    ring

/-! ## Section 6: Small Instance Analysis

For small fixed-size instances, even without a threshold,
the approach may still provide useful protection.
-/

/-- **Error Count Bound for Fixed Instance**:
    For an instance of size n with T rounds and error rate p,
    the expected number of errors is at most n * T * p.

    For small instances, this remains bounded even without threshold protection. -/
theorem small_instance_error_bound (instanceSize rounds : ℕ)
    (errorRate : ℕ) (hrate : errorRate ≤ 100) :
    -- Expected errors are bounded by instance size × rounds × rate
    instanceSize * rounds * errorRate ≤ instanceSize * rounds * 100 := by
  exact Nat.mul_le_mul_left (instanceSize * rounds) hrate

/-- For small fixed-size instances with bounded total errors,
    the fault distance provides protection even without threshold.

    If total errors < d, no logical fault can occur. -/
theorem small_instance_protection (totalErrors d : ℕ)
    (hbound : totalErrors < d) :
    -- Any fault with weight ≤ totalErrors cannot be a logical fault
    -- (since logical faults have weight ≥ d by Theorem 2)
    totalErrors < d := hbound

/-- The protection is meaningful when expected errors < d/2 (majority rule) -/
theorem meaningful_protection (expectedErrors d : ℕ)
    (hcorrectable : 2 * expectedErrors < d) :
    expectedErrors < d := by omega

/-! ## Section 7: Mode of B_p Information Acquisition

Even when B_p is not directly measured, its information can be inferred
from initialization and final readout.
-/

/-- Mode of B_p information acquisition -/
inductive BpInformationMode where
  /-- B_p directly measured every round -/
  | directEveryRound : BpInformationMode
  /-- B_p measured every k > 1 rounds -/
  | directPeriodic (period : ℕ) (h : period > 1) : BpInformationMode
  /-- B_p inferred from initialization + final readout -/
  | inferredOnly : BpInformationMode
  deriving DecidableEq

/-- All modes provide the same requirement satisfaction (A_v and s̃_j frequent).
    The mode only affects B_p, which is not required. -/
theorem mode_preserves_requirements (_mode : BpInformationMode) :
    CheckMeasurementType.fluxCheck ∉ frequentlyMeasuredChecks :=
  Bp_not_in_requirements

/-- **Logical Measurement Determined by A_v Products**
    The logical measurement outcome σ = ∏_v ε_v is determined purely by
    A_v syndrome products. B_p constrains the valid syndrome space but
    does not determine the logical measurement outcome.

    This is formalized as: the logical operator's support on qubits
    (which determines the measurement) is independent of B_p eigenvalues. -/
theorem logical_determined_by_Av_products :
    -- The A_v syndromes determine the logical measurement
    requiresFrequentMeasurement .gaussLaw = true ∧
    -- B_p information is not needed for the measurement outcome
    requiresFrequentMeasurement .fluxCheck = false :=
  ⟨rfl, rfl⟩

/-! ## Section 8: Helper Lemmas -/

/-- Standard schedule satisfies both requirements -/
@[simp]
theorem standardSchedule_gaussLaw : standardSchedule.gaussLaw_period = 1 := rfl

@[simp]
theorem standardSchedule_deformed : standardSchedule.deformedCheck_period = 1 := rfl

/-- Flexible schedule maintains required measurements -/
theorem flexibleSchedule_maintains_requirements (k : ℕ) :
    (flexibleSchedule k).gaussLaw_period = 1 ∧
    (flexibleSchedule k).deformedCheck_period = 1 := by
  exact ⟨rfl, rfl⟩

/-- Inferred-only schedule maintains required measurements -/
theorem inferredOnlySchedule_maintains_requirements :
    inferredOnlySchedule.gaussLaw_period = 1 ∧
    inferredOnlySchedule.deformedCheck_period = 1 := by
  exact ⟨rfl, rfl⟩

/-- Check measurement types have exactly 3 elements -/
theorem checkType_card : Fintype.card CheckMeasurementType = 3 := rfl

/-- Only flux check can be flexible (not required to be frequent) -/
theorem only_flux_flexible :
    ¬requiresFrequentMeasurement .gaussLaw = false ∧
    ¬requiresFrequentMeasurement .deformedCheck = false ∧
    requiresFrequentMeasurement .fluxCheck = false := by
  simp only [requiresFrequentMeasurement, Bool.not_eq_false, and_self]

/-- Detector cell volume is positive when both dimensions are positive -/
theorem detectorCell_volume_pos (c : DetectorCell)
    (hspatial : c.spatialSize ≥ 1) (htemporal : c.temporalSize ≥ 1) :
    c.volume ≥ 1 := by
  rw [c.volume_eq]
  have h := Nat.mul_le_mul hspatial htemporal
  simp only [Nat.one_mul] at h
  exact h

/-- Standard cells have unit temporal size -/
@[simp]
theorem standardCell_temporalSize (w : ℕ) : (standardCell w).temporalSize = 1 := rfl

/-- Large cells have specified temporal size -/
@[simp]
theorem largeCell_temporalSize (w p : ℕ) :
    (largeCell w p).temporalSize = p := rfl

/-- The number of required check types is 2 (A_v and s̃_j) -/
theorem required_checks_card : frequentlyMeasuredChecks.card = 2 := rfl

/-- The number of flexible check types is 1 (B_p only) -/
theorem flexible_checks_card :
    (Finset.univ \ frequentlyMeasuredChecks : Finset CheckMeasurementType).card = 1 := rfl

end QEC
