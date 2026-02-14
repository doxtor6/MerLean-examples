import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Definition 8: Detectors

## Statement
A **detector** is a collection of state initializations and measurements whose outcomes
satisfy a deterministic constraint in the absence of faults (Definition 7).

A detector is specified by a set of measurement labels such that the product of all
outcomes (in {+1, -1}) equals +1 when there are no faults. In ZMod 2 encoding
(0 ↔ +1, 1 ↔ -1), this means the sum of ideal outcomes over the detector's
measurements equals 0.

## Main Results
- `Detector`: A detector on measurement type M with ideal outcomes
- `Detector.detectorConstraint`: The sum of ideal outcomes over detector measurements is 0
- `Detector.isViolated`: Whether a set of time-faults causes the detector to fire
- `Detector.observedParity`: The observed parity of detector measurements under faults
- `repeatedMeasurementDetector`: Two consecutive measurements of the same check form a detector
- `initAndMeasureDetector`: Initialization + later measurement forms a detector

## Corollaries
- No-fault detectors have observed parity 0
- Violation depends only on which detector measurements are faulted
- Syndrome: the set of violated detectors
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {Q : Type*} {T : Type*} {M : Type*}

/-! ## Detector Definition -/

/-- A detector is a finite collection of measurement labels together with ideal outcomes,
    such that the sum (in ZMod 2) of the ideal outcomes over the detector's measurements
    is 0. In {+1, -1} encoding, this means the product of ideal outcomes equals +1.

    The type parameter M labels all measurements and state initializations in the
    procedure (per Definition 7, initializations are treated as measurements). -/
structure Detector (M : Type*) where
  /-- The finset of measurement labels comprising this detector. -/
  measurements : Finset M
  /-- The ideal outcome of each measurement (0 ↔ +1, 1 ↔ -1 in ZMod 2). -/
  idealOutcome : M → ZMod 2
  /-- The detector constraint: in the absence of faults, the sum of ideal outcomes
      over the detector's measurements is 0 in ZMod 2.
      Equivalently, the product of {+1, -1} outcomes equals +1. -/
  detectorConstraint : ∑ m ∈ measurements, idealOutcome m = 0

namespace Detector

variable [DecidableEq M] [DecidableEq (TimeFault M)]

/-! ## Observed parity and violation -/

/-- The observed parity of a detector under a set of time-faults.
    This is the sum (in ZMod 2) of observed outcomes over the detector's measurements.
    In {+1, -1} encoding, 0 means the product is +1, 1 means the product is -1. -/
def observedParity (D : Detector M) (faults : Finset (TimeFault M)) : ZMod 2 :=
  ∑ m ∈ D.measurements, observedOutcome D.idealOutcome faults m

/-- A detector is violated by a set of time-faults if the observed parity is 1
    (i.e., the product of observed outcomes is -1 instead of +1). -/
def isViolated (D : Detector M) (faults : Finset (TimeFault M)) : Prop :=
  D.observedParity faults = 1

/-- The flip parity: the sum in ZMod 2 of the indicator of faulted measurements
    in this detector. This equals the observed parity. -/
def flipParity (D : Detector M) (faults : Finset (TimeFault M)) : ZMod 2 :=
  ∑ m ∈ D.measurements, if (⟨m⟩ : TimeFault M) ∈ faults then 1 else 0

/-! ## Basic Properties -/

/-- In the absence of faults, the observed parity equals 0 (detector is not violated). -/
@[simp]
theorem observedParity_no_faults (D : Detector M) :
    D.observedParity ∅ = 0 := by
  unfold observedParity observedOutcome
  have : ∀ m ∈ D.measurements, (D.idealOutcome m +
      if (⟨m⟩ : TimeFault M) ∈ (∅ : Finset (TimeFault M)) then (1 : ZMod 2) else 0) =
      D.idealOutcome m := by
    intro m _
    simp [Finset.notMem_empty]
  rw [Finset.sum_congr rfl this]
  exact D.detectorConstraint

/-- In the absence of faults, no detector is violated. -/
theorem not_isViolated_no_faults (D : Detector M) :
    ¬D.isViolated ∅ := by
  unfold isViolated
  rw [observedParity_no_faults]
  exact zero_ne_one

/-- The observed parity equals the flip parity (number of faulted measurements mod 2).
    This is because the ideal outcomes cancel by the detector constraint. -/
theorem observedParity_eq_flipParity (D : Detector M) (faults : Finset (TimeFault M)) :
    D.observedParity faults = D.flipParity faults := by
  unfold observedParity flipParity observedOutcome
  rw [show ∑ m ∈ D.measurements, (D.idealOutcome m +
        if (⟨m⟩ : TimeFault M) ∈ faults then (1 : ZMod 2) else 0) =
      ∑ m ∈ D.measurements, D.idealOutcome m +
      ∑ m ∈ D.measurements, (if (⟨m⟩ : TimeFault M) ∈ faults then (1 : ZMod 2) else 0)
    from Finset.sum_add_distrib]
  rw [D.detectorConstraint, zero_add]

/-- A detector is violated iff the flip parity is 1. -/
theorem isViolated_iff_flipParity (D : Detector M) (faults : Finset (TimeFault M)) :
    D.isViolated faults ↔ D.flipParity faults = 1 := by
  unfold isViolated
  rw [observedParity_eq_flipParity]

/-- The flip parity with no faults is 0. -/
@[simp]
theorem flipParity_no_faults (D : Detector M) :
    D.flipParity ∅ = 0 := by
  unfold flipParity
  simp

/-! ## Violation depends only on fault-detector intersection -/

/-- The violation of a detector depends only on which of the detector's measurements
    appear in the fault set. -/
theorem isViolated_depends_on_intersection (D : Detector M) (faults₁ faults₂ : Finset (TimeFault M))
    (h : ∀ m ∈ D.measurements, ((⟨m⟩ : TimeFault M) ∈ faults₁ ↔ (⟨m⟩ : TimeFault M) ∈ faults₂)) :
    D.isViolated faults₁ ↔ D.isViolated faults₂ := by
  simp only [isViolated_iff_flipParity, flipParity]
  constructor <;> intro heq <;> {
    convert heq using 1
    apply Finset.sum_congr rfl
    intro m hm
    simp only [h m hm]
  }

/-- Violation is invariant if we add faults outside the detector. -/
theorem isViolated_of_superset_disjoint (D : Detector M) (faults extra : Finset (TimeFault M))
    (hdisj : ∀ m ∈ D.measurements, (⟨m⟩ : TimeFault M) ∉ extra) :
    D.isViolated (faults ∪ extra) ↔ D.isViolated faults := by
  apply isViolated_depends_on_intersection
  intro m hm
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h1 | h2
    · exact h1
    · exact absurd h2 (hdisj m hm)
  · intro h; exact Finset.mem_union_left _ h

end Detector

/-! ## Detector from a single measurement repeated twice

Example 1: Two consecutive measurements of the same stabilizer check s at times t and t+1
form a detector. If no faults occur, both give the same outcome, so their product is +1. -/

/-- Helper: in ZMod 2, a + a = 0. -/
private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 :=
  CharTwo.add_self_eq_zero x

/-- A repeated measurement detector: measuring the same check at two different times.
    Both measurements have the same ideal outcome, so in ZMod 2 they sum to 0. -/
def repeatedMeasurementDetector [DecidableEq M]
    (m₁ m₂ : M) (hne : m₁ ≠ m₂) (outcome : ZMod 2) : Detector M where
  measurements := {m₁, m₂}
  idealOutcome := fun m => if m = m₁ ∨ m = m₂ then outcome else 0
  detectorConstraint := by
    rw [Finset.sum_pair hne]
    simp only [eq_self_iff_true, true_or, or_true, ite_true]
    exact zmod2_add_self outcome

/-- An initialization-measurement detector: initializing a qubit and later measuring
    it in the same basis. Both give the same outcome (+1 for |0⟩ → Z-measurement),
    so the product is +1. The two labels m_init and m_meas represent the initialization
    (treated as a measurement per Def 7) and the actual measurement. -/
def initAndMeasureDetector [DecidableEq M]
    (m_init m_meas : M) (hne : m_init ≠ m_meas) (outcome : ZMod 2) : Detector M where
  measurements := {m_init, m_meas}
  idealOutcome := fun m => if m = m_init ∨ m = m_meas then outcome else 0
  detectorConstraint := by
    rw [Finset.sum_pair hne]
    simp only [eq_self_iff_true, true_or, or_true, ite_true]
    exact zmod2_add_self outcome

/-! ## Properties of example detectors -/

namespace Detector

variable [DecidableEq M] [DecidableEq (TimeFault M)]

/-- A repeated measurement detector is violated iff exactly one of the two measurements
    is faulted (i.e., the two outcomes disagree). -/
theorem repeatedMeasurement_violated_iff (m₁ m₂ : M) (hne : m₁ ≠ m₂) (outcome : ZMod 2)
    (faults : Finset (TimeFault M)) :
    (repeatedMeasurementDetector m₁ m₂ hne outcome).isViolated faults ↔
    Xor' ((⟨m₁⟩ : TimeFault M) ∈ faults) ((⟨m₂⟩ : TimeFault M) ∈ faults) := by
  rw [isViolated_iff_flipParity]
  unfold flipParity repeatedMeasurementDetector
  simp only
  rw [Finset.sum_pair hne]
  constructor
  · intro h
    unfold Xor'
    by_cases h1 : (⟨m₁⟩ : TimeFault M) ∈ faults <;>
    by_cases h2 : (⟨m₂⟩ : TimeFault M) ∈ faults <;>
    simp_all
  · intro h
    unfold Xor' at h
    by_cases h1 : (⟨m₁⟩ : TimeFault M) ∈ faults <;>
    by_cases h2 : (⟨m₂⟩ : TimeFault M) ∈ faults <;>
    simp_all

/-! ## Syndrome: the set of violated detectors -/

/-- The syndrome of a set of time-faults with respect to a collection of detectors:
    the set of detector indices that are violated. -/
def syndrome {I : Type*} [DecidableEq I] [Fintype I]
    (detectors : I → Detector M)
    (faults : Finset (TimeFault M)) : Finset I :=
  Finset.univ.filter (fun i => (detectors i).observedParity faults = 1)

/-- A detector index is in the syndrome iff the detector is violated. -/
@[simp]
theorem mem_syndrome_iff {I : Type*} [DecidableEq I] [Fintype I]
    (detectors : I → Detector M)
    (faults : Finset (TimeFault M))
    (i : I) :
    i ∈ syndrome detectors faults ↔ (detectors i).isViolated faults := by
  simp [syndrome, isViolated]

/-- The syndrome is empty when there are no faults. -/
@[simp]
theorem syndrome_empty_no_faults {I : Type*} [DecidableEq I] [Fintype I]
    (detectors : I → Detector M) :
    syndrome detectors (∅ : Finset (TimeFault M)) = ∅ := by
  simp only [syndrome, Finset.filter_eq_empty_iff]
  intro i _
  rw [(detectors i).observedParity_no_faults]
  exact zero_ne_one

/-! ## Disjoint union of detectors -/

/-- The union of two detectors with disjoint measurement sets forms a new detector,
    provided the ideal outcomes agree on any common measurements. -/
def disjointUnion
    (D₁ D₂ : Detector M)
    (hdisj : Disjoint D₁.measurements D₂.measurements)
    (hsame : ∀ m, D₁.idealOutcome m = D₂.idealOutcome m) :
    Detector M where
  measurements := D₁.measurements ∪ D₂.measurements
  idealOutcome := D₁.idealOutcome
  detectorConstraint := by
    rw [Finset.sum_union hdisj]
    have : ∑ m ∈ D₂.measurements, D₁.idealOutcome m =
           ∑ m ∈ D₂.measurements, D₂.idealOutcome m := by
      apply Finset.sum_congr rfl
      intro m _; exact hsame m
    rw [this, D₁.detectorConstraint, D₂.detectorConstraint, add_zero]

/-! ## Empty and single-measurement detectors -/

/-- The empty detector (no measurements) is trivially satisfied. -/
def emptyDetector (idealOutcome : M → ZMod 2) : Detector M where
  measurements := ∅
  idealOutcome := idealOutcome
  detectorConstraint := by simp

/-- The empty detector is never violated. -/
@[simp]
theorem emptyDetector_not_violated (idealOutcome : M → ZMod 2)
    (faults : Finset (TimeFault M)) :
    ¬(emptyDetector idealOutcome : Detector M).isViolated faults := by
  unfold isViolated observedParity emptyDetector
  simp only [Finset.sum_empty]
  exact zero_ne_one

/-- A single-measurement detector requires the ideal outcome to be 0
    (i.e., the measurement gives +1 in the absence of faults). -/
def singleMeasurementDetector (m : M) : Detector M where
  measurements := {m}
  idealOutcome := fun _ => 0
  detectorConstraint := by simp

/-- A single-measurement detector with outcome 0 is violated iff the measurement is faulted. -/
theorem singleMeasurement_violated_iff (m : M) (faults : Finset (TimeFault M)) :
    (singleMeasurementDetector m).isViolated faults ↔
    (⟨m⟩ : TimeFault M) ∈ faults := by
  rw [isViolated_iff_flipParity]
  unfold flipParity singleMeasurementDetector
  simp only [Finset.sum_singleton]
  constructor
  · intro h
    by_contra hm
    simp [hm] at h
  · intro h; simp [h]

/-! ## Detector violation from spacetime faults -/

/-- The violation status of a detector under a spacetime fault is determined
    by the time-fault component. Space-faults change the quantum state but the
    detector constraint is purely about measurement outcome flips. -/
theorem isViolated_spacetimeFault
    [DecidableEq Q] [DecidableEq T]
    [DecidableEq (SpaceFault Q T)]
    (D : Detector M) (F : SpacetimeFault Q T M) :
    D.isViolated F.timeFaults ↔ D.observedParity F.timeFaults = 1 := by
  rfl

/-! ## Detector weight -/

/-- The weight (number of measurements) in a detector. -/
def detectorWeight (D : Detector M) : ℕ := D.measurements.card

/-- The repeated measurement detector has weight 2. -/
theorem repeatedMeasurement_weight (m₁ m₂ : M) (hne : m₁ ≠ m₂) (outcome : ZMod 2) :
    (repeatedMeasurementDetector m₁ m₂ hne outcome).detectorWeight = 2 := by
  unfold detectorWeight repeatedMeasurementDetector
  simp [Finset.card_pair hne]

/-- The init-and-measure detector has weight 2. -/
theorem initAndMeasure_weight (m_init m_meas : M) (hne : m_init ≠ m_meas) (outcome : ZMod 2) :
    (initAndMeasureDetector m_init m_meas hne outcome).detectorWeight = 2 := by
  unfold detectorWeight initAndMeasureDetector
  simp [Finset.card_pair hne]

/-- The empty detector has weight 0. -/
@[simp]
theorem emptyDetector_weight (idealOutcome : M → ZMod 2) :
    (emptyDetector idealOutcome : Detector M).detectorWeight = 0 := by
  unfold detectorWeight emptyDetector; simp

/-- The single-measurement detector has weight 1. -/
theorem singleMeasurement_weight (m : M) :
    (singleMeasurementDetector m : Detector M).detectorWeight = 1 := by
  unfold detectorWeight singleMeasurementDetector; simp

end Detector
