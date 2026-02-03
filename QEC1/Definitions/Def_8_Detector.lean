import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Order.SymmDiff

import QEC1.Definitions.Def_7_SpaceAndTimeFaults

/-!
# Def_8: Detector

## Statement
A **detector** is a collection of state initializations and measurement events that yield a
deterministic result in the absence of faults. Specifically, a detector is a subset D of
initialization events and measurement events such that:

1. In a fault-free execution, the product of all measurement outcomes in D (treating +1 outcomes
   as 0 and −1 outcomes as 1 modulo 2) combined with initialization parities equals a fixed value
   (conventionally +1 or equivalently 0 mod 2).

2. This determinism holds regardless of the quantum state being processed (for measurements of
   stabilizer generators) or is guaranteed by the initialization (for measurements immediately
   following initialization).

Intuitively, a detector is a parity check on measurement outcomes that should always yield +1 if
no errors occurred. A fault that causes a detector to report −1 instead is said to **violate**
that detector.

## Main Definitions
- `MeasurementOutcome` : The outcome of a quantum measurement (+1 or -1, represented as ZMod 2)
- `InitializationEvent` : A state initialization event (qubit and time)
- `MeasurementEvent` : A measurement event (measurement index and time)
- `DetectorEvent` : Either an initialization or measurement event
- `Detector` : A set of events with deterministic fault-free parity
- `Detector.expectedParity` : The expected parity (0 for +1 outcome, 1 for -1)
- `Detector.observedParity` : The observed parity given measurement outcomes
- `Detector.isViolated` : Whether a detector reports an unexpected value

## Key Properties
- `Detector.satisfied_or_violated` : A detector is either satisfied or violated
- `Detector.satisfied_iff_not_violated` : A detector is satisfied iff not violated
- `Detector.empty_isSatisfied` : Empty detector always has parity 0
-/

open Finset symmDiff

set_option linter.unusedSectionVars false

/-! ## Measurement Outcomes

Measurement outcomes in quantum mechanics are typically ±1 eigenvalues.
We represent these mod 2: +1 → 0, -1 → 1.
This convention means XOR (addition mod 2) computes product parity correctly:
- +1 × +1 = +1 → 0 + 0 = 0
- +1 × -1 = -1 → 0 + 1 = 1
- -1 × +1 = -1 → 1 + 0 = 1
- -1 × -1 = +1 → 1 + 1 = 0
-/

/-- A measurement outcome represented mod 2: 0 for +1, 1 for -1 -/
abbrev MeasurementOutcome := ZMod 2

namespace MeasurementOutcome

/-- The +1 outcome (no error detected) -/
def plusOne : MeasurementOutcome := 0

/-- The -1 outcome (error detected) -/
def minusOne : MeasurementOutcome := 1

@[simp] lemma plusOne_val : plusOne = 0 := rfl
@[simp] lemma minusOne_val : minusOne = 1 := rfl

/-- Convert from Bool: false → +1 (0), true → -1 (1) -/
def fromBool : Bool → MeasurementOutcome
  | false => plusOne
  | true => minusOne

/-- Convert to Bool: 0 → false (+1), 1 → true (-1) -/
def toBool (m : MeasurementOutcome) : Bool := m ≠ 0

@[simp] lemma fromBool_false : fromBool false = plusOne := rfl
@[simp] lemma fromBool_true : fromBool true = minusOne := rfl

@[simp] lemma toBool_plusOne : toBool plusOne = false := by decide
@[simp] lemma toBool_minusOne : toBool minusOne = true := by decide

/-- Product of outcomes is addition mod 2 -/
def product (m₁ m₂ : MeasurementOutcome) : MeasurementOutcome := m₁ + m₂

@[simp] lemma product_plusOne_plusOne : product plusOne plusOne = plusOne := by decide
@[simp] lemma product_plusOne_minusOne : product plusOne minusOne = minusOne := by decide
@[simp] lemma product_minusOne_plusOne : product minusOne plusOne = minusOne := by decide
@[simp] lemma product_minusOne_minusOne : product minusOne minusOne = plusOne := by decide

end MeasurementOutcome

/-! ## Events: Initialization and Measurement

A detector monitors both initialization events (where qubits are prepared in known states)
and measurement events (where observables are measured). -/

/-- An initialization event: preparing a qubit at a specific time -/
structure InitializationEvent (V E : Type*) where
  /-- The qubit being initialized -/
  qubit : QubitLoc V E
  /-- The time of initialization -/
  time : TimeStep
  /-- The expected parity of this initialization (0 for standard basis state) -/
  expectedParity : ZMod 2
  deriving DecidableEq

/-- A measurement event: measuring an observable at a specific time -/
structure MeasurementEvent (M : Type*) where
  /-- The measurement index (which check/observable is measured) -/
  measurement : M
  /-- The time of measurement -/
  time : TimeStep
  deriving DecidableEq

namespace InitializationEvent

variable {V E : Type*}

/-- Create an initialization event with +1 expected outcome -/
def standard (q : QubitLoc V E) (t : TimeStep) : InitializationEvent V E :=
  ⟨q, t, 0⟩

@[simp] lemma standard_qubit (q : QubitLoc V E) (t : TimeStep) :
    (standard q t).qubit = q := rfl

@[simp] lemma standard_time (q : QubitLoc V E) (t : TimeStep) :
    (standard q t).time = t := rfl

@[simp] lemma standard_expectedParity (q : QubitLoc V E) (t : TimeStep) :
    (standard q t).expectedParity = 0 := rfl

end InitializationEvent

namespace MeasurementEvent

variable {M : Type*}

/-- Get the time of a measurement event -/
@[simp] lemma measurement_accessor (m : M) (t : TimeStep) :
    (⟨m, t⟩ : MeasurementEvent M).measurement = m := rfl

@[simp] lemma time_accessor (m : M) (t : TimeStep) :
    (⟨m, t⟩ : MeasurementEvent M).time = t := rfl

end MeasurementEvent

/-! ## Detector Events

A detector event is either an initialization or a measurement. -/

/-- A detector event: either an initialization or a measurement -/
inductive DetectorEvent (V E M : Type*) where
  /-- An initialization event -/
  | init : InitializationEvent V E → DetectorEvent V E M
  /-- A measurement event -/
  | meas : MeasurementEvent M → DetectorEvent V E M
  deriving DecidableEq

namespace DetectorEvent

variable {V E M : Type*}

/-- Check if this is an initialization event -/
def isInit : DetectorEvent V E M → Bool
  | init _ => true
  | meas _ => false

/-- Check if this is a measurement event -/
def isMeas : DetectorEvent V E M → Bool
  | init _ => false
  | meas _ => true

@[simp] lemma isInit_init (e : InitializationEvent V E) :
    (init e : DetectorEvent V E M).isInit = true := rfl

@[simp] lemma isInit_meas (e : MeasurementEvent M) :
    (meas e : DetectorEvent V E M).isInit = false := rfl

@[simp] lemma isMeas_init (e : InitializationEvent V E) :
    (init e : DetectorEvent V E M).isMeas = false := rfl

@[simp] lemma isMeas_meas (e : MeasurementEvent M) :
    (meas e : DetectorEvent V E M).isMeas = true := rfl

/-- Get the time of a detector event -/
def time : DetectorEvent V E M → TimeStep
  | init e => e.time
  | meas e => e.time

@[simp] lemma time_init (e : InitializationEvent V E) :
    (init e : DetectorEvent V E M).time = e.time := rfl

@[simp] lemma time_meas (e : MeasurementEvent M) :
    (meas e : DetectorEvent V E M).time = e.time := rfl

/-- Get the initialization event if this is one -/
def getInit : DetectorEvent V E M → Option (InitializationEvent V E)
  | init e => some e
  | meas _ => none

/-- Get the measurement event if this is one -/
def getMeas : DetectorEvent V E M → Option (MeasurementEvent M)
  | init _ => none
  | meas e => some e

/-- getInit is injective on init events -/
lemma getInit_injective : ∀ a b : DetectorEvent V E M,
    a.getInit.isSome → b.getInit.isSome → a.getInit = b.getInit → a = b := by
  intro a b ha hb hab
  match a, b with
  | init ea, init eb =>
    simp only [getInit, Option.some.injEq] at hab
    rw [hab]
  | init _, meas _ => simp [getInit] at hb
  | meas _, init _ => simp [getInit] at ha
  | meas _, meas _ => simp [getInit] at ha

/-- getMeas is injective on meas events -/
lemma getMeas_injective : ∀ a b : DetectorEvent V E M,
    a.getMeas.isSome → b.getMeas.isSome → a.getMeas = b.getMeas → a = b := by
  intro a b ha hb hab
  match a, b with
  | meas ea, meas eb =>
    simp only [getMeas, Option.some.injEq] at hab
    rw [hab]
  | init _, meas _ => simp [getMeas] at ha
  | meas _, init _ => simp [getMeas] at hb
  | init _, init _ => simp [getMeas] at ha

end DetectorEvent

/-! ## Detectors

A detector is a set of events that together form a parity check with deterministic
outcome in fault-free execution. -/

/-- An outcome assignment: provides measurement outcomes for all measurements at all times -/
abbrev OutcomeAssignment (M : Type*) := M → TimeStep → MeasurementOutcome

/-- An initialization fault record: whether each initialization is faulty -/
abbrev InitFaultRecord (V E : Type*) := QubitLoc V E → TimeStep → Bool

/-- A detector: a set of events with an expected fault-free parity.

    The key property is that in fault-free execution, the XOR of all measurement outcomes
    in the detector (combined with initialization parities) equals the expected value.
    When faults occur, the observed parity may differ from expected. -/
structure Detector (V E M : Type*) [DecidableEq V] [DecidableEq E] [DecidableEq M] where
  /-- The set of events in this detector -/
  events : Finset (DetectorEvent V E M)
  /-- The expected parity in fault-free execution (0 for +1, 1 for -1) -/
  expectedParity : ZMod 2

instance [DecidableEq V] [DecidableEq E] [DecidableEq M] : DecidableEq (Detector V E M) :=
  fun d1 d2 =>
    if h : d1.events = d2.events ∧ d1.expectedParity = d2.expectedParity then
      isTrue (by cases d1; cases d2; simp_all)
    else
      isFalse (by intro heq; simp_all)

namespace Detector

variable {V E M : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq M]

/-- Get all initialization events in a detector -/
def initEvents (D : Detector V E M) : Finset (InitializationEvent V E) :=
  D.events.filterMap DetectorEvent.getInit (by
    intro a b c ha hb
    simp only [Option.mem_def] at ha hb
    exact DetectorEvent.getInit_injective a b
      (by rw [ha]; exact Option.isSome_some)
      (by rw [hb]; exact Option.isSome_some)
      (by rw [ha, hb]))

/-- Get all measurement events in a detector -/
def measEvents (D : Detector V E M) : Finset (MeasurementEvent M) :=
  D.events.filterMap DetectorEvent.getMeas (by
    intro a b c ha hb
    simp only [Option.mem_def] at ha hb
    exact DetectorEvent.getMeas_injective a b
      (by rw [ha]; exact Option.isSome_some)
      (by rw [hb]; exact Option.isSome_some)
      (by rw [ha, hb]))

/-- The contribution from initialization events: sum of their expected parities -/
def initParity (D : Detector V E M) : ZMod 2 :=
  D.initEvents.sum (fun e => e.expectedParity)

/-- The observed parity: sum of measurement outcomes plus initialization parities -/
def observedParity (D : Detector V E M) (outcomes : OutcomeAssignment M) : ZMod 2 :=
  D.initParity + D.measEvents.sum (fun e => outcomes e.measurement e.time)

/-- A detector is violated if observed parity differs from expected -/
def isViolated (D : Detector V E M) (outcomes : OutcomeAssignment M) : Prop :=
  D.observedParity outcomes ≠ D.expectedParity

/-- A detector is satisfied if observed parity equals expected -/
def isSatisfied (D : Detector V E M) (outcomes : OutcomeAssignment M) : Prop :=
  D.observedParity outcomes = D.expectedParity

instance decIsViolated (D : Detector V E M) (outcomes : OutcomeAssignment M) :
    Decidable (D.isViolated outcomes) :=
  inferInstanceAs (Decidable (_ ≠ _))

instance decIsSatisfied (D : Detector V E M) (outcomes : OutcomeAssignment M) :
    Decidable (D.isSatisfied outcomes) :=
  inferInstanceAs (Decidable (_ = _))

/-- A detector is either satisfied or violated -/
theorem satisfied_or_violated (D : Detector V E M) (outcomes : OutcomeAssignment M) :
    D.isSatisfied outcomes ∨ D.isViolated outcomes := by
  unfold isSatisfied isViolated
  exact eq_or_ne _ _

/-- Satisfied and violated are mutually exclusive -/
theorem satisfied_iff_not_violated (D : Detector V E M) (outcomes : OutcomeAssignment M) :
    D.isSatisfied outcomes ↔ ¬D.isViolated outcomes := by
  unfold isSatisfied isViolated
  constructor
  · intro h hne; exact hne h
  · intro h; by_contra hne; exact h hne

/-! ## Empty Detector -/

/-- The empty detector with expected parity 0 -/
def empty : Detector V E M where
  events := ∅
  expectedParity := 0

@[simp] lemma empty_events : (empty : Detector V E M).events = ∅ := rfl
@[simp] lemma empty_expectedParity : (empty : Detector V E M).expectedParity = 0 := rfl

@[simp] lemma empty_initEvents : (empty : Detector V E M).initEvents = ∅ := by
  simp only [initEvents, empty_events, Finset.filterMap_empty]

@[simp] lemma empty_measEvents : (empty : Detector V E M).measEvents = ∅ := by
  simp only [measEvents, empty_events, Finset.filterMap_empty]

@[simp] lemma empty_initParity : (empty : Detector V E M).initParity = 0 := by
  simp [initParity]

@[simp] lemma empty_observedParity (outcomes : OutcomeAssignment M) :
    (empty : Detector V E M).observedParity outcomes = 0 := by
  simp [observedParity]

/-- The empty detector is always satisfied -/
@[simp] theorem empty_isSatisfied (outcomes : OutcomeAssignment M) :
    (empty : Detector V E M).isSatisfied outcomes := by
  simp [isSatisfied]

/-- The empty detector is never violated -/
@[simp] theorem empty_not_isViolated (outcomes : OutcomeAssignment M) :
    ¬(empty : Detector V E M).isViolated outcomes := by
  simp [isViolated]

/-! ## Single-Event Detectors -/

/-- A detector consisting of a single initialization event -/
def singleInit (e : InitializationEvent V E) : Detector V E M where
  events := {DetectorEvent.init e}
  expectedParity := e.expectedParity

/-- A detector consisting of a single measurement event -/
def singleMeas (e : MeasurementEvent M) (expectedOutcome : ZMod 2 := 0) : Detector V E M where
  events := {DetectorEvent.meas e}
  expectedParity := expectedOutcome

@[simp] lemma singleInit_events (e : InitializationEvent V E) :
    (singleInit e : Detector V E M).events = {DetectorEvent.init e} := rfl

@[simp] lemma singleMeas_events (e : MeasurementEvent M) (p : ZMod 2) :
    (singleMeas e p : Detector V E M).events = {DetectorEvent.meas e} := rfl

/-! ## Combining Detectors -/

/-- Combine two detectors by taking symmetric difference of events and XOR of parities.
    This corresponds to multiplying the parity checks. -/
def combine (D₁ D₂ : Detector V E M) : Detector V E M where
  events := D₁.events ∆ D₂.events
  expectedParity := D₁.expectedParity + D₂.expectedParity

/-- Notation for detector combination -/
instance : Add (Detector V E M) where
  add := combine

@[simp] lemma combine_events (D₁ D₂ : Detector V E M) :
    (combine D₁ D₂).events = D₁.events ∆ D₂.events := rfl

@[simp] lemma combine_expectedParity (D₁ D₂ : Detector V E M) :
    (combine D₁ D₂).expectedParity = D₁.expectedParity + D₂.expectedParity := rfl

/-- Two detectors are equal iff their components are equal -/
theorem ext_iff {D₁ D₂ : Detector V E M} :
    D₁ = D₂ ↔ D₁.events = D₂.events ∧ D₁.expectedParity = D₂.expectedParity := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · intro ⟨h_events, h_parity⟩; cases D₁; cases D₂; simp only [mk.injEq] at *; exact ⟨h_events, h_parity⟩

/-- Adding empty detector does nothing (from the left) -/
theorem empty_combine (D : Detector V E M) : combine empty D = D := by
  rw [ext_iff]
  constructor
  · simp only [combine_events, empty_events]
    rw [← Finset.bot_eq_empty, bot_symmDiff]
  · simp only [combine_expectedParity, empty_expectedParity, zero_add]

/-- Adding empty detector does nothing (from the right) -/
theorem combine_empty (D : Detector V E M) : combine D empty = D := by
  rw [ext_iff]
  constructor
  · simp only [combine_events, empty_events]
    rw [← Finset.bot_eq_empty, symmDiff_bot]
  · simp only [combine_expectedParity, empty_expectedParity, add_zero]

/-- Combining a detector with itself gives empty -/
theorem combine_self (D : Detector V E M) : combine D D = empty := by
  rw [ext_iff]
  constructor
  · simp only [combine_events, empty_events]
    exact symmDiff_self D.events
  · simp only [combine_expectedParity, CharTwo.add_self_eq_zero, empty_expectedParity]

/-! ## Fault-Free Execution

The key property of detectors is determinism in fault-free execution. -/

/-- Fault-free outcomes: all measurements return their expected values.
    For stabilizer measurements, this means +1 (represented as 0).
    This function represents the outcomes in an ideal fault-free execution. -/
def faultFreeOutcomes (expectedMeasOutcome : M → TimeStep → ZMod 2) :
    OutcomeAssignment M :=
  expectedMeasOutcome

/-- A detector with consistent expected outcomes is satisfied in fault-free execution.
    This captures the defining property of detectors: determinism without faults. -/
theorem faultFree_isSatisfied (D : Detector V E M)
    (expectedMeasOutcome : M → TimeStep → ZMod 2)
    (h_consistent : D.initParity + D.measEvents.sum (fun e => expectedMeasOutcome e.measurement e.time)
                    = D.expectedParity) :
    D.isSatisfied (faultFreeOutcomes expectedMeasOutcome) := by
  unfold isSatisfied observedParity faultFreeOutcomes
  exact h_consistent

/-! ## Effect of Faults on Detectors

Faults can flip measurement outcomes, causing detectors to be violated. -/

/-- Apply a time fault to outcomes: if the fault is active, flip the outcome -/
def applyTimeFault (outcomes : OutcomeAssignment M) (f : TimeFault M) :
    OutcomeAssignment M :=
  fun m t => if m = f.measurement ∧ t = f.time ∧ f.isFlipped
             then outcomes m t + 1
             else outcomes m t

/-- A single time fault at a measurement in the detector flips its contribution -/
lemma applyTimeFault_flips (outcomes : OutcomeAssignment M) (f : TimeFault M)
    (e : MeasurementEvent M) (hf : f.isFlipped = true) (he : e.measurement = f.measurement)
    (ht : e.time = f.time) :
    applyTimeFault outcomes f e.measurement e.time = outcomes e.measurement e.time + 1 := by
  simp [applyTimeFault, he, ht, hf]

/-- A time fault outside the detector doesn't affect outcomes for events not at that location -/
lemma applyTimeFault_unchanged (outcomes : OutcomeAssignment M) (f : TimeFault M)
    (m : M) (t : TimeStep) (h : m ≠ f.measurement ∨ t ≠ f.time) :
    applyTimeFault outcomes f m t = outcomes m t := by
  simp only [applyTimeFault]
  split_ifs with hcond
  · obtain ⟨h1, h2, _⟩ := hcond
    cases h with
    | inl hn => exact absurd h1 hn
    | inr hn => exact absurd h2 hn
  · rfl

/-! ## Detector Violation Analysis

We characterize when faults violate detectors. -/

/-- The syndrome of a fault on a detector: how much the parity is shifted -/
def faultSyndrome (D : Detector V E M)
    (faultedMeas : Finset (MeasurementEvent M)) : ZMod 2 :=
  (D.measEvents ∩ faultedMeas).card

/-- A fault violates a detector iff the syndrome is odd (1 mod 2) -/
theorem isViolated_iff_odd_syndrome (D : Detector V E M)
    (outcomes : OutcomeAssignment M)
    (faultedMeas : Finset (MeasurementEvent M))
    (h_outcomes : ∀ e ∈ D.measEvents, e ∈ faultedMeas →
        outcomes e.measurement e.time = 1)
    (h_no_fault : ∀ e ∈ D.measEvents, e ∉ faultedMeas →
        outcomes e.measurement e.time = 0)
    (h_init : D.initParity = 0)
    (h_expected : D.expectedParity = 0) :
    D.isViolated outcomes ↔ D.faultSyndrome faultedMeas = 1 := by
  unfold isViolated observedParity faultSyndrome
  simp only [h_init, h_expected, zero_add, ne_eq]
  -- First establish that the sum equals the count of faulted measurements
  have sum_eq : D.measEvents.sum (fun e => outcomes e.measurement e.time) =
                (D.measEvents ∩ faultedMeas).card := by
    rw [← Finset.sum_filter_add_sum_filter_not D.measEvents (· ∈ faultedMeas)]
    have h1 : (D.measEvents.filter (· ∈ faultedMeas)).sum
                (fun e => outcomes e.measurement e.time) =
              (D.measEvents.filter (· ∈ faultedMeas)).card := by
      trans (D.measEvents.filter (· ∈ faultedMeas)).sum (fun _ => (1 : ZMod 2))
      · apply Finset.sum_congr rfl
        intro e he
        simp only [Finset.mem_filter] at he
        exact h_outcomes e he.1 he.2
      · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : (D.measEvents.filter (· ∉ faultedMeas)).sum
                (fun e => outcomes e.measurement e.time) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      simp only [Finset.mem_filter] at he
      exact h_no_fault e he.1 he.2
    rw [h1, h2, add_zero]
    congr 1
  rw [sum_eq]
  -- Now the equivalence is about when a nat cast to ZMod 2 is 0 vs 1
  -- In ZMod 2, every element is either 0 or 1
  have zmod2_dichotomy : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by
    fin_cases x <;> simp
  constructor
  · intro h
    cases zmod2_dichotomy ((D.measEvents ∩ faultedMeas).card : ZMod 2) with
    | inl h0 => exact absurd h0 h
    | inr h1 => exact h1
  · intro h
    rw [h]
    decide

end Detector

/-! ## Detector Collection

A fault-tolerant procedure typically has multiple detectors. -/

/-- A detector collection: a set of detectors for a fault-tolerant procedure -/
structure DetectorCollection (V E M : Type*) [DecidableEq V] [DecidableEq E] [DecidableEq M] where
  /-- The set of detectors -/
  detectors : Finset (Detector V E M)

namespace DetectorCollection

variable {V E M : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq M]

/-- The syndrome: which detectors are violated by given outcomes -/
def syndrome (DC : DetectorCollection V E M) (outcomes : OutcomeAssignment M) :
    Finset (Detector V E M) :=
  DC.detectors.filter (fun D => D.isViolated outcomes)

/-- Count of violated detectors -/
def violatedCount (DC : DetectorCollection V E M) (outcomes : OutcomeAssignment M) : ℕ :=
  (DC.syndrome outcomes).card

/-- All detectors are satisfied (syndrome is empty) -/
def allSatisfied (DC : DetectorCollection V E M) (outcomes : OutcomeAssignment M) : Prop :=
  DC.syndrome outcomes = ∅

@[simp] lemma allSatisfied_iff (DC : DetectorCollection V E M) (outcomes : OutcomeAssignment M) :
    DC.allSatisfied outcomes ↔ ∀ D ∈ DC.detectors, D.isSatisfied outcomes := by
  unfold allSatisfied syndrome
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h D hD
    rw [Detector.satisfied_iff_not_violated]
    exact h hD
  · intro h D hD
    rw [← Detector.satisfied_iff_not_violated]
    exact h D hD

/-- Empty collection has all detectors satisfied -/
@[simp] theorem empty_allSatisfied (outcomes : OutcomeAssignment M) :
    (⟨∅⟩ : DetectorCollection V E M).allSatisfied outcomes := by
  simp [allSatisfied, syndrome]

end DetectorCollection

/-! ## Summary

This formalization captures the detector concept from fault-tolerant quantum error correction:

1. **Measurement Outcomes**: Represented mod 2 (0 for +1, 1 for -1), with XOR computing
   product parity.

2. **Events**: Either initialization events (preparing qubits) or measurement events
   (measuring observables).

3. **Detectors**: Sets of events with an expected fault-free parity. The key property is
   that in fault-free execution, the XOR of all measurement outcomes (plus initialization
   parities) equals the expected value.

4. **Violation**: A detector is violated when the observed parity differs from expected.
   This indicates that a fault has occurred.

5. **Fault Analysis**: The syndrome of a fault on a detector counts (mod 2) how many
   faulted measurements are in the detector. A detector is violated iff this count is odd.

Key properties proven:
- Detectors are either satisfied or violated (exclusive)
- Empty detector is always satisfied
- Combining detectors XORs their events and parities
- Self-combination gives the empty detector
- Fault-free execution satisfies consistent detectors
- Violation occurs iff the fault syndrome is odd
-/
