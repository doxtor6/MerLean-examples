import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

import QEC1.Definitions.Def_7_SpaceAndTimeFaults

/-!
# Def_12: Time Step Convention

## Statement
We use a half-integer time step convention for the fault-tolerant gauging measurement procedure:

**Integer time steps** $t = 0, 1, 2, \ldots$: Associated with qubit states and Pauli space-errors.
A Pauli error 'at time $t$' affects the state between measurement rounds at times $t - \frac{1}{2}$
and $t + \frac{1}{2}$.

**Half-integer time steps** $t + \frac{1}{2}$: Associated with measurements and measurement errors.
A measurement 'at time $t + \frac{1}{2}$' occurs between qubit states at times $t$ and $t + 1$.

**Key time points**:
- $t_0$: Start of the procedure
- $t_i$: Time of the initial gauging code deformation (edge qubit initialization and first $A_v$
  measurements at $t_i - \frac{1}{2}$ and $t_i + \frac{1}{2}$)
- $t_o$: Time of the final ungauging code deformation (last $A_v$ measurements and edge qubit
  readout at $t_o - \frac{1}{2}$ and $t_o + \frac{1}{2}$)

## Main Definitions
- `HalfIntegerTime` : Represents both integer and half-integer time steps
- `IntegerTimeStep` : Integer times associated with qubit states
- `HalfIntegerTimeStep` : Half-integer times associated with measurements
- `TimeStepConvention` : The convention relating integer/half-integer times

## Key Properties
- `integerTime_isQubitStateTime` : Integer times are for qubit states
- `halfIntegerTime_isMeasurementTime` : Half-integer times are for measurements
- `measurement_between_states` : Measurement at t+1/2 is between states at t and t+1
- `error_between_measurements` : Error at t is between measurements at t-1/2 and t+1/2
-/

set_option linter.unusedSectionVars false

/-! ## Half-Integer Time Representation

We represent time as either an integer (for qubit states) or a half-integer (for measurements).
A half-integer n + 1/2 is represented by storing the integer n.

We use ℤ to allow negative times for generality (though in practice we mostly use t ≥ 0). -/

/-- A half-integer time representation.
    - `integer n` represents the integer time step n
    - `halfInteger n` represents the half-integer time step n + 1/2 -/
inductive HalfIntegerTime : Type
  | integer : ℤ → HalfIntegerTime
  | halfInteger : ℤ → HalfIntegerTime
  deriving DecidableEq, Repr

namespace HalfIntegerTime

/-- Convert to a rational number for comparison -/
def toRat : HalfIntegerTime → ℚ
  | integer n => n
  | halfInteger n => n + 1/2

/-- Check if this is an integer time -/
def isInteger : HalfIntegerTime → Bool
  | integer _ => true
  | halfInteger _ => false

/-- Check if this is a half-integer time -/
def isHalfInteger : HalfIntegerTime → Bool
  | integer _ => false
  | halfInteger _ => true

@[simp] lemma isInteger_integer (n : ℤ) : (integer n).isInteger = true := rfl
@[simp] lemma isInteger_halfInteger (n : ℤ) : (halfInteger n).isInteger = false := rfl
@[simp] lemma isHalfInteger_integer (n : ℤ) : (integer n).isHalfInteger = false := rfl
@[simp] lemma isHalfInteger_halfInteger (n : ℤ) : (halfInteger n).isHalfInteger = true := rfl

/-- Get the integer part (floor) -/
def floor : HalfIntegerTime → ℤ
  | integer n => n
  | halfInteger n => n

/-- Get the integer part rounded up (ceiling) -/
def ceil : HalfIntegerTime → ℤ
  | integer n => n
  | halfInteger n => n + 1

@[simp] lemma floor_integer (n : ℤ) : (integer n).floor = n := rfl
@[simp] lemma floor_halfInteger (n : ℤ) : (halfInteger n).floor = n := rfl
@[simp] lemma ceil_integer (n : ℤ) : (integer n).ceil = n := rfl
@[simp] lemma ceil_halfInteger (n : ℤ) : (halfInteger n).ceil = n + 1 := rfl

/-- Linear ordering on half-integer times -/
instance : LE HalfIntegerTime where
  le t₁ t₂ := t₁.toRat ≤ t₂.toRat

instance : LT HalfIntegerTime where
  lt t₁ t₂ := t₁.toRat < t₂.toRat

instance : DecidableRel (· ≤ · : HalfIntegerTime → HalfIntegerTime → Prop) :=
  fun t₁ t₂ => inferInstanceAs (Decidable (t₁.toRat ≤ t₂.toRat))

instance : DecidableRel (· < · : HalfIntegerTime → HalfIntegerTime → Prop) :=
  fun t₁ t₂ => inferInstanceAs (Decidable (t₁.toRat < t₂.toRat))

/-- Integer time n comes before half-integer time n + 1/2 -/
lemma integer_lt_halfInteger_same (n : ℤ) : integer n < halfInteger n := by
  change (n : ℚ) < n + 1/2
  linarith

/-- Half-integer time n + 1/2 comes before integer time n + 1 -/
lemma halfInteger_lt_integer_succ (n : ℤ) : halfInteger n < integer (n + 1) := by
  change (n : ℚ) + 1/2 < (n + 1 : ℤ)
  simp only [Int.cast_add, Int.cast_one]
  linarith

/-- Successor: move to the next time step -/
def succ : HalfIntegerTime → HalfIntegerTime
  | integer n => halfInteger n  -- n → n + 1/2
  | halfInteger n => integer (n + 1)  -- n + 1/2 → n + 1

/-- Predecessor: move to the previous time step -/
def pred : HalfIntegerTime → HalfIntegerTime
  | integer n => halfInteger (n - 1)  -- n → n - 1/2
  | halfInteger n => integer n  -- n + 1/2 → n

@[simp] lemma succ_integer (n : ℤ) : (integer n).succ = halfInteger n := rfl
@[simp] lemma succ_halfInteger (n : ℤ) : (halfInteger n).succ = integer (n + 1) := rfl
@[simp] lemma pred_integer (n : ℤ) : (integer n).pred = halfInteger (n - 1) := rfl
@[simp] lemma pred_halfInteger (n : ℤ) : (halfInteger n).pred = integer n := rfl

/-- succ and pred are inverses -/
@[simp] lemma pred_succ (t : HalfIntegerTime) : t.succ.pred = t := by
  cases t with
  | integer n => simp [succ, pred]
  | halfInteger n => simp [succ, pred]

@[simp] lemma succ_pred (t : HalfIntegerTime) : t.pred.succ = t := by
  cases t with
  | integer n => simp [succ, pred]
  | halfInteger n => simp [succ, pred]

/-- t < t.succ -/
lemma lt_succ (t : HalfIntegerTime) : t < t.succ := by
  cases t with
  | integer n => exact integer_lt_halfInteger_same n
  | halfInteger n => exact halfInteger_lt_integer_succ n

/-- t.pred < t -/
lemma pred_lt (t : HalfIntegerTime) : t.pred < t := by
  cases t with
  | integer n =>
    change (halfInteger (n - 1)).toRat < (integer n).toRat
    simp only [toRat, Int.cast_sub, Int.cast_one]
    linarith
  | halfInteger n =>
    change (integer n).toRat < (halfInteger n).toRat
    simp only [toRat]
    linarith

end HalfIntegerTime

/-! ## Integer Time Steps (Qubit States)

Integer time steps t = 0, 1, 2, ... are associated with qubit states and Pauli space-errors.
A Pauli error 'at time t' affects the state between measurement rounds at times t - 1/2 and t + 1/2.
-/

/-- An integer time step, associated with qubit states and space-errors -/
abbrev IntegerTimeStep := ℤ

/-- Convert a natural number time step to an integer time step -/
def TimeStep.toIntegerTime (t : TimeStep) : IntegerTimeStep := (t : ℤ)

/-- Convert an integer time step to a HalfIntegerTime -/
def IntegerTimeStep.toHalfIntegerTime (t : IntegerTimeStep) : HalfIntegerTime :=
  HalfIntegerTime.integer t

/-! ## Half-Integer Time Steps (Measurements)

Half-integer time steps t + 1/2 are associated with measurements and measurement errors.
A measurement 'at time t + 1/2' occurs between qubit states at times t and t + 1.
-/

/-- A half-integer time step (measurements), represented by storing the integer part.
    Value n represents the time n + 1/2 -/
abbrev MeasurementTimeStep := ℤ

/-- Convert a measurement time step to a HalfIntegerTime -/
def MeasurementTimeStep.toHalfIntegerTime (t : MeasurementTimeStep) : HalfIntegerTime :=
  HalfIntegerTime.halfInteger t

/-- The measurement time immediately after integer time t is t + 1/2 -/
def IntegerTimeStep.nextMeasurementTime (t : IntegerTimeStep) : MeasurementTimeStep := t

/-- The measurement time immediately before integer time t is t - 1/2 -/
def IntegerTimeStep.prevMeasurementTime (t : IntegerTimeStep) : MeasurementTimeStep := t - 1

/-- The integer time immediately after measurement time t + 1/2 is t + 1 -/
def MeasurementTimeStep.nextIntegerTime (t : MeasurementTimeStep) : IntegerTimeStep := t + 1

/-- The integer time immediately before measurement time t + 1/2 is t -/
def MeasurementTimeStep.prevIntegerTime (t : MeasurementTimeStep) : IntegerTimeStep := t

/-! ## Key Properties: Time Ordering -/

/-- A measurement at time t + 1/2 occurs between qubit states at times t and t + 1 -/
theorem measurement_between_states (t : MeasurementTimeStep) :
    HalfIntegerTime.integer t < HalfIntegerTime.halfInteger t ∧
    HalfIntegerTime.halfInteger t < HalfIntegerTime.integer (t + 1) :=
  ⟨HalfIntegerTime.integer_lt_halfInteger_same t,
   HalfIntegerTime.halfInteger_lt_integer_succ t⟩

/-- A Pauli error at integer time t affects state between measurements at t - 1/2 and t + 1/2 -/
theorem error_between_measurements (t : IntegerTimeStep) :
    HalfIntegerTime.halfInteger (t - 1) < HalfIntegerTime.integer t ∧
    HalfIntegerTime.integer t < HalfIntegerTime.halfInteger t := by
  constructor
  · change (HalfIntegerTime.halfInteger (t - 1)).toRat < (HalfIntegerTime.integer t).toRat
    simp only [HalfIntegerTime.toRat, Int.cast_sub, Int.cast_one]
    linarith
  · exact HalfIntegerTime.integer_lt_halfInteger_same t

/-! ## Key Time Points in Gauging Procedure

The gauging measurement procedure has three key time points:
- t₀: Start of the procedure
- tᵢ: Time of the initial gauging code deformation
- tₒ: Time of the final ungauging code deformation
-/

/-- Configuration of key time points in the gauging procedure -/
structure GaugingTimeConfig where
  /-- t₀: Start of the procedure -/
  t_start : IntegerTimeStep
  /-- tᵢ: Time of the initial gauging code deformation -/
  t_initial : IntegerTimeStep
  /-- tₒ: Time of the final ungauging code deformation -/
  t_final : IntegerTimeStep
  /-- The procedure proceeds in order: t₀ ≤ tᵢ ≤ tₒ -/
  start_le_initial : t_start ≤ t_initial
  initial_le_final : t_initial ≤ t_final

namespace GaugingTimeConfig

variable (config : GaugingTimeConfig)

/-- Duration of the gauging measurement procedure -/
def duration : ℕ := (config.t_final - config.t_start).toNat

/-- Duration of the gauged phase (from tᵢ to tₒ) -/
def gaugedPhaseDuration : ℕ := (config.t_final - config.t_initial).toNat

/-- First A_v measurement time: tᵢ - 1/2 -/
def firstGaugeMeasurement : MeasurementTimeStep := config.t_initial - 1

/-- Second A_v measurement time: tᵢ + 1/2 -/
def secondGaugeMeasurement : MeasurementTimeStep := config.t_initial

/-- Last A_v measurement time: tₒ - 1/2 -/
def lastGaugeMeasurementBefore : MeasurementTimeStep := config.t_final - 1

/-- Final A_v measurement time: tₒ + 1/2 -/
def finalGaugeMeasurement : MeasurementTimeStep := config.t_final

/-- The first A_v measurement at tᵢ - 1/2 comes before the integer time tᵢ -/
theorem firstGaugeMeasurement_before_initial :
    HalfIntegerTime.halfInteger config.firstGaugeMeasurement <
    HalfIntegerTime.integer config.t_initial := by
  simp only [firstGaugeMeasurement]
  change (HalfIntegerTime.halfInteger (config.t_initial - 1)).toRat <
         (HalfIntegerTime.integer config.t_initial).toRat
  simp only [HalfIntegerTime.toRat, Int.cast_sub, Int.cast_one]
  linarith

/-- The second A_v measurement at tᵢ + 1/2 comes after the integer time tᵢ -/
theorem secondGaugeMeasurement_after_initial :
    HalfIntegerTime.integer config.t_initial <
    HalfIntegerTime.halfInteger config.secondGaugeMeasurement := by
  simp only [secondGaugeMeasurement]
  exact HalfIntegerTime.integer_lt_halfInteger_same config.t_initial

end GaugingTimeConfig

/-! ## Time Step Convention Summary

The convention establishes a clear relationship between:
1. Integer times (qubit states, Pauli errors)
2. Half-integer times (measurements, measurement errors)

This interleaving ensures that:
- Each measurement occurs between two consecutive state times
- Each Pauli error affects the state between two consecutive measurements
-/

/-- The time step convention type -/
structure TimeStepConvention where
  /-- Integer times are for qubit states -/
  integerTimesForStates : Bool := true
  /-- Half-integer times are for measurements -/
  halfIntegerTimesForMeasurements : Bool := true

/-- The standard half-integer convention -/
def standardTimeConvention : TimeStepConvention where
  integerTimesForStates := true
  halfIntegerTimesForMeasurements := true

/-! ## Association of Fault Types with Time Types -/

/-- Space faults (Pauli errors) occur at integer times -/
def spaceFaultTime (t : TimeStep) : HalfIntegerTime :=
  HalfIntegerTime.integer (t : ℤ)

/-- Time faults (measurement errors) occur at half-integer times -/
def timeFaultTime (t : TimeStep) : HalfIntegerTime :=
  HalfIntegerTime.halfInteger (t : ℤ)

/-- A space fault at time t is between measurements at t - 1/2 and t + 1/2 -/
theorem spaceFault_between_measurements (t : TimeStep) (_ht : 0 < t) :
    HalfIntegerTime.halfInteger (t - 1 : ℤ) < spaceFaultTime t ∧
    spaceFaultTime t < HalfIntegerTime.halfInteger (t : ℤ) := by
  constructor
  · simp only [spaceFaultTime]
    change (HalfIntegerTime.halfInteger ((t : ℤ) - 1)).toRat <
           (HalfIntegerTime.integer (t : ℤ)).toRat
    simp only [HalfIntegerTime.toRat, Int.cast_sub, Int.cast_one]
    linarith
  · simp only [spaceFaultTime]
    exact HalfIntegerTime.integer_lt_halfInteger_same (t : ℤ)

/-- A measurement fault at time t + 1/2 is between states at t and t + 1 -/
theorem timeFault_between_states (t : TimeStep) :
    spaceFaultTime t < timeFaultTime t ∧
    timeFaultTime t < spaceFaultTime (t + 1) := by
  simp only [spaceFaultTime, timeFaultTime]
  constructor
  · exact HalfIntegerTime.integer_lt_halfInteger_same (t : ℤ)
  · have h := HalfIntegerTime.halfInteger_lt_integer_succ (t : ℤ)
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    exact h

/-! ## Ranges of Time Steps

Useful predicates and functions for working with ranges of integer and half-integer times. -/

/-- The integer time steps in a range [t₁, t₂] -/
def integerTimesInRange (t₁ t₂ : IntegerTimeStep) : Set IntegerTimeStep :=
  { t | t₁ ≤ t ∧ t ≤ t₂ }

/-- The measurement time steps in a range [t₁ + 1/2, t₂ - 1/2] -/
def measurementTimesInRange (t₁ t₂ : IntegerTimeStep) : Set MeasurementTimeStep :=
  { t | t₁ ≤ t ∧ t < t₂ }

/-- All half-integer times between integer times t₁ and t₂ -/
def allTimesInRange (t₁ t₂ : IntegerTimeStep) : Set HalfIntegerTime :=
  { t | HalfIntegerTime.integer t₁ ≤ t ∧ t ≤ HalfIntegerTime.integer t₂ }

/-! ## Simp Lemmas for Time Conversions -/

@[simp] lemma IntegerTimeStep.toHalfIntegerTime_isInteger (t : IntegerTimeStep) :
    t.toHalfIntegerTime.isInteger = true := rfl

@[simp] lemma MeasurementTimeStep.toHalfIntegerTime_isHalfInteger (t : MeasurementTimeStep) :
    t.toHalfIntegerTime.isHalfInteger = true := rfl

@[simp] lemma IntegerTimeStep.nextMeasurementTime_prevIntegerTime (t : IntegerTimeStep) :
    t.nextMeasurementTime.prevIntegerTime = t := rfl

@[simp] lemma MeasurementTimeStep.prevIntegerTime_nextMeasurementTime (t : MeasurementTimeStep) :
    t.prevIntegerTime.nextMeasurementTime = t := rfl

@[simp] lemma IntegerTimeStep.prevMeasurementTime_nextIntegerTime (t : IntegerTimeStep) :
    t.prevMeasurementTime.nextIntegerTime = t := by
  simp only [prevMeasurementTime, MeasurementTimeStep.nextIntegerTime]
  ring

@[simp] lemma MeasurementTimeStep.nextIntegerTime_prevMeasurementTime (t : MeasurementTimeStep) :
    t.nextIntegerTime.prevMeasurementTime = t := by
  simp only [nextIntegerTime, IntegerTimeStep.prevMeasurementTime]
  ring

/-! ## Summary

This formalization captures the half-integer time step convention for the fault-tolerant
gauging measurement procedure:

1. **Integer time steps** (t = 0, 1, 2, ...):
   - Associated with qubit states and Pauli space-errors
   - A Pauli error 'at time t' affects the state between measurements at t - 1/2 and t + 1/2

2. **Half-integer time steps** (t + 1/2):
   - Associated with measurements and measurement errors
   - A measurement 'at time t + 1/2' occurs between qubit states at times t and t + 1

3. **Key time points**:
   - t₀: Start of the procedure
   - tᵢ: Time of initial gauging (edge initialization, first A_v measurements at tᵢ ± 1/2)
   - tₒ: Time of final ungauging (last A_v measurements, edge readout at tₒ ± 1/2)

Key properties proven:
- `measurement_between_states`: Measurement at t + 1/2 is between states at t and t + 1
- `error_between_measurements`: Error at t is between measurements at t - 1/2 and t + 1/2
- `spaceFault_between_measurements`: Space faults occur between measurement rounds
- `timeFault_between_states`: Time faults occur between state times
- Ordering and conversion lemmas for half-integer time arithmetic
-/
