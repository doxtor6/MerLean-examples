import QEC1.Remarks.Rem_2_NotationPauliOperators
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.SymmDiff

/-!
# Definition 7: Space and Time Faults

## Statement
In the context of fault-tolerant quantum error correction:

1. A **space-fault** (or **space error**) is a Pauli error operator that occurs on some
   qubit at a specific time during the procedure.

2. A **time-fault** (or **measurement error**) is an error where the result of a
   measurement is reported incorrectly (i.e., +1 is reported as -1 or vice versa).

3. A **spacetime fault** is a collection of space-faults and time-faults occurring at
   various locations and times during the procedure.

**Convention:** State mis-initialization faults are treated as time-faults that are
equivalent to a perfect initialization followed by a space-fault.

## Main Results
- `SpaceFault`: A Pauli error on a specific qubit at a specific time
- `TimeFault`: A measurement error (bit-flip of outcome) at a specific measurement location
- `SpacetimeFault`: A collection of space-faults and time-faults
- `SpacetimeFault.weight`: The total number of individual faults
- `SpacetimeFault.empty`: The fault-free configuration
- `SpacetimeFault.compose`: Composition (symmetric difference) of faults

## Corollaries
- Weight properties: empty has weight 0, single faults have weight 1
- Composition is commutative and involutive
- Space-only and time-only fault embeddings
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open scoped symmDiff

variable {Q : Type*} {T : Type*} {M : Type*}

/-! ## Space Faults -/

/-- A space-fault (space error) is a single-qubit Pauli error at a specific qubit
    and time. The error is described by which qubit is affected, when it occurs,
    and what Pauli error is applied (X, Y, or Z, encoded as a nonzero element of
    ZMod 2 x ZMod 2 for the x and z components). -/
structure SpaceFault (Q : Type*) (T : Type*) where
  /-- The qubit where the error occurs. -/
  qubit : Q
  /-- The time at which the error occurs. -/
  time : T
  /-- The X-component of the Pauli error (1 if X or Y, 0 otherwise). -/
  xComponent : ZMod 2
  /-- The Z-component of the Pauli error (1 if Z or Y, 0 otherwise). -/
  zComponent : ZMod 2
  /-- The error is nontrivial: at least one component is nonzero. -/
  nontrivial : xComponent ≠ 0 ∨ zComponent ≠ 0

/-! ## Time Faults -/

/-- A time-fault (measurement error) is a single measurement whose outcome is
    reported incorrectly. In ZMod 2 encoding (0 -> +1, 1 -> -1), this corresponds
    to flipping the measurement outcome bit. The fault is identified by which
    measurement is affected.

    Convention: State mis-initialization faults are also modeled as time-faults.
    For example, initializing |0> but getting |1> is equivalent to a perfect
    initialization followed by an X error. The initialization measurement
    (projecting onto |0>) is treated as a measurement that reported incorrectly. -/
structure TimeFault (M : Type*) where
  /-- The measurement whose outcome is flipped. -/
  measurement : M

/-! ## Spacetime Faults -/

/-- A spacetime fault is a collection of space-faults and time-faults occurring
    at various locations and times during the procedure. We represent it as
    a pair of finsets: one of space-faults and one of time-faults.

    The weight of a spacetime fault is the total number of individual faults
    (each single-qubit Pauli error counts as 1, each measurement error counts as 1). -/
@[ext]
structure SpacetimeFault (Q : Type*) (T : Type*) (M : Type*) where
  /-- The collection of space-faults (Pauli errors on qubits at specific times). -/
  spaceFaults : Finset (SpaceFault Q T)
  /-- The collection of time-faults (measurement errors). -/
  timeFaults : Finset (TimeFault M)

namespace SpacetimeFault

variable [DecidableEq Q] [DecidableEq T] [DecidableEq M]
variable [DecidableEq (SpaceFault Q T)] [DecidableEq (TimeFault M)]

/-- The weight of a spacetime fault: total number of individual faults. -/
def weight (F : SpacetimeFault Q T M) : ℕ :=
  F.spaceFaults.card + F.timeFaults.card

/-- The empty spacetime fault: no errors at all. -/
def empty : SpacetimeFault Q T M :=
  ⟨∅, ∅⟩

/-- A spacetime fault consisting of a single space-fault. -/
def ofSpaceFault (f : SpaceFault Q T) : SpacetimeFault Q T M :=
  ⟨{f}, ∅⟩

/-- A spacetime fault consisting of a single time-fault. -/
def ofTimeFault (f : TimeFault M) : SpacetimeFault Q T M :=
  ⟨∅, {f}⟩

/-- Composition of spacetime faults via symmetric difference.
    Applying the same error twice cancels it; flipping an outcome twice restores it. -/
def compose (F₁ F₂ : SpacetimeFault Q T M) : SpacetimeFault Q T M :=
  ⟨F₁.spaceFaults ∆ F₂.spaceFaults, F₁.timeFaults ∆ F₂.timeFaults⟩

/-- A spacetime fault is pure-space if it has no time-faults. -/
def isPureSpace (F : SpacetimeFault Q T M) : Prop :=
  F.timeFaults = ∅

/-- A spacetime fault is pure-time if it has no space-faults. -/
def isPureTime (F : SpacetimeFault Q T M) : Prop :=
  F.spaceFaults = ∅

/-- The number of space-faults in the spacetime fault. -/
def spaceWeight (F : SpacetimeFault Q T M) : ℕ :=
  F.spaceFaults.card

/-- The number of time-faults in the spacetime fault. -/
def timeWeight (F : SpacetimeFault Q T M) : ℕ :=
  F.timeFaults.card

/-! ## Basic Properties -/

@[simp]
theorem weight_empty : (empty : SpacetimeFault Q T M).weight = 0 := by
  simp [weight, empty]

@[simp]
theorem weight_eq_space_plus_time (F : SpacetimeFault Q T M) :
    F.weight = F.spaceWeight + F.timeWeight := by
  simp [weight, spaceWeight, timeWeight]

@[simp]
theorem spaceWeight_empty : (empty : SpacetimeFault Q T M).spaceWeight = 0 := by
  simp [spaceWeight, empty]

@[simp]
theorem timeWeight_empty : (empty : SpacetimeFault Q T M).timeWeight = 0 := by
  simp [timeWeight, empty]

theorem weight_ofSpaceFault (f : SpaceFault Q T) :
    (ofSpaceFault f : SpacetimeFault Q T M).weight = 1 := by
  simp [weight, ofSpaceFault]

theorem weight_ofTimeFault (f : TimeFault M) :
    (ofTimeFault f : SpacetimeFault Q T M).weight = 1 := by
  simp [weight, ofTimeFault]

@[simp]
theorem isPureSpace_empty : (empty : SpacetimeFault Q T M).isPureSpace := by
  simp [isPureSpace, empty]

@[simp]
theorem isPureTime_empty : (empty : SpacetimeFault Q T M).isPureTime := by
  simp [isPureTime, empty]

theorem isPureSpace_ofSpaceFault (f : SpaceFault Q T) :
    (ofSpaceFault f : SpacetimeFault Q T M).isPureSpace := by
  simp [isPureSpace, ofSpaceFault]

theorem isPureTime_ofTimeFault (f : TimeFault M) :
    (ofTimeFault f : SpacetimeFault Q T M).isPureTime := by
  simp [isPureTime, ofTimeFault]

theorem weight_pos_of_nonempty_space {F : SpacetimeFault Q T M}
    (h : F.spaceFaults.Nonempty) : 0 < F.weight := by
  unfold weight
  have := Finset.card_pos.mpr h
  omega

theorem weight_pos_of_nonempty_time {F : SpacetimeFault Q T M}
    (h : F.timeFaults.Nonempty) : 0 < F.weight := by
  unfold weight
  have := Finset.card_pos.mpr h
  omega

/-! ## Composition Properties -/

theorem compose_comm (F₁ F₂ : SpacetimeFault Q T M) :
    compose F₁ F₂ = compose F₂ F₁ := by
  ext a
  · simp [compose, Finset.mem_symmDiff]; tauto
  · simp [compose, Finset.mem_symmDiff]; tauto

theorem compose_self (F : SpacetimeFault Q T M) :
    compose F F = empty := by
  ext a
  · simp [compose, empty, Finset.mem_symmDiff]
  · simp [compose, empty, Finset.mem_symmDiff]

theorem compose_empty_left (F : SpacetimeFault Q T M) :
    compose empty F = F := by
  ext a
  · simp [compose, empty, Finset.mem_symmDiff]
  · simp [compose, empty, Finset.mem_symmDiff]

theorem compose_empty_right (F : SpacetimeFault Q T M) :
    compose F empty = F := by
  ext a
  · simp [compose, empty, Finset.mem_symmDiff]
  · simp [compose, empty, Finset.mem_symmDiff]

theorem compose_assoc (F₁ F₂ F₃ : SpacetimeFault Q T M) :
    compose (compose F₁ F₂) F₃ = compose F₁ (compose F₂ F₃) := by
  ext a
  · simp [compose, Finset.mem_symmDiff]; tauto
  · simp [compose, Finset.mem_symmDiff]; tauto

/-! ## Space-only and time-only projections -/

/-- The space component of a spacetime fault (keeping only space-faults). -/
def spaceComponent (F : SpacetimeFault Q T M) : SpacetimeFault Q T M :=
  ⟨F.spaceFaults, ∅⟩

/-- The time component of a spacetime fault (keeping only time-faults). -/
def timeComponent (F : SpacetimeFault Q T M) : SpacetimeFault Q T M :=
  ⟨∅, F.timeFaults⟩

@[simp]
theorem spaceComponent_isPureSpace (F : SpacetimeFault Q T M) :
    F.spaceComponent.isPureSpace := by
  simp [spaceComponent, isPureSpace]

@[simp]
theorem timeComponent_isPureTime (F : SpacetimeFault Q T M) :
    F.timeComponent.isPureTime := by
  simp [timeComponent, isPureTime]

theorem weight_spaceComponent (F : SpacetimeFault Q T M) :
    F.spaceComponent.weight = F.spaceWeight := by
  simp [spaceComponent, weight, spaceWeight]

theorem weight_timeComponent (F : SpacetimeFault Q T M) :
    F.timeComponent.weight = F.timeWeight := by
  simp [timeComponent, weight, timeWeight]

/-- Any spacetime fault decomposes into its space and time components. -/
theorem decompose_space_time (F : SpacetimeFault Q T M) :
    compose F.spaceComponent F.timeComponent = F := by
  ext a
  · simp [compose, spaceComponent, timeComponent, Finset.mem_symmDiff]
  · simp [compose, spaceComponent, timeComponent, Finset.mem_symmDiff]

/-! ## Pauli operator associated to space-faults at a given time -/

/-- The space-faults of a spacetime fault restricted to a specific time. -/
def spaceFaultsAt (F : SpacetimeFault Q T M) (t : T) :
    Finset (SpaceFault Q T) :=
  F.spaceFaults.filter (fun f => f.time = t)

/-- The composite Pauli error on qubit system Q from all space-faults at time t. -/
def pauliErrorAt [Fintype Q] (F : SpacetimeFault Q T M) (t : T) : PauliOp Q where
  xVec q := ∑ f ∈ F.spaceFaultsAt t, if f.qubit = q then f.xComponent else 0
  zVec q := ∑ f ∈ F.spaceFaultsAt t, if f.qubit = q then f.zComponent else 0

@[simp]
theorem pauliErrorAt_empty [Fintype Q] (t : T) :
    (empty : SpacetimeFault Q T M).pauliErrorAt t = 1 := by
  ext q <;> simp [pauliErrorAt, spaceFaultsAt, empty]

/-! ## Convention: Initialization faults as time-faults

The convention that initialization faults are treated as time-faults is captured
by modeling each initialization as a measurement. An initialization fault
(e.g., preparing |1> instead of |0>) is then a time-fault on that measurement,
equivalent to perfect initialization followed by a Pauli X error (space-fault). -/

/-- An initialization fault viewed as a time-fault on the initialization measurement. -/
def initializationFault (initMeasurement : M) : SpacetimeFault Q T M :=
  ofTimeFault ⟨initMeasurement⟩

/-- The equivalent space-fault: perfect initialization followed by Pauli X error. -/
def initializationAsSpaceFault (q : Q) (t : T) : SpacetimeFault Q T M :=
  ofSpaceFault ⟨q, t, 1, 0, Or.inl one_ne_zero⟩

theorem initializationFault_weight (m : M) :
    (initializationFault m : SpacetimeFault Q T M).weight = 1 := by
  simp [initializationFault, ofTimeFault, weight]

theorem initializationAsSpaceFault_weight (q : Q) (t : T) :
    (initializationAsSpaceFault q t : SpacetimeFault Q T M).weight = 1 := by
  simp [initializationAsSpaceFault, ofSpaceFault, weight]

/-! ## Weight bounds -/

theorem spaceWeight_le_weight (F : SpacetimeFault Q T M) :
    F.spaceWeight ≤ F.weight := by
  unfold weight spaceWeight; omega

theorem timeWeight_le_weight (F : SpacetimeFault Q T M) :
    F.timeWeight ≤ F.weight := by
  unfold weight timeWeight; omega

theorem weight_zero_iff (F : SpacetimeFault Q T M) :
    F.weight = 0 ↔ F.spaceFaults = ∅ ∧ F.timeFaults = ∅ := by
  simp [weight, Nat.add_eq_zero_iff, Finset.card_eq_zero]

theorem weight_zero_iff_empty (F : SpacetimeFault Q T M) :
    F.weight = 0 ↔ F = empty := by
  constructor
  · intro h
    have ⟨hs, ht⟩ := (weight_zero_iff F).mp h
    ext <;> simp_all [empty]
  · intro h; subst h; simp

end SpacetimeFault

/-! ## Fault classification predicates -/

/-- A spacetime fault is trivial (identity) if it has no faults at all. -/
def SpacetimeFault.isTrivial [DecidableEq Q] [DecidableEq T] [DecidableEq M]
    [DecidableEq (SpaceFault Q T)] [DecidableEq (TimeFault M)]
    (F : SpacetimeFault Q T M) : Prop :=
  F = SpacetimeFault.empty

/-- The set of qubits affected by space-faults in a spacetime fault. -/
def SpacetimeFault.affectedQubits [DecidableEq Q]
    [DecidableEq (SpaceFault Q T)]
    (F : SpacetimeFault Q T M) : Finset Q :=
  F.spaceFaults.image SpaceFault.qubit

/-- The set of times at which space-faults occur. -/
def SpacetimeFault.activeTimes [DecidableEq T]
    [DecidableEq (SpaceFault Q T)]
    (F : SpacetimeFault Q T M) : Finset T :=
  F.spaceFaults.image SpaceFault.time

/-- The set of measurements affected by time-faults. -/
def SpacetimeFault.affectedMeasurements [DecidableEq M]
    [DecidableEq (TimeFault M)]
    (F : SpacetimeFault Q T M) : Finset M :=
  F.timeFaults.image TimeFault.measurement

/-! ## Measurement outcome with faults

A time-fault flips the measurement outcome. In ZMod 2 encoding (0 -> +1, 1 -> -1),
this means adding 1 to the ideal outcome. -/

/-- The observed measurement outcome given an ideal outcome and a set of time-faults.
    If measurement m appears in the time-faults, the outcome is flipped. -/
def observedOutcome [DecidableEq M] [DecidableEq (TimeFault M)]
    (idealOutcome : M → ZMod 2)
    (faults : Finset (TimeFault M))
    (m : M) : ZMod 2 :=
  idealOutcome m + if (⟨m⟩ : TimeFault M) ∈ faults then 1 else 0

theorem observedOutcome_no_fault [DecidableEq M] [DecidableEq (TimeFault M)]
    (idealOutcome : M → ZMod 2) (faults : Finset (TimeFault M)) (m : M)
    (h : (⟨m⟩ : TimeFault M) ∉ faults) :
    observedOutcome idealOutcome faults m = idealOutcome m := by
  simp [observedOutcome, h]

theorem observedOutcome_with_fault [DecidableEq M] [DecidableEq (TimeFault M)]
    (idealOutcome : M → ZMod 2) (faults : Finset (TimeFault M)) (m : M)
    (h : (⟨m⟩ : TimeFault M) ∈ faults) :
    observedOutcome idealOutcome faults m = idealOutcome m + 1 := by
  simp [observedOutcome, h]

theorem observedOutcome_flip [DecidableEq M] [DecidableEq (TimeFault M)]
    (idealOutcome : M → ZMod 2) (faults : Finset (TimeFault M)) (m : M)
    (h : (⟨m⟩ : TimeFault M) ∈ faults) :
    observedOutcome idealOutcome faults m ≠ idealOutcome m := by
  rw [observedOutcome_with_fault idealOutcome faults m h]
  intro heq
  have h1 : (0 : ZMod 2) = 1 := by
    have : idealOutcome m + 1 - idealOutcome m = idealOutcome m - idealOutcome m := by
      rw [heq]
    simp at this
  exact zero_ne_one h1
