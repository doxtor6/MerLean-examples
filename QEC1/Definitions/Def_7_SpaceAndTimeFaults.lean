import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Lattice

import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps

/-!
# Def_7: Space and Time Faults

## Statement
In the context of fault-tolerant implementation of the gauging measurement procedure:

**Space-fault**: A Pauli error operator (single-qubit X, Y, or Z error) that occurs on some qubit
at some time during the procedure. Space-faults are characterized by the qubit affected and the
time of occurrence.

**Time-fault (measurement error)**: An error where the result of a quantum measurement is reported
incorrectly. The actual measurement projects onto an eigenspace, but the classical outcome is
flipped. Time-faults are characterized by the measurement affected and the time step.

**State initialization fault**: Treated as equivalent to a time-fault. A faulty initialization of
state |ψ⟩ is modeled as perfect initialization followed by an immediate space-fault.

**Spacetime fault**: A collection of space-faults and time-faults occurring at various locations
and times during the procedure. The set of all spacetime faults forms a group under composition.

## Main Definitions
- `PauliType` : The three Pauli error types (X, Y, Z)
- `SpaceFault` : A single-qubit Pauli error at a specific qubit and time
- `TimeFault` : A measurement error (bit flip) at a specific measurement and time
- `InitializationFault` : A state initialization fault (modeled as time-fault)
- `SpacetimeFault` : A collection of space-faults and time-faults
- `SpacetimeFaultGroup` : The group structure on spacetime faults

## Key Properties
- `spaceFault_identity` : Identity space-fault (no error)
- `timeFault_identity` : Identity time-fault (no measurement error)
- `spacetimeFault_compose` : Composition of spacetime faults
- `spacetimeFault_inv` : Inverse of a spacetime fault
- `spacetimeFault_group` : Group structure on spacetime faults
-/

open Finset

set_option linter.unusedSectionVars false

/-! ## Time Steps

We model time discretely. Each round of the procedure corresponds to a time step.
Time steps are indexed by natural numbers. -/

/-- A time step in the fault-tolerant procedure.
    Time 0 is the start, and time increases with each round. -/
abbrev TimeStep := ℕ

/-! ## Pauli Error Types

A single-qubit Pauli error can be X, Y, or Z. We also include Identity (I) for completeness,
representing "no error". -/

/-- The four single-qubit Pauli operators -/
inductive PauliType : Type
  | I : PauliType  -- Identity (no error)
  | X : PauliType  -- Bit flip
  | Y : PauliType  -- Combined bit and phase flip
  | Z : PauliType  -- Phase flip
  deriving DecidableEq, Repr, Inhabited

namespace PauliType

/-- Pauli multiplication table.
    I is identity, X² = Y² = Z² = I, and XYZ = iI (we ignore global phases). -/
def mul : PauliType → PauliType → PauliType
  | I, p => p
  | p, I => p
  | X, X => I
  | Y, Y => I
  | Z, Z => I
  | X, Y => Z
  | Y, X => Z
  | Y, Z => X
  | Z, Y => X
  | Z, X => Y
  | X, Z => Y

instance : Mul PauliType where
  mul := mul

/-- Pauli operators are self-inverse (up to phase) -/
def inv : PauliType → PauliType := id

instance : Inv PauliType where
  inv := inv

/-- Identity element -/
instance : One PauliType where
  one := I

@[simp] lemma one_eq_I : (1 : PauliType) = I := rfl

@[simp] lemma mul_I (p : PauliType) : p * I = p := by cases p <;> rfl

@[simp] lemma I_mul (p : PauliType) : I * p = p := by cases p <;> rfl

@[simp] lemma mul_self (p : PauliType) : p * p = I := by cases p <;> rfl

@[simp] lemma inv_eq_self (p : PauliType) : p⁻¹ = p := rfl

/-- Pauli multiplication is associative -/
theorem mul_assoc (a b c : PauliType) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Pauli inverses work correctly -/
theorem mul_inv_cancel (p : PauliType) : p * p⁻¹ = 1 := mul_self p

theorem inv_mul_cancel (p : PauliType) : p⁻¹ * p = 1 := mul_self p

/-- PauliType forms a group -/
instance : Group PauliType where
  mul_assoc := mul_assoc
  one_mul := I_mul
  mul_one := mul_I
  inv_mul_cancel := inv_mul_cancel

/-- Check if a Pauli type represents an actual error (not identity) -/
def isError : PauliType → Bool
  | I => false
  | _ => true

@[simp] lemma isError_I : isError I = false := rfl
@[simp] lemma isError_X : isError X = true := rfl
@[simp] lemma isError_Y : isError Y = true := rfl
@[simp] lemma isError_Z : isError Z = true := rfl

end PauliType

/-! ## Qubit Index Type

Qubits are indexed by some type. In the gauging context, we have:
- Vertex qubits (indexed by V)
- Edge qubits (indexed by E)
We use a unified qubit index type that can represent both. -/

/-- A qubit location in the system. Can be a vertex qubit or an edge qubit. -/
inductive QubitLoc (V E : Type*)
  | vertex : V → QubitLoc V E  -- A vertex qubit
  | edge : E → QubitLoc V E     -- An edge qubit
  deriving DecidableEq

namespace QubitLoc

variable {V E : Type*}

/-- Check if a location is a vertex qubit -/
def isVertex : QubitLoc V E → Bool
  | vertex _ => true
  | edge _ => false

/-- Check if a location is an edge qubit -/
def isEdge : QubitLoc V E → Bool
  | vertex _ => false
  | edge _ => true

@[simp] lemma isVertex_vertex (v : V) : (vertex v : QubitLoc V E).isVertex = true := rfl
@[simp] lemma isVertex_edge (e : E) : (edge e : QubitLoc V E).isVertex = false := rfl
@[simp] lemma isEdge_vertex (v : V) : (vertex v : QubitLoc V E).isEdge = false := rfl
@[simp] lemma isEdge_edge (e : E) : (edge e : QubitLoc V E).isEdge = true := rfl

/-- Extract the vertex index if this is a vertex qubit -/
def getVertex : QubitLoc V E → Option V
  | vertex v => some v
  | edge _ => none

/-- Extract the edge index if this is an edge qubit -/
def getEdge : QubitLoc V E → Option E
  | vertex _ => none
  | edge e => some e

instance [Fintype V] [Fintype E] : Fintype (QubitLoc V E) :=
  Fintype.ofEquiv (V ⊕ E) {
    toFun := Sum.elim vertex edge
    invFun := fun q => match q with
      | vertex v => Sum.inl v
      | edge e => Sum.inr e
    left_inv := fun s => by cases s <;> rfl
    right_inv := fun q => by cases q <;> rfl
  }

@[simp]
lemma card_qubitLoc [Fintype V] [Fintype E] :
    Fintype.card (QubitLoc V E) = Fintype.card V + Fintype.card E := by
  rw [Fintype.card_eq.mpr ⟨{
    toFun := fun q => match q with
      | vertex v => Sum.inl v
      | edge e => Sum.inr e
    invFun := Sum.elim vertex edge
    left_inv := fun q => by cases q <;> rfl
    right_inv := fun s => by cases s <;> rfl
  }⟩]
  simp [Fintype.card_sum]

end QubitLoc

/-! ## Measurement Index Type

Measurements are indexed by type M. Each measurement corresponds to measuring some check
operator (Gauss law A_v, flux B_p, or original stabilizer s_j). -/

/-- A measurement index. This identifies which measurement is being referred to. -/
abbrev MeasurementIdx (M : Type*) := M

/-! ## Space-Faults

A space-fault is a single-qubit Pauli error occurring on a specific qubit at a specific time. -/

/-- A space-fault: a Pauli error on a specific qubit at a specific time.
    The error `pauliType` occurs on qubit `qubit` at time `time`. -/
structure SpaceFault (V E : Type*) where
  /-- The qubit where the error occurs -/
  qubit : QubitLoc V E
  /-- The time step when the error occurs -/
  time : TimeStep
  /-- The type of Pauli error (X, Y, Z, or I for no error) -/
  pauliType : PauliType
  deriving DecidableEq

namespace SpaceFault

variable {V E : Type*}

/-- The identity space-fault at a given location and time (no error) -/
def identity (q : QubitLoc V E) (t : TimeStep) : SpaceFault V E :=
  ⟨q, t, PauliType.I⟩

/-- Check if this space-fault represents an actual error -/
def isActualError (f : SpaceFault V E) : Bool := f.pauliType.isError

@[simp]
lemma isActualError_identity (q : QubitLoc V E) (t : TimeStep) :
    (identity q t).isActualError = false := rfl

/-- Compose two space-faults at the same location and time -/
def compose (f g : SpaceFault V E)
    (_h_qubit : f.qubit = g.qubit) (_h_time : f.time = g.time) : SpaceFault V E :=
  ⟨f.qubit, f.time, f.pauliType * g.pauliType⟩

/-- The inverse of a space-fault (same fault, since Paulis are self-inverse) -/
def inv (f : SpaceFault V E) : SpaceFault V E :=
  ⟨f.qubit, f.time, f.pauliType⁻¹⟩

@[simp]
lemma inv_pauliType (f : SpaceFault V E) : f.inv.pauliType = f.pauliType := rfl

@[simp]
lemma inv_qubit (f : SpaceFault V E) : f.inv.qubit = f.qubit := rfl

@[simp]
lemma inv_time (f : SpaceFault V E) : f.inv.time = f.time := rfl

/-- A space-fault on a vertex qubit -/
def onVertex (v : V) (t : TimeStep) (p : PauliType) : SpaceFault V E :=
  ⟨QubitLoc.vertex v, t, p⟩

/-- A space-fault on an edge qubit -/
def onEdge (e : E) (t : TimeStep) (p : PauliType) : SpaceFault V E :=
  ⟨QubitLoc.edge e, t, p⟩

@[simp]
lemma onVertex_qubit (v : V) (t : TimeStep) (p : PauliType) :
    (onVertex v t p : SpaceFault V E).qubit = QubitLoc.vertex v := rfl

@[simp]
lemma onEdge_qubit (e : E) (t : TimeStep) (p : PauliType) :
    (onEdge e t p : SpaceFault V E).qubit = QubitLoc.edge e := rfl

/-- An X error on a vertex qubit -/
abbrev X_vertex (v : V) (t : TimeStep) : SpaceFault V E := onVertex v t PauliType.X

/-- A Y error on a vertex qubit -/
abbrev Y_vertex (v : V) (t : TimeStep) : SpaceFault V E := onVertex v t PauliType.Y

/-- A Z error on a vertex qubit -/
abbrev Z_vertex (v : V) (t : TimeStep) : SpaceFault V E := onVertex v t PauliType.Z

/-- An X error on an edge qubit -/
abbrev X_edge (e : E) (t : TimeStep) : SpaceFault V E := onEdge e t PauliType.X

/-- A Y error on an edge qubit -/
abbrev Y_edge (e : E) (t : TimeStep) : SpaceFault V E := onEdge e t PauliType.Y

/-- A Z error on an edge qubit -/
abbrev Z_edge (e : E) (t : TimeStep) : SpaceFault V E := onEdge e t PauliType.Z

end SpaceFault

/-! ## Time-Faults (Measurement Errors)

A time-fault is a measurement error: the classical outcome of a measurement is flipped.
This is also called a "measurement error" or "readout error". -/

/-- A time-fault: a measurement whose classical outcome is flipped.
    The measurement `measurement` at time `time` reports the wrong outcome. -/
structure TimeFault (M : Type*) where
  /-- The measurement that is affected -/
  measurement : M
  /-- The time step when the measurement occurs -/
  time : TimeStep
  /-- Whether this fault is active (true = flipped outcome) -/
  isFlipped : Bool
  deriving DecidableEq

namespace TimeFault

variable {M : Type*}

/-- The identity time-fault (no measurement error) -/
def identity (m : M) (t : TimeStep) : TimeFault M :=
  ⟨m, t, false⟩

/-- An active measurement error -/
def active (m : M) (t : TimeStep) : TimeFault M :=
  ⟨m, t, true⟩

/-- Check if this time-fault represents an actual error -/
def isActualError (f : TimeFault M) : Bool := f.isFlipped

@[simp]
lemma isActualError_identity (m : M) (t : TimeStep) :
    (identity m t).isActualError = false := rfl

@[simp]
lemma isActualError_active (m : M) (t : TimeStep) :
    (active m t).isActualError = true := rfl

/-- Compose two time-faults at the same measurement and time (XOR of flips) -/
def compose (f g : TimeFault M)
    (_h_meas : f.measurement = g.measurement) (_h_time : f.time = g.time) : TimeFault M :=
  ⟨f.measurement, f.time, xor f.isFlipped g.isFlipped⟩

/-- The inverse of a time-fault (same fault, since flip is self-inverse) -/
def inv (f : TimeFault M) : TimeFault M := f

@[simp]
lemma inv_isFlipped (f : TimeFault M) : f.inv.isFlipped = f.isFlipped := rfl

@[simp]
lemma inv_measurement (f : TimeFault M) : f.inv.measurement = f.measurement := rfl

@[simp]
lemma inv_time (f : TimeFault M) : f.inv.time = f.time := rfl

end TimeFault

/-! ## Initialization Faults

A state initialization fault is treated as equivalent to a time-fault.
A faulty initialization of state |ψ⟩ is modeled as perfect initialization
followed by an immediate space-fault.

We model this by having initialization faults be a special case that can be
represented either as a time-fault on the initialization "measurement" or
as a space-fault immediately after initialization. -/

/-- An initialization fault on a qubit.
    This represents a faulty preparation of the initial state.
    It is modeled as equivalent to perfect initialization followed by a space-fault. -/
structure InitializationFault (V E : Type*) where
  /-- The qubit being initialized -/
  qubit : QubitLoc V E
  /-- The time step of initialization -/
  time : TimeStep
  /-- The effective Pauli error (applied after "perfect" initialization) -/
  effectiveError : PauliType
  deriving DecidableEq

namespace InitializationFault

variable {V E : Type*}

/-- Convert an initialization fault to an equivalent space-fault.
    The space-fault occurs at the same time as the initialization. -/
def toSpaceFault (f : InitializationFault V E) : SpaceFault V E :=
  ⟨f.qubit, f.time, f.effectiveError⟩

/-- The identity initialization fault (no error) -/
def identity (q : QubitLoc V E) (t : TimeStep) : InitializationFault V E :=
  ⟨q, t, PauliType.I⟩

/-- Check if this initialization fault represents an actual error -/
def isActualError (f : InitializationFault V E) : Bool := f.effectiveError.isError

@[simp]
lemma toSpaceFault_qubit (f : InitializationFault V E) :
    f.toSpaceFault.qubit = f.qubit := rfl

@[simp]
lemma toSpaceFault_time (f : InitializationFault V E) :
    f.toSpaceFault.time = f.time := rfl

@[simp]
lemma toSpaceFault_pauliType (f : InitializationFault V E) :
    f.toSpaceFault.pauliType = f.effectiveError := rfl

@[simp]
lemma toSpaceFault_identity (q : QubitLoc V E) (t : TimeStep) :
    (identity q t).toSpaceFault = SpaceFault.identity q t := rfl

end InitializationFault

/-! ## Spacetime Faults

A spacetime fault is a collection of space-faults and time-faults occurring at various
locations and times during the procedure. -/

/-- A spacetime fault: a collection of space-faults and time-faults.

    We represent this as:
    - A function from (qubit, time) pairs to Pauli errors (for space-faults)
    - A function from (measurement, time) pairs to flip flags (for time-faults)

    This representation allows for efficient composition (pointwise multiplication/XOR). -/
@[ext]
structure SpacetimeFault (V E M : Type*) where
  /-- The Pauli error at each (qubit, time) location. Identity means no error. -/
  spaceErrors : QubitLoc V E → TimeStep → PauliType
  /-- Whether each (measurement, time) has a flipped outcome. False means no error. -/
  timeErrors : M → TimeStep → Bool

namespace SpacetimeFault

variable {V E M : Type*}

/-- The identity spacetime fault (no errors anywhere) -/
def identity : SpacetimeFault V E M where
  spaceErrors := fun _ _ => PauliType.I
  timeErrors := fun _ _ => false

instance : One (SpacetimeFault V E M) where
  one := identity

@[simp]
lemma one_spaceErrors (q : QubitLoc V E) (t : TimeStep) :
    (1 : SpacetimeFault V E M).spaceErrors q t = PauliType.I := rfl

@[simp]
lemma one_timeErrors (m : M) (t : TimeStep) :
    (1 : SpacetimeFault V E M).timeErrors m t = false := rfl

/-- Composition of spacetime faults (pointwise multiplication/XOR) -/
def compose (f g : SpacetimeFault V E M) : SpacetimeFault V E M where
  spaceErrors := fun q t => f.spaceErrors q t * g.spaceErrors q t
  timeErrors := fun m t => xor (f.timeErrors m t) (g.timeErrors m t)

instance : Mul (SpacetimeFault V E M) where
  mul := compose

@[simp]
lemma mul_spaceErrors (f g : SpacetimeFault V E M) (q : QubitLoc V E) (t : TimeStep) :
    (f * g).spaceErrors q t = f.spaceErrors q t * g.spaceErrors q t := rfl

@[simp]
lemma mul_timeErrors (f g : SpacetimeFault V E M) (m : M) (t : TimeStep) :
    (f * g).timeErrors m t = xor (f.timeErrors m t) (g.timeErrors m t) := rfl

/-- Inverse of a spacetime fault -/
def inv (f : SpacetimeFault V E M) : SpacetimeFault V E M where
  spaceErrors := fun q t => (f.spaceErrors q t)⁻¹
  timeErrors := f.timeErrors  -- XOR is self-inverse

instance : Inv (SpacetimeFault V E M) where
  inv := inv

@[simp]
lemma inv_spaceErrors (f : SpacetimeFault V E M) (q : QubitLoc V E) (t : TimeStep) :
    f⁻¹.spaceErrors q t = (f.spaceErrors q t)⁻¹ := rfl

@[simp]
lemma inv_timeErrors (f : SpacetimeFault V E M) (m : M) (t : TimeStep) :
    f⁻¹.timeErrors m t = f.timeErrors m t := rfl

/-- Spacetime faults form a group under composition -/
theorem mul_assoc (a b c : SpacetimeFault V E M) : a * b * c = a * (b * c) := by
  ext q t
  · simp [PauliType.mul_assoc]
  · simp only [mul_timeErrors]
    cases a.timeErrors q t <;> cases b.timeErrors q t <;> cases c.timeErrors q t <;> rfl

theorem one_mul (f : SpacetimeFault V E M) : 1 * f = f := by
  ext q t
  · simp
  · simp

theorem mul_one (f : SpacetimeFault V E M) : f * 1 = f := by
  ext q t
  · simp
  · simp

theorem inv_mul_cancel (f : SpacetimeFault V E M) : f⁻¹ * f = 1 := by
  ext q t
  · simp [PauliType.inv_mul_cancel]
  · simp only [mul_timeErrors, inv_timeErrors, one_timeErrors]
    cases f.timeErrors q t <;> rfl

instance : Group (SpacetimeFault V E M) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel

/-- Create a spacetime fault from a single space-fault -/
def fromSpaceFault [DecidableEq V] [DecidableEq E] (f : SpaceFault V E) : SpacetimeFault V E M where
  spaceErrors := fun q t => if q = f.qubit ∧ t = f.time then f.pauliType else PauliType.I
  timeErrors := fun _ _ => false

/-- Create a spacetime fault from a single time-fault -/
def fromTimeFault [DecidableEq M] (f : TimeFault M) : SpacetimeFault V E M where
  spaceErrors := fun _ _ => PauliType.I
  timeErrors := fun m t => if m = f.measurement ∧ t = f.time then f.isFlipped else false

/-- Create a spacetime fault from a single initialization fault -/
def fromInitializationFault [DecidableEq V] [DecidableEq E] (f : InitializationFault V E) : SpacetimeFault V E M :=
  fromSpaceFault f.toSpaceFault

@[simp]
lemma fromSpaceFault_at_location [DecidableEq V] [DecidableEq E] (f : SpaceFault V E) :
    (fromSpaceFault (M := M) f).spaceErrors f.qubit f.time = f.pauliType := by
  simp [fromSpaceFault]

@[simp]
lemma fromTimeFault_at_location [DecidableEq M] (f : TimeFault M) :
    (fromTimeFault (V := V) (E := E) f).timeErrors f.measurement f.time = f.isFlipped := by
  simp [fromTimeFault]

/-- The set of (qubit, time) locations where space errors occur -/
def spaceErrorLocations [Fintype V] [Fintype E]
    (f : SpacetimeFault V E M) (times : Finset TimeStep) : Finset (QubitLoc V E × TimeStep) :=
  (Finset.univ ×ˢ times).filter fun ⟨q, t⟩ => f.spaceErrors q t ≠ PauliType.I

/-- The set of (measurement, time) locations where time errors occur -/
def timeErrorLocations [Fintype M]
    (f : SpacetimeFault V E M) (times : Finset TimeStep) : Finset (M × TimeStep) :=
  (Finset.univ ×ˢ times).filter fun ⟨m, t⟩ => f.timeErrors m t = true

/-- The total weight of a spacetime fault (number of non-trivial errors) over given time range -/
def weight [Fintype V] [Fintype E] [Fintype M]
    (f : SpacetimeFault V E M) (times : Finset TimeStep) : ℕ :=
  (f.spaceErrorLocations times).card + (f.timeErrorLocations times).card

@[simp]
lemma weight_identity [Fintype V] [Fintype E] [Fintype M] (times : Finset TimeStep) :
    weight (1 : SpacetimeFault V E M) times = 0 := by
  simp [weight, spaceErrorLocations, timeErrorLocations]

/-- A spacetime fault is "pure space" if it has no time errors -/
def isPureSpace (f : SpacetimeFault V E M) : Prop :=
  ∀ m t, f.timeErrors m t = false

/-- A spacetime fault is "pure time" if it has no space errors -/
def isPureTime (f : SpacetimeFault V E M) : Prop :=
  ∀ q t, f.spaceErrors q t = PauliType.I

@[simp]
lemma identity_isPureSpace : isPureSpace (1 : SpacetimeFault V E M) := by
  simp [isPureSpace]

@[simp]
lemma identity_isPureTime : isPureTime (1 : SpacetimeFault V E M) := by
  simp [isPureTime]

lemma fromSpaceFault_isPureSpace [DecidableEq V] [DecidableEq E] (f : SpaceFault V E) :
    isPureSpace (fromSpaceFault (M := M) f) := by
  simp [isPureSpace, fromSpaceFault]

lemma fromTimeFault_isPureTime [DecidableEq M] (f : TimeFault M) :
    isPureTime (fromTimeFault (V := V) (E := E) f) := by
  simp [isPureTime, fromTimeFault]

/-- The space-only component of a spacetime fault -/
def spaceComponent (f : SpacetimeFault V E M) : SpacetimeFault V E M where
  spaceErrors := f.spaceErrors
  timeErrors := fun _ _ => false

/-- The time-only component of a spacetime fault -/
def timeComponent (f : SpacetimeFault V E M) : SpacetimeFault V E M where
  spaceErrors := fun _ _ => PauliType.I
  timeErrors := f.timeErrors

@[simp]
lemma spaceComponent_isPureSpace (f : SpacetimeFault V E M) :
    isPureSpace f.spaceComponent := by
  simp [isPureSpace, spaceComponent]

@[simp]
lemma timeComponent_isPureTime (f : SpacetimeFault V E M) :
    isPureTime f.timeComponent := by
  simp [isPureTime, timeComponent]

/-- A spacetime fault decomposes into its space and time components -/
theorem decompose (f : SpacetimeFault V E M) :
    f = f.spaceComponent * f.timeComponent := by
  ext q t
  · simp [spaceComponent, timeComponent]
  · simp only [mul_timeErrors, spaceComponent, timeComponent]
    cases f.timeErrors q t <;> rfl

end SpacetimeFault

/-! ## The Group of Spacetime Faults

The set of all spacetime faults forms a group under composition.
This is captured by the `Group` instance on `SpacetimeFault`. -/

/-- The subgroup of pure space-faults -/
def pureSpaceFaults (V E M : Type*) : Subgroup (SpacetimeFault V E M) where
  carrier := { f | f.isPureSpace }
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, SpacetimeFault.isPureSpace] at *
    intro m t
    simp [hf m t, hg m t]
  one_mem' := SpacetimeFault.identity_isPureSpace
  inv_mem' := by
    intro f hf
    simp only [Set.mem_setOf_eq, SpacetimeFault.isPureSpace] at *
    intro m t
    simp [hf m t]

/-- The subgroup of pure time-faults -/
def pureTimeFaults (V E M : Type*) : Subgroup (SpacetimeFault V E M) where
  carrier := { f | f.isPureTime }
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, SpacetimeFault.isPureTime] at *
    intro q t
    simp [hf q t, hg q t]
  one_mem' := SpacetimeFault.identity_isPureTime
  inv_mem' := by
    intro f hf
    simp only [Set.mem_setOf_eq, SpacetimeFault.isPureTime] at *
    intro q t
    simp only [SpacetimeFault.inv_spaceErrors, hf q t, PauliType.inv_eq_self]

/-! ## Summary

This formalization captures the fault model for fault-tolerant quantum error correction:

1. **Space-faults**: Single-qubit Pauli errors (X, Y, Z) occurring at specific qubits and times.
   - Represented by `SpaceFault V E` which records qubit location, time, and error type.
   - Can occur on vertex qubits (V) or edge qubits (E).

2. **Time-faults**: Measurement errors where classical outcomes are flipped.
   - Represented by `TimeFault M` which records measurement index, time, and flip status.
   - Models readout errors in the measurement process.

3. **Initialization faults**: Faulty state preparation.
   - Modeled as equivalent to a space-fault immediately after initialization.
   - Represented by `InitializationFault V E`.

4. **Spacetime faults**: Collections of space and time faults.
   - Represented by `SpacetimeFault V E M` as functions from locations to errors.
   - Form a group under pointwise composition (`Group` instance).
   - Can be decomposed into pure-space and pure-time components.

Key properties proven:
- `PauliType` forms a group (Pauli operators under multiplication)
- `SpacetimeFault` forms a group under composition
- Pure space-faults form a subgroup
- Pure time-faults form a subgroup
- Every spacetime fault decomposes as space_component * time_component
-/
