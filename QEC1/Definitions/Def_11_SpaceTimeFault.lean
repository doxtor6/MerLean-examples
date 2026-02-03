import QEC1.Remarks.Rem_1_NotationConventions

/-!
# Spacetime Faults (Definition 11)

## Statement
In the fault-tolerant implementation of the gauging measurement:

**Space-fault (Pauli error)**: A Pauli error operator P ∈ {X, Y, Z} that occurs on some qubit
at some time step during the procedure.

**Time-fault (measurement error)**: An error where the result of a measurement is reported
incorrectly (bit-flip of the classical outcome).

**Initialization fault**: An error where a qubit is initialized in the wrong state.
This is equivalent to a space-fault: initializing in wrong state = perfect initialization
followed by an error operator.

**General spacetime fault**: A collection F of space-faults and time-faults occurring at
various spacetime locations.

**Weight of a fault**: |F| = (number of single-qubit Pauli errors) + (number of measurement
errors).

## Main Results
**Main Inductive** (`FaultType`): Classification of fault types (Space, Time, Initialization)
**Main Structure** (`SpaceFault`): A Pauli error at a specific qubit and time step
**Main Structure** (`TimeFault`): A measurement error at a specific measurement location
**Main Structure** (`SpaceTimeFault`): A collection of space and time faults with weight

## File Structure
1. Fault Type Classification: Space-fault, Time-fault, Initialization fault
2. Space Fault: Pauli error on a qubit at a time step
3. Time Fault: Measurement bit-flip error
4. Initialization Fault: Wrong initial state (equivalent to space-fault)
5. Spacetime Fault Collection: General collection F with weight |F|
6. Helper Lemmas: Basic properties and weight calculations
-/

namespace QEC

/-! ## Section 1: Basic Types -/

/-- Time step index in the circuit execution -/
abbrev TimeStep := ℕ

/-- Qubit index for n-qubit systems -/
abbrev QubitIndex (n : ℕ) := Fin n

/-- Measurement location: which measurement (check operator index) -/
abbrev MeasurementIndex (m : ℕ) := Fin m

/-! ## Section 2: Fault Type Classification -/

/-- Classification of fault types in fault-tolerant quantum computation.
    These are the three fundamental ways errors can occur. -/
inductive FaultType where
  /-- Space-fault: A Pauli error occurs on a qubit -/
  | space
  /-- Time-fault: A measurement outcome is flipped -/
  | time
  /-- Initialization fault: A qubit starts in wrong state (equivalent to space-fault) -/
  | initialization
  deriving DecidableEq, Repr

namespace FaultType

instance : Fintype FaultType where
  elems := {space, time, initialization}
  complete := fun x => by cases x <;> simp

/-- There are exactly 3 fault types -/
theorem card_faultType : Fintype.card FaultType = 3 := rfl

/-- Initialization faults are equivalent to space faults.
    This captures: wrong initialization = perfect init + error operator -/
def isEquivalentToSpace : FaultType → Bool
  | space => true
  | initialization => true
  | time => false

/-- Space and initialization faults are Pauli-like -/
theorem space_equiv : isEquivalentToSpace space = true := rfl
theorem init_equiv : isEquivalentToSpace initialization = true := rfl
theorem time_not_space_equiv : isEquivalentToSpace time = false := rfl

end FaultType

/-! ## Section 3: Non-identity Pauli Type -/

/-- The three non-identity single-qubit Pauli operators that can occur as errors.
    We exclude I since it represents "no error". -/
inductive ErrorPauli where
  | X : ErrorPauli  -- Bit flip
  | Y : ErrorPauli  -- Both bit and phase flip
  | Z : ErrorPauli  -- Phase flip
  deriving DecidableEq, Repr

namespace ErrorPauli

instance : Fintype ErrorPauli where
  elems := {X, Y, Z}
  complete := fun x => by cases x <;> simp

/-- There are exactly 3 error Pauli types -/
theorem card_errorPauli : Fintype.card ErrorPauli = 3 := rfl

/-- Convert ErrorPauli to general PauliOp -/
def toPauliOp : ErrorPauli → PauliOp
  | X => PauliOp.X
  | Y => PauliOp.Y
  | Z => PauliOp.Z

/-- toPauliOp never returns I -/
theorem toPauliOp_ne_I (e : ErrorPauli) : e.toPauliOp ≠ PauliOp.I := by
  cases e <;> simp [toPauliOp]

/-- Conversion is injective -/
theorem toPauliOp_injective : Function.Injective toPauliOp := by
  intro e₁ e₂ h
  cases e₁ <;> cases e₂ <;> simp [toPauliOp] at h <;> try rfl

end ErrorPauli

/-! ## Section 4: Space Fault (Pauli Error) -/

/-- A space-fault is a Pauli error operator P ∈ {X, Y, Z} that occurs on some qubit
    at some time step during the procedure. -/
structure SpaceFault (n : ℕ) where
  /-- The type of Pauli error (X, Y, or Z) -/
  pauliType : ErrorPauli
  /-- The qubit on which the error occurs -/
  qubit : Fin n
  /-- The time step at which the error occurs -/
  timeStep : TimeStep
  deriving DecidableEq, Repr

namespace SpaceFault

variable {n : ℕ}

/-- Two space faults are at the same spacetime location iff same qubit and time -/
def sameLocation (f₁ f₂ : SpaceFault n) : Prop :=
  f₁.qubit = f₂.qubit ∧ f₁.timeStep = f₂.timeStep

instance : DecidablePred (fun p : SpaceFault n × SpaceFault n => sameLocation p.1 p.2) :=
  fun p => inferInstanceAs (Decidable (p.1.qubit = p.2.qubit ∧ p.1.timeStep = p.2.timeStep))

/-- Each space fault contributes weight 1 -/
def weight (_f : SpaceFault n) : ℕ := 1

/-- Space fault weight is always 1 -/
@[simp]
theorem weight_eq_one (f : SpaceFault n) : f.weight = 1 := rfl

/-- Create an X error at a specific location -/
def mkX (q : Fin n) (t : TimeStep) : SpaceFault n :=
  ⟨ErrorPauli.X, q, t⟩

/-- Create a Y error at a specific location -/
def mkY (q : Fin n) (t : TimeStep) : SpaceFault n :=
  ⟨ErrorPauli.Y, q, t⟩

/-- Create a Z error at a specific location -/
def mkZ (q : Fin n) (t : TimeStep) : SpaceFault n :=
  ⟨ErrorPauli.Z, q, t⟩

/-- The Pauli operator of an X error is X -/
@[simp]
theorem mkX_pauliType (q : Fin n) (t : TimeStep) : (mkX q t).pauliType = ErrorPauli.X := rfl

/-- The Pauli operator of a Y error is Y -/
@[simp]
theorem mkY_pauliType (q : Fin n) (t : TimeStep) : (mkY q t).pauliType = ErrorPauli.Y := rfl

/-- The Pauli operator of a Z error is Z -/
@[simp]
theorem mkZ_pauliType (q : Fin n) (t : TimeStep) : (mkZ q t).pauliType = ErrorPauli.Z := rfl

end SpaceFault

/-! ## Section 5: Time Fault (Measurement Error) -/

/-- A time-fault is an error where the result of a measurement is reported incorrectly.
    This represents a bit-flip of the classical measurement outcome. -/
structure TimeFault (m : ℕ) where
  /-- Which measurement (check operator) has the error -/
  measurementIndex : Fin m
  /-- The time step (round) of the measurement -/
  measurementRound : TimeStep
  deriving DecidableEq, Repr

namespace TimeFault

variable {m : ℕ}

/-- Two time faults are at the same location iff same measurement and round -/
def sameLocation (f₁ f₂ : TimeFault m) : Prop :=
  f₁.measurementIndex = f₂.measurementIndex ∧ f₁.measurementRound = f₂.measurementRound

instance : DecidablePred (fun p : TimeFault m × TimeFault m => sameLocation p.1 p.2) :=
  fun p => inferInstanceAs (Decidable (p.1.measurementIndex = p.2.measurementIndex ∧
                                       p.1.measurementRound = p.2.measurementRound))

/-- Each time fault contributes weight 1 -/
def weight (_f : TimeFault m) : ℕ := 1

/-- Time fault weight is always 1 -/
@[simp]
theorem weight_eq_one (f : TimeFault m) : f.weight = 1 := rfl

/-- Create a measurement error at a specific location -/
def create (idx : Fin m) (round : TimeStep) : TimeFault m :=
  ⟨idx, round⟩

/-- Measurement index of a created fault -/
@[simp]
theorem create_measurementIndex (idx : Fin m) (round : TimeStep) :
    (create idx round).measurementIndex = idx := rfl

/-- Round of a created fault -/
@[simp]
theorem create_measurementRound (idx : Fin m) (round : TimeStep) :
    (create idx round).measurementRound = round := rfl

end TimeFault

/-! ## Section 6: Initialization Fault -/

/-- An initialization fault is an error where a qubit is initialized in the wrong state.
    This is equivalent to a space-fault at time step 0:
    wrong initialization = perfect initialization followed by an error operator.

    We model this as a special case of SpaceFault at the initialization time step (0). -/
structure InitFault (n : ℕ) where
  /-- The type of Pauli error that "corrects" to the wrong state -/
  pauliType : ErrorPauli
  /-- The qubit that is wrongly initialized -/
  qubit : Fin n
  deriving DecidableEq, Repr

namespace InitFault

variable {n : ℕ}

/-- Convert an initialization fault to an equivalent space fault at time 0.
    This formalizes: initializing in wrong state = perfect init + error operator -/
def toSpaceFault (f : InitFault n) : SpaceFault n :=
  ⟨f.pauliType, f.qubit, 0⟩

/-- The space fault conversion produces a fault at time 0 -/
@[simp]
theorem toSpaceFault_timeStep (f : InitFault n) : f.toSpaceFault.timeStep = 0 := rfl

/-- The space fault conversion preserves the Pauli type -/
@[simp]
theorem toSpaceFault_pauliType (f : InitFault n) :
    f.toSpaceFault.pauliType = f.pauliType := rfl

/-- The space fault conversion preserves the qubit -/
@[simp]
theorem toSpaceFault_qubit (f : InitFault n) : f.toSpaceFault.qubit = f.qubit := rfl

/-- Each initialization fault contributes weight 1 -/
def weight (_f : InitFault n) : ℕ := 1

/-- Initialization fault weight is always 1 -/
@[simp]
theorem weight_eq_one (f : InitFault n) : f.weight = 1 := rfl

/-- Create an initialization fault that should have been |0⟩ but got |1⟩ (X error) -/
def mkBitFlip (q : Fin n) : InitFault n := ⟨ErrorPauli.X, q⟩

/-- Create an initialization fault that should have been |+⟩ but got |-⟩ (Z error) -/
def mkPhaseFlip (q : Fin n) : InitFault n := ⟨ErrorPauli.Z, q⟩

end InitFault

/-! ## Section 7: General Spacetime Fault Collection -/

/-- A general spacetime fault is a collection F of space-faults and time-faults
    occurring at various spacetime locations.

    The weight |F| = (number of single-qubit Pauli errors) + (number of measurement errors) -/
structure SpaceTimeFault (n m : ℕ) where
  /-- The set of space faults (Pauli errors) -/
  spaceFaults : Finset (SpaceFault n)
  /-- The set of time faults (measurement errors) -/
  timeFaults : Finset (TimeFault m)
  deriving DecidableEq

namespace SpaceTimeFault

variable {n m : ℕ}

/-- The weight of a spacetime fault collection.
    |F| = (number of single-qubit Pauli errors) + (number of measurement errors) -/
def weight (F : SpaceTimeFault n m) : ℕ :=
  F.spaceFaults.card + F.timeFaults.card

/-- The empty fault (no errors) -/
def empty : SpaceTimeFault n m :=
  ⟨∅, ∅⟩

/-- Number of space faults -/
def numSpaceFaults (F : SpaceTimeFault n m) : ℕ := F.spaceFaults.card

/-- Number of time faults -/
def numTimeFaults (F : SpaceTimeFault n m) : ℕ := F.timeFaults.card

/-- The empty fault has weight 0 -/
@[simp]
theorem empty_weight : (empty : SpaceTimeFault n m).weight = 0 := by
  simp [empty, weight]

/-- The empty fault has no space faults -/
@[simp]
theorem empty_numSpaceFaults : (empty : SpaceTimeFault n m).numSpaceFaults = 0 := by
  simp [empty, numSpaceFaults]

/-- The empty fault has no time faults -/
@[simp]
theorem empty_numTimeFaults : (empty : SpaceTimeFault n m).numTimeFaults = 0 := by
  simp [empty, numTimeFaults]

/-- Weight equals sum of component counts -/
theorem weight_eq_sum (F : SpaceTimeFault n m) :
    F.weight = F.numSpaceFaults + F.numTimeFaults := rfl

/-- Weight is non-negative -/
theorem weight_nonneg (F : SpaceTimeFault n m) : 0 ≤ F.weight := Nat.zero_le _

/-- Union of two spacetime faults -/
def union (F₁ F₂ : SpaceTimeFault n m) : SpaceTimeFault n m :=
  ⟨F₁.spaceFaults ∪ F₂.spaceFaults, F₁.timeFaults ∪ F₂.timeFaults⟩

/-- Weight of union is at most sum of weights -/
theorem weight_union_le (F₁ F₂ : SpaceTimeFault n m) :
    (union F₁ F₂).weight ≤ F₁.weight + F₂.weight := by
  unfold union weight
  have h1 : (F₁.spaceFaults ∪ F₂.spaceFaults).card ≤
            F₁.spaceFaults.card + F₂.spaceFaults.card :=
    Finset.card_union_le _ _
  have h2 : (F₁.timeFaults ∪ F₂.timeFaults).card ≤
            F₁.timeFaults.card + F₂.timeFaults.card :=
    Finset.card_union_le _ _
  calc (F₁.spaceFaults ∪ F₂.spaceFaults).card + (F₁.timeFaults ∪ F₂.timeFaults).card
      ≤ (F₁.spaceFaults.card + F₂.spaceFaults.card) +
        (F₁.timeFaults.card + F₂.timeFaults.card) := Nat.add_le_add h1 h2
    _ = (F₁.spaceFaults.card + F₁.timeFaults.card) +
        (F₂.spaceFaults.card + F₂.timeFaults.card) := by ring

/-- Weight of union equals sum for disjoint faults -/
theorem weight_union_disjoint (F₁ F₂ : SpaceTimeFault n m)
    (hspace : Disjoint F₁.spaceFaults F₂.spaceFaults)
    (htime : Disjoint F₁.timeFaults F₂.timeFaults) :
    (union F₁ F₂).weight = F₁.weight + F₂.weight := by
  unfold union weight
  rw [Finset.card_union_of_disjoint hspace, Finset.card_union_of_disjoint htime]
  ring

/-- Add a single space fault -/
def addSpaceFault (F : SpaceTimeFault n m) (f : SpaceFault n) : SpaceTimeFault n m :=
  ⟨insert f F.spaceFaults, F.timeFaults⟩

/-- Add a single time fault -/
def addTimeFault (F : SpaceTimeFault n m) (f : TimeFault m) : SpaceTimeFault n m :=
  ⟨F.spaceFaults, insert f F.timeFaults⟩

/-- Adding a new space fault increases weight by 1 -/
theorem weight_addSpaceFault (F : SpaceTimeFault n m) (f : SpaceFault n)
    (hf : f ∉ F.spaceFaults) :
    (F.addSpaceFault f).weight = F.weight + 1 := by
  unfold addSpaceFault weight
  rw [Finset.card_insert_of_notMem hf]
  ring

/-- Adding a new time fault increases weight by 1 -/
theorem weight_addTimeFault (F : SpaceTimeFault n m) (f : TimeFault m)
    (hf : f ∉ F.timeFaults) :
    (F.addTimeFault f).weight = F.weight + 1 := by
  unfold addTimeFault weight
  rw [Finset.card_insert_of_notMem hf]
  ring

/-- Create a single-space-fault collection -/
def singleSpace (f : SpaceFault n) : SpaceTimeFault n m :=
  ⟨{f}, ∅⟩

/-- Create a single-time-fault collection -/
def singleTime (f : TimeFault m) : SpaceTimeFault n m :=
  ⟨∅, {f}⟩

/-- Single space fault has weight 1 -/
@[simp]
theorem singleSpace_weight (f : SpaceFault n) :
    (singleSpace f : SpaceTimeFault n m).weight = 1 := by
  simp [singleSpace, weight]

/-- Single time fault has weight 1 -/
@[simp]
theorem singleTime_weight (f : TimeFault m) :
    (singleTime f : SpaceTimeFault n m).weight = 1 := by
  simp [singleTime, weight]

end SpaceTimeFault

/-! ## Section 8: Fault Correction Properties -/

/-- A fault-tolerant code can correct a spacetime fault collection F if |F| ≤ t,
    where t is the fault tolerance threshold. -/
def canCorrect (t : ℕ) (F : SpaceTimeFault n m) : Prop :=
  F.weight ≤ t

/-- The correctable property is monotone: if we can correct F, we can correct any subset -/
theorem canCorrect_of_subset {t : ℕ} {n m : ℕ}
    (F₁ F₂ : SpaceTimeFault n m)
    (h_space : F₁.spaceFaults ⊆ F₂.spaceFaults)
    (h_time : F₁.timeFaults ⊆ F₂.timeFaults)
    (h : canCorrect t F₂) : canCorrect t F₁ := by
  unfold canCorrect at *
  unfold SpaceTimeFault.weight at *
  have hs : F₁.spaceFaults.card ≤ F₂.spaceFaults.card := Finset.card_le_card h_space
  have ht : F₁.timeFaults.card ≤ F₂.timeFaults.card := Finset.card_le_card h_time
  omega

/-- Empty fault is always correctable -/
theorem empty_canCorrect (t : ℕ) :
    canCorrect t (SpaceTimeFault.empty : SpaceTimeFault n m) := by
  unfold canCorrect
  simp

/-! ## Section 9: Space Faults from Pauli Strings -/

/-- Extract non-identity qubits from a Pauli string as a Finset -/
def pauliNonIdentityQubits (P : PauliString n) : Finset (Fin n) :=
  Finset.filter (fun q => P q ≠ PauliOp.I) Finset.univ

/-- The number of non-identity qubits equals the weight -/
theorem pauliNonIdentityQubits_card (P : PauliString n) :
    (pauliNonIdentityQubits P).card = weight P := by
  unfold pauliNonIdentityQubits weight
  rfl

/-! ## Section 10: Helper Lemmas -/

/-- Space faults and time faults are disjoint by type -/
theorem space_time_disjoint : FaultType.space ≠ FaultType.time := by decide

/-- Initialization is equivalent to space for counting purposes -/
theorem init_counts_as_space (f : InitFault n) :
    f.toSpaceFault.weight = f.weight := by
  simp [InitFault.weight, SpaceFault.weight]

/-- The weight function respects equivalence of initialization and space faults -/
theorem weight_init_equiv (f : InitFault n) :
    SpaceFault.weight f.toSpaceFault = 1 := by
  rfl

/-- Weight is additive for disjoint fault collections -/
theorem weight_additive (F₁ F₂ : SpaceTimeFault n m)
    (h_disj_space : Disjoint F₁.spaceFaults F₂.spaceFaults)
    (h_disj_time : Disjoint F₁.timeFaults F₂.timeFaults) :
    (SpaceTimeFault.union F₁ F₂).weight = F₁.weight + F₂.weight :=
  SpaceTimeFault.weight_union_disjoint F₁ F₂ h_disj_space h_disj_time

/-- Zero weight means no faults -/
theorem zero_weight_empty (F : SpaceTimeFault n m) (h : F.weight = 0) :
    F.spaceFaults = ∅ ∧ F.timeFaults = ∅ := by
  unfold SpaceTimeFault.weight at h
  have h1 : F.spaceFaults.card = 0 := by omega
  have h2 : F.timeFaults.card = 0 := by omega
  exact ⟨Finset.card_eq_zero.mp h1, Finset.card_eq_zero.mp h2⟩

/-- Extensionality for SpaceTimeFault -/
theorem SpaceTimeFault_ext (F₁ F₂ : SpaceTimeFault n m)
    (hs : F₁.spaceFaults = F₂.spaceFaults)
    (ht : F₁.timeFaults = F₂.timeFaults) : F₁ = F₂ := by
  cases F₁
  cases F₂
  simp only at hs ht
  subst hs ht
  rfl

/-- If weight is positive, at least one fault exists -/
theorem weight_pos_nonempty (F : SpaceTimeFault n m) (h : 0 < F.weight) :
    F.spaceFaults.Nonempty ∨ F.timeFaults.Nonempty := by
  unfold SpaceTimeFault.weight at h
  by_contra h_empty
  push_neg at h_empty
  -- h_empty now has type: F.spaceFaults = ∅ ∧ F.timeFaults = ∅
  simp only [h_empty.1, h_empty.2, Finset.card_empty, add_zero] at h
  exact Nat.lt_irrefl 0 h

/-- Space faults form a Finset with decidable membership -/
instance (n : ℕ) : DecidableEq (SpaceFault n) := inferInstance

/-- Time faults form a Finset with decidable membership -/
instance (m : ℕ) : DecidableEq (TimeFault m) := inferInstance

/-- The total number of faults -/
def totalFaults (F : SpaceTimeFault n m) : ℕ := F.weight

/-- Total faults equals weight -/
@[simp]
theorem totalFaults_eq_weight (F : SpaceTimeFault n m) : totalFaults F = F.weight := rfl

/-- Empty spacetime fault has empty space faults -/
@[simp]
theorem empty_spaceFaults :
    (SpaceTimeFault.empty : SpaceTimeFault n m).spaceFaults = ∅ := rfl

/-- Empty spacetime fault has empty time faults -/
@[simp]
theorem empty_timeFaults :
    (SpaceTimeFault.empty : SpaceTimeFault n m).timeFaults = ∅ := rfl

end QEC
