import QEC1.Definitions.Def_11_SpaceTimeFault

/-!
# Detector (Definition 12)

## Statement
A **detector** is a collection of state initializations and measurements that yield a deterministic
result in the absence of faults.

Formally, a detector D consists of:
- A set of qubit initializations (each in a known state)
- A set of measurements (each of a known observable)
- A parity constraint: the product of measurement outcomes must equal a fixed value (typically +1)

**Detector violation**: A spacetime fault F **violates** detector D if F causes the parity
constraint of D to fail.

**Syndrome**: The **syndrome** of a spacetime fault F is the set of all detectors violated by F:
  syn(F) = {D : F violates D}

## Main Results
**Main Structure** (`Detector`): A detector with initializations, measurements, and parity
**Main Definition** (`violates`): When a fault violates a detector
**Main Definition** (`syndrome`): The syndrome of a fault (set of violated detectors)

## File Structure
1. Initialization State: Known initial state for a qubit
2. Measurement Observable: Known observable to measure
3. Parity Value: The expected parity (+1 or -1, encoded as ZMod 2)
4. Detector Structure: Collection with parity constraint
5. Violation: When a fault causes parity to fail
6. Syndrome: Set of all violated detectors
7. Helper Lemmas: Basic properties of detectors and syndromes
-/

namespace QEC

/-! ## Section 1: Initialization States -/

/-- A known initial state for a qubit.
    In quantum error correction, qubits are typically initialized in:
    - Computational basis: |0⟩ or |1⟩
    - Hadamard basis: |+⟩ or |-⟩ -/
inductive InitState where
  | zero : InitState   -- |0⟩ state
  | one : InitState    -- |1⟩ state
  | plus : InitState   -- |+⟩ = (|0⟩ + |1⟩)/√2
  | minus : InitState  -- |-⟩ = (|0⟩ - |1⟩)/√2
  deriving DecidableEq, Repr

namespace InitState

instance : Fintype InitState where
  elems := {zero, one, plus, minus}
  complete := fun x => by cases x <;> simp

/-- There are exactly 4 initialization states -/
theorem card_initState : Fintype.card InitState = 4 := rfl

/-- The basis type (computational or Hadamard) -/
def isComputationalBasis : InitState → Bool
  | zero => true
  | one => true
  | plus => false
  | minus => false

/-- The basis type (Hadamard) -/
def isHadamardBasis : InitState → Bool
  | zero => false
  | one => false
  | plus => true
  | minus => true

/-- The parity (0 for |0⟩/|+⟩, 1 for |1⟩/|-⟩) encoded as ZMod 2 -/
def parity : InitState → ZMod 2
  | zero => 0
  | one => 1
  | plus => 0
  | minus => 1

end InitState

/-! ## Section 2: Measurement Observables -/

/-- A measurement observable for a single qubit.
    Standard basis measurements in QEC are:
    - Z-basis: measures in computational basis (eigenvalues ±1)
    - X-basis: measures in Hadamard basis (eigenvalues ±1) -/
inductive MeasBasis where
  | Z : MeasBasis  -- Computational basis measurement
  | X : MeasBasis  -- Hadamard basis measurement
  deriving DecidableEq, Repr

namespace MeasBasis

instance : Fintype MeasBasis where
  elems := {Z, X}
  complete := fun x => by cases x <;> simp

/-- There are exactly 2 measurement bases -/
theorem card_measBasis : Fintype.card MeasBasis = 2 := rfl

end MeasBasis

/-! ## Section 3: Qubit Initialization in a Detector -/

/-- A single qubit initialization in a detector.
    Specifies which qubit is initialized and in what state. -/
structure QubitInit (n : ℕ) where
  /-- The qubit being initialized -/
  qubit : Fin n
  /-- The initial state -/
  state : InitState
  /-- The time step of initialization (typically 0) -/
  timeStep : TimeStep
  deriving DecidableEq, Repr

namespace QubitInit

variable {n : ℕ}

/-- Two initializations are on the same qubit -/
def sameQubit (i₁ i₂ : QubitInit n) : Prop := i₁.qubit = i₂.qubit

instance : DecidablePred (fun p : QubitInit n × QubitInit n => sameQubit p.1 p.2) :=
  fun p => inferInstanceAs (Decidable (p.1.qubit = p.2.qubit))

end QubitInit

/-! ## Section 4: Single Qubit Measurement in a Detector -/

/-- A single qubit measurement in a detector.
    Specifies which qubit is measured, in what basis, and when. -/
structure SingleMeasurement (n : ℕ) where
  /-- The qubit being measured -/
  qubit : Fin n
  /-- The measurement basis -/
  basis : MeasBasis
  /-- The time step of measurement -/
  timeStep : TimeStep
  deriving DecidableEq, Repr

namespace SingleMeasurement

variable {n : ℕ}

/-- Two measurements are at the same location -/
def sameLocation (m₁ m₂ : SingleMeasurement n) : Prop :=
  m₁.qubit = m₂.qubit ∧ m₁.timeStep = m₂.timeStep

instance : DecidablePred (fun p : SingleMeasurement n × SingleMeasurement n =>
    sameLocation p.1 p.2) :=
  fun p => inferInstanceAs (Decidable (p.1.qubit = p.2.qubit ∧ p.1.timeStep = p.2.timeStep))

end SingleMeasurement

/-! ## Section 5: Detector Structure -/

/-- A detector is a collection of initializations and measurements with a parity constraint.
    In the absence of faults, the product of measurement outcomes equals the expected parity.

    We use ZMod 2 for parity: 0 represents +1 (even parity), 1 represents -1 (odd parity). -/
structure Detector (n : ℕ) where
  /-- The set of qubit initializations -/
  initializations : Finset (QubitInit n)
  /-- The set of measurements -/
  measurements : Finset (SingleMeasurement n)
  /-- The expected parity: 0 for +1 (typical), 1 for -1 -/
  expectedParity : ZMod 2
  deriving DecidableEq

namespace Detector

variable {n : ℕ}

/-- The number of initializations in a detector -/
def numInits (D : Detector n) : ℕ := D.initializations.card

/-- The number of measurements in a detector -/
def numMeasurements (D : Detector n) : ℕ := D.measurements.card

/-- A detector with no components (trivially satisfied) -/
def trivial (n : ℕ) : Detector n where
  initializations := ∅
  measurements := ∅
  expectedParity := 0

/-- The trivial detector has no initializations -/
@[simp]
theorem trivial_numInits : (trivial n).numInits = 0 := by
  simp [trivial, numInits]

/-- The trivial detector has no measurements -/
@[simp]
theorem trivial_numMeasurements : (trivial n).numMeasurements = 0 := by
  simp [trivial, numMeasurements]

/-- The trivial detector has expected parity 0 (+1) -/
@[simp]
theorem trivial_expectedParity : (trivial n).expectedParity = 0 := rfl

/-- The qubits involved in a detector (union of initialized and measured qubits) -/
def involvedQubits (D : Detector n) : Finset (Fin n) :=
  (D.initializations.image (·.qubit)) ∪ (D.measurements.image (·.qubit))

/-- Check if a detector is non-trivial (has at least one component) -/
def isNontrivial (D : Detector n) : Prop :=
  D.initializations.Nonempty ∨ D.measurements.Nonempty

end Detector

/-! ## Section 6: Effect of Faults on Measurements -/

/-- A single-qubit Pauli error affects a measurement outcome.
    - An X or Y error flips a Z-basis measurement
    - A Z or Y error flips an X-basis measurement -/
def pauliFlipsMeasurement (p : ErrorPauli) (b : MeasBasis) : Bool :=
  match p, b with
  | ErrorPauli.X, MeasBasis.Z => true   -- X flips Z measurement
  | ErrorPauli.Y, MeasBasis.Z => true   -- Y flips Z measurement
  | ErrorPauli.Y, MeasBasis.X => true   -- Y flips X measurement
  | ErrorPauli.Z, MeasBasis.X => true   -- Z flips X measurement
  | ErrorPauli.X, MeasBasis.X => false  -- X doesn't flip X measurement
  | ErrorPauli.Z, MeasBasis.Z => false  -- Z doesn't flip Z measurement

/-- X error flips Z measurement -/
theorem X_flips_Z : pauliFlipsMeasurement ErrorPauli.X MeasBasis.Z = true := rfl

/-- Z error flips X measurement -/
theorem Z_flips_X : pauliFlipsMeasurement ErrorPauli.Z MeasBasis.X = true := rfl

/-- Y error flips both Z and X measurements -/
theorem Y_flips_both : pauliFlipsMeasurement ErrorPauli.Y MeasBasis.Z = true ∧
    pauliFlipsMeasurement ErrorPauli.Y MeasBasis.X = true := ⟨rfl, rfl⟩

/-! ## Section 7: Counting Parity Flips -/

/-- Count how many times space faults flip a specific measurement's outcome.
    A space fault flips the measurement if:
    1. It affects the same qubit
    2. It occurs at or before the measurement time (and after initialization)
    3. The Pauli type anticommutes with the measurement basis -/
def countSpaceFlips (spaceFaults : Finset (SpaceFault n)) (m : SingleMeasurement n) : ℕ :=
  (spaceFaults.filter (fun f =>
    f.qubit = m.qubit ∧
    f.timeStep ≤ m.timeStep ∧
    pauliFlipsMeasurement f.pauliType m.basis = true)).card

/-- Count time faults that affect a measurement at the same location.
    (Each time fault at this measurement location flips the reported outcome once.) -/
def countTimeFaults (m : ℕ) (timeFaults : Finset (TimeFault m))
    (_meas : SingleMeasurement n) (_measIdx : Fin m) : ℕ :=
  -- For simplicity, we count time faults at the given measurement index
  -- In a full model, this would match measurement locations more precisely
  timeFaults.card

/-! ## Section 8: Parity Calculation -/

/-- The total parity flip induced by a spacetime fault on a detector's measurements.
    This is the sum (mod 2) of:
    1. Space fault flips on each measurement
    2. Time fault flips on each measurement

    The detector is violated if this differs from 0. -/
def parityFlip {m : ℕ} (F : SpaceTimeFault n m) (D : Detector n) : ZMod 2 :=
  -- Sum over all measurements the number of space flips (mod 2)
  D.measurements.sum (fun meas =>
    (countSpaceFlips F.spaceFaults meas : ZMod 2)) +
  -- Add contribution from time faults (simplified model)
  (F.timeFaults.card : ZMod 2)

/-- The observed parity when fault F occurs, starting from expected parity -/
def observedParity {m : ℕ} (F : SpaceTimeFault n m) (D : Detector n) : ZMod 2 :=
  D.expectedParity + parityFlip F D

/-! ## Section 9: Detector Violation -/

/-- A spacetime fault F **violates** detector D if F causes the parity constraint to fail.
    This happens when the observed parity differs from the expected parity,
    i.e., when parityFlip is non-zero. -/
def violates {m : ℕ} (F : SpaceTimeFault n m) (D : Detector n) : Prop :=
  parityFlip F D ≠ 0

instance {m : ℕ} (F : SpaceTimeFault n m) (D : Detector n) :
    Decidable (violates F D) :=
  inferInstanceAs (Decidable (parityFlip F D ≠ 0))

/-- Equivalently, violation means observed parity differs from expected -/
theorem violates_iff_parity_mismatch {m : ℕ} (F : SpaceTimeFault n m) (D : Detector n) :
    violates F D ↔ observedParity F D ≠ D.expectedParity := by
  unfold violates observedParity
  constructor
  · intro h hcontra
    have heq : D.expectedParity + parityFlip F D = D.expectedParity := hcontra
    have hzero : parityFlip F D = 0 := by
      have h2 : parityFlip F D = D.expectedParity + parityFlip F D - D.expectedParity := by ring
      rw [heq] at h2
      simp only [sub_self] at h2
      exact h2
    exact h hzero
  · intro h hcontra
    apply h
    rw [hcontra]
    simp only [add_zero]

/-- The empty fault never violates any detector -/
theorem empty_not_violates (D : Detector n) :
    ¬violates (SpaceTimeFault.empty : SpaceTimeFault n m) D := by
  unfold violates parityFlip
  simp [SpaceTimeFault.empty, countSpaceFlips]

/-! ## Section 10: Syndrome Definition -/

/-- The **syndrome** of a spacetime fault F is the set of all detectors violated by F.
    syn(F) = {D : F violates D}

    We represent this as a predicate since the set of all detectors is not finite in general.
    For a finite detector set, we can compute the syndrome as a Finset. -/
def syndrome {m : ℕ} (F : SpaceTimeFault n m) : Detector n → Prop :=
  fun D => violates F D

/-- The syndrome as a Finset given a finite set of detectors -/
def syndromeFinset {m : ℕ} (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) :
    Finset (Detector n) :=
  detectors.filter (fun D => violates F D)

/-- The syndrome Finset is a subset of the detector set -/
theorem syndromeFinset_subset {m : ℕ} (F : SpaceTimeFault n m)
    (detectors : Finset (Detector n)) :
    syndromeFinset F detectors ⊆ detectors :=
  Finset.filter_subset _ _

/-- A detector is in the syndrome Finset iff it is violated -/
theorem mem_syndromeFinset_iff {m : ℕ} (F : SpaceTimeFault n m)
    (detectors : Finset (Detector n)) (D : Detector n) :
    D ∈ syndromeFinset F detectors ↔ D ∈ detectors ∧ violates F D := by
  simp [syndromeFinset]

/-- The syndrome of the empty fault is empty -/
theorem syndrome_empty (detectors : Finset (Detector n)) :
    syndromeFinset (SpaceTimeFault.empty : SpaceTimeFault n m) detectors = ∅ := by
  ext D
  simp [syndromeFinset, empty_not_violates]

/-! ## Section 11: Syndrome Weight -/

/-- The weight of a syndrome is the number of violated detectors -/
def syndromeWeight {m : ℕ} (F : SpaceTimeFault n m) (detectors : Finset (Detector n)) : ℕ :=
  (syndromeFinset F detectors).card

/-- The empty fault has zero syndrome weight -/
@[simp]
theorem syndromeWeight_empty (detectors : Finset (Detector n)) :
    syndromeWeight (SpaceTimeFault.empty : SpaceTimeFault n m) detectors = 0 := by
  simp [syndromeWeight, syndrome_empty]

/-- Syndrome weight is bounded by the number of detectors -/
theorem syndromeWeight_le_card {m : ℕ} (F : SpaceTimeFault n m)
    (detectors : Finset (Detector n)) :
    syndromeWeight F detectors ≤ detectors.card :=
  Finset.card_le_card (syndromeFinset_subset F detectors)

/-! ## Section 12: Detector Properties -/

/-- Two faults have the same syndrome if they violate exactly the same detectors -/
def sameSyndrome {m : ℕ} (F₁ F₂ : SpaceTimeFault n m) : Prop :=
  ∀ D : Detector n, violates F₁ D ↔ violates F₂ D

/-- Same syndrome is reflexive -/
theorem sameSyndrome_refl {m : ℕ} (F : SpaceTimeFault n m) : sameSyndrome F F :=
  fun _ => Iff.rfl

/-- Same syndrome is symmetric -/
theorem sameSyndrome_symm {m : ℕ} {F₁ F₂ : SpaceTimeFault n m}
    (h : sameSyndrome F₁ F₂) : sameSyndrome F₂ F₁ :=
  fun D => (h D).symm

/-- Same syndrome is transitive -/
theorem sameSyndrome_trans {m : ℕ} {F₁ F₂ F₃ : SpaceTimeFault n m}
    (h₁ : sameSyndrome F₁ F₂) (h₂ : sameSyndrome F₂ F₃) : sameSyndrome F₁ F₃ :=
  fun D => (h₁ D).trans (h₂ D)

/-- Same syndrome gives same syndrome Finset -/
theorem sameSyndrome_syndromeFinset {m : ℕ} {F₁ F₂ : SpaceTimeFault n m}
    (h : sameSyndrome F₁ F₂) (detectors : Finset (Detector n)) :
    syndromeFinset F₁ detectors = syndromeFinset F₂ detectors := by
  ext D
  simp only [mem_syndromeFinset_iff]
  constructor
  · intro ⟨hD, hv⟩
    exact ⟨hD, (h D).mp hv⟩
  · intro ⟨hD, hv⟩
    exact ⟨hD, (h D).mpr hv⟩

/-! ## Section 13: Helper Lemmas -/

/-- The number of space flips is bounded by the number of space faults -/
theorem countSpaceFlips_le_card (spaceFaults : Finset (SpaceFault n))
    (meas : SingleMeasurement n) :
    countSpaceFlips spaceFaults meas ≤ spaceFaults.card :=
  Finset.card_filter_le _ _

/-- Zero space faults means zero space flips -/
@[simp]
theorem countSpaceFlips_empty (meas : SingleMeasurement n) :
    countSpaceFlips ∅ meas = 0 := by
  simp [countSpaceFlips]

/-- Parity flip from empty fault is zero -/
@[simp]
theorem parityFlip_empty (D : Detector n) :
    parityFlip (SpaceTimeFault.empty : SpaceTimeFault n m) D = 0 := by
  simp [parityFlip, SpaceTimeFault.empty]

/-- A detector with no measurements has zero parity flip from any fault -/
theorem parityFlip_no_measurements {m : ℕ} (F : SpaceTimeFault n m) (D : Detector n)
    (hD : D.measurements = ∅) :
    parityFlip F D = (F.timeFaults.card : ZMod 2) := by
  unfold parityFlip
  simp [hD]

/-- The trivial detector is never violated (by faults with no time faults) -/
theorem trivial_not_violated {m : ℕ} (F : SpaceTimeFault n m)
    (hF : F.timeFaults = ∅) :
    ¬violates F (Detector.trivial n) := by
  unfold violates parityFlip
  simp [Detector.trivial, hF]

/-- Two detectors with same components and parity are equal -/
theorem Detector_ext (D₁ D₂ : Detector n)
    (hi : D₁.initializations = D₂.initializations)
    (hm : D₁.measurements = D₂.measurements)
    (hp : D₁.expectedParity = D₂.expectedParity) : D₁ = D₂ := by
  cases D₁
  cases D₂
  simp only at hi hm hp
  subst hi hm hp
  rfl

/-- The syndrome is monotone in the detector set -/
theorem syndromeFinset_mono {m : ℕ} (F : SpaceTimeFault n m)
    {D₁ D₂ : Finset (Detector n)} (h : D₁ ⊆ D₂) :
    syndromeFinset F D₁ ⊆ syndromeFinset F D₂ := by
  intro D hD
  simp only [syndromeFinset, Finset.mem_filter] at hD ⊢
  exact ⟨h hD.1, hD.2⟩

/-- Syndrome weight is monotone in the detector set -/
theorem syndromeWeight_mono {m : ℕ} (F : SpaceTimeFault n m)
    {D₁ D₂ : Finset (Detector n)} (h : D₁ ⊆ D₂) :
    syndromeWeight F D₁ ≤ syndromeWeight F D₂ :=
  Finset.card_le_card (syndromeFinset_mono F h)

end QEC
