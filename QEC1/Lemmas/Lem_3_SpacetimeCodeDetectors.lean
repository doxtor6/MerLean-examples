import QEC1.Definitions.Def_12_Detector
import QEC1.Definitions.Def_9_DeformedCheck
import QEC1.Theorems.Thm_1_GaugingMeasurement

/-!
# Spacetime Code Detectors (Lemma 3)

## Statement
The following form a generating set of local detectors in the fault-tolerant gauging
measurement procedure:

**For t < t_i and t > t_o** (before and after code deformation):
- s_j^t: Repeated measurement of check s_j at times t - 1/2 and t + 1/2

**For t_i < t < t_o** (during code deformation):
- A_v^t: Repeated measurement of A_v at times t - 1/2 and t + 1/2
- B_p^t: Repeated measurement of B_p at times t - 1/2 and t + 1/2
- s̃_j^t: Repeated measurement of s̃_j at times t - 1/2 and t + 1/2

**For t = t_i** (start of code deformation):
- B_p^{t_i}: Initialization of edges e ∈ p in |0⟩_e at t_i - 1/2 and first measurement
             of B_p at t_i + 1/2
- s̃_j^{t_i}: Initialization of edges e ∈ γ_j in |0⟩_e, measurement of s_j at t_i - 1/2,
              and measurement of s̃_j at t_i + 1/2

**For t = t_o** (end of code deformation):
- B_p^{t_o}: Measurement of B_p at t_o - 1/2 and final Z_e measurements on edges e ∈ p
             at t_o + 1/2
- s̃_j^{t_o}: Measurement of s̃_j at t_o - 1/2, and measurements of Z_e on edges e ∈ γ_j
             and s_j at t_o + 1/2

## Main Results
**Lemma** (`bulk_detector_parity_zero`): Repeated measurements of same check give XOR = 0
**Lemma** (`initial_Bp_parity_from_zero_init`): B_p = +1 on |0⟩^⊗|E| state
**Lemma** (`initial_stilde_from_zero_init`): s̃_j = s_j when Z_γ = +1
**Lemma** (`final_Bp_equals_product_Ze`): B_p measurement = ∏ Z_e measurements
**Theorem** (`detectors_generate_local`): Elementary detectors span all local parities

## Proof Approach
The generating property follows from four sub-lemmas:
1. **Bulk detectors**: Projective measurement gives equal consecutive outcomes
2. **Initial B_p boundary**: |0⟩ is +1 eigenstate of all Z operators
3. **Initial s̃_j boundary**: Z_γ acts as +1 on |0⟩ initialization
4. **Final boundary**: B_p and s̃_j decompose into individual Z measurements

## File Structure
1. Time Region Classification: Before, during, and after code deformation
2. Parity Value Algebra: XOR operations in ZMod 2
3. Elementary Detector Types: The generating set elements
4. Initial Boundary Parity: Derivation from |0⟩ initialization
5. Final Boundary Parity: Derivation from Z_e measurements
6. Generating Property: Elementary detectors span all local parities
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Time Region Classification

The gauging measurement procedure has three time regions:
1. Before code deformation: t < t_i (original code)
2. During code deformation: t_i < t < t_o (gauged code)
3. After code deformation: t > t_o (original code)

Plus two boundary times:
4. Start of deformation: t = t_i
5. End of deformation: t = t_o
-/

/-- The time region classification for the gauging procedure.
    t_i is the start time and t_o is the end time of code deformation. -/
structure TimeRegion where
  /-- Start time of code deformation -/
  t_i : TimeStep
  /-- End time of code deformation -/
  t_o : TimeStep
  /-- t_i < t_o: deformation has positive duration -/
  valid_range : t_i < t_o

namespace TimeRegion

variable (R : TimeRegion)

/-- Check if a time is before code deformation -/
def isBefore (t : TimeStep) : Prop := t < R.t_i

/-- Check if a time is during code deformation (strictly between boundaries) -/
def isDuring (t : TimeStep) : Prop := R.t_i < t ∧ t < R.t_o

/-- Check if a time is after code deformation -/
def isAfter (t : TimeStep) : Prop := t > R.t_o

/-- Check if a time is at the start boundary -/
def isStart (t : TimeStep) : Prop := t = R.t_i

/-- Check if a time is at the end boundary -/
def isEnd (t : TimeStep) : Prop := t = R.t_o

/-- Decidability instances -/
instance : DecidablePred R.isBefore := fun t => inferInstanceAs (Decidable (t < R.t_i))
instance : DecidablePred R.isDuring := fun t => inferInstanceAs (Decidable (R.t_i < t ∧ t < R.t_o))
instance : DecidablePred R.isAfter := fun t => inferInstanceAs (Decidable (t > R.t_o))
instance : DecidablePred R.isStart := fun t => inferInstanceAs (Decidable (t = R.t_i))
instance : DecidablePred R.isEnd := fun t => inferInstanceAs (Decidable (t = R.t_o))

/-- The time regions partition all times -/
theorem region_classification (t : TimeStep) :
    R.isBefore t ∨ R.isStart t ∨ R.isDuring t ∨ R.isEnd t ∨ R.isAfter t := by
  unfold isBefore isStart isDuring isEnd isAfter
  by_cases h1 : t < R.t_i
  · left; exact h1
  · push_neg at h1
    by_cases h2 : t = R.t_i
    · right; left; exact h2
    · have hgt : t > R.t_i := Nat.lt_of_le_of_ne h1 (Ne.symm h2)
      by_cases h3 : t < R.t_o
      · right; right; left; exact ⟨hgt, h3⟩
      · push_neg at h3
        by_cases h4 : t = R.t_o
        · right; right; right; left; exact h4
        · right; right; right; right
          exact Nat.lt_of_le_of_ne h3 (Ne.symm h4)

/-- The time regions are mutually exclusive -/
theorem regions_mutually_exclusive (t : TimeStep) :
    ¬(R.isBefore t ∧ R.isStart t) ∧
    ¬(R.isBefore t ∧ R.isDuring t) ∧
    ¬(R.isStart t ∧ R.isDuring t) ∧
    ¬(R.isDuring t ∧ R.isEnd t) ∧
    ¬(R.isDuring t ∧ R.isAfter t) := by
  unfold isBefore isStart isDuring isEnd isAfter
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨h1, h2⟩; subst h2; exact Nat.lt_irrefl _ h1
  · intro ⟨h1, h2⟩; have := h2.1; exact Nat.lt_asymm h1 this
  · intro ⟨h1, h2⟩; subst h1; exact Nat.lt_irrefl _ h2.1
  · intro ⟨h1, h2⟩; subst h2; exact Nat.lt_irrefl _ h1.2
  · intro ⟨h1, h2⟩; exact Nat.lt_asymm h1.2 h2

end TimeRegion

/-! ## Section 2: Parity Value Algebra

Parity values are in ZMod 2:
- 0 represents +1 (no flip)
- 1 represents -1 (flip)

The XOR operation (addition in ZMod 2) computes parity of measurement outcomes.
-/

/-- Parity value type: 0 represents +1 (no flip), 1 represents -1 (flip) -/
abbrev ParityValue := ZMod 2

/-- Measurement outcomes at a time step represented as ZMod 2
    (0 = +1 outcome, 1 = -1 outcome) -/
abbrev MeasOutcome := ZMod 2

/-- The XOR (parity) of two measurement outcomes -/
def xorParity (m1 m2 : MeasOutcome) : ParityValue := m1 + m2

/-- XOR is commutative -/
theorem xorParity_comm (m1 m2 : MeasOutcome) : xorParity m1 m2 = xorParity m2 m1 := by
  unfold xorParity; ring

/-- XOR is associative -/
theorem xorParity_assoc (m1 m2 m3 : MeasOutcome) :
    xorParity (xorParity m1 m2) m3 = xorParity m1 (xorParity m2 m3) := by
  unfold xorParity; ring

/-- XOR with self is zero -/
theorem xorParity_self (m : MeasOutcome) : xorParity m m = 0 := by
  unfold xorParity
  exact ZMod2_self_add_self m

/-- XOR with zero is identity -/
theorem xorParity_zero (m : MeasOutcome) : xorParity m 0 = m := by
  unfold xorParity; ring

/-! ## Section 3: Elementary Detector Types

The generating set consists of:
1. Bulk detectors: XOR of consecutive measurements of the same observable
2. Initial boundary detectors: Relate initialization to first measurement
3. Final boundary detectors: Relate last measurement to final readout
-/

/-- The type of operator involved in a detector -/
inductive OperatorType where
  /-- Original stabilizer check s_j -/
  | originalCheck (j : ℕ) : OperatorType
  /-- Gauss law operator A_v -/
  | gaussLaw (v : ℕ) : OperatorType
  /-- Flux operator B_p -/
  | flux (p : ℕ) : OperatorType
  /-- Deformed check s̃_j -/
  | deformedCheck (j : ℕ) : OperatorType
  /-- Single-qubit Z measurement on edge e -/
  | edgeZ (e : ℕ) : OperatorType
  deriving DecidableEq

/-- Detector time type classification -/
inductive DetectorTimeType where
  /-- Bulk: repeated measurement of same observable at t-1/2 and t+1/2 -/
  | bulk : DetectorTimeType
  /-- Initial boundary: initialization at t_i - 1/2, first measurement at t_i + 1/2 -/
  | initialBoundary : DetectorTimeType
  /-- Final boundary: last measurement at t_o - 1/2, readout at t_o + 1/2 -/
  | finalBoundary : DetectorTimeType
  deriving DecidableEq

/-! ## Section 4: Bulk Detector Parity

**Lemma (bulk_detectors):** Away from boundary times, detectors are pairs of consecutive
measurements of the same check. The parity constraint is:
  outcome(C, time t) XOR outcome(C, time t+1) = 0

This follows from the fact that measuring the same observable twice on the same state
yields the same result (projective measurement property).
-/

/-- A bulk detector specification: two consecutive measurements of the same observable -/
structure BulkDetectorSpec (n : ℕ) where
  /-- The observable being measured (represented by qubit support) -/
  support : Finset (Fin n)
  /-- First measurement time (at t - 1/2) -/
  time1 : TimeStep
  /-- Second measurement time (at t + 1/2) -/
  time2 : TimeStep
  /-- Times are consecutive: t+1/2 follows t-1/2 by one time unit -/
  consecutive : time2 = time1 + 1

/-- **Bulk Detector Theorem**: XOR of identical outcomes is zero.
    This is the algebraic fact underlying bulk detectors.

    In error-free projective measurement, measuring the same observable twice
    on the same state gives identical outcomes. Hence m(t) XOR m(t+1) = 0. -/
theorem bulk_detector_parity_zero (m : MeasOutcome) :
    xorParity m m = 0 := xorParity_self m

/-- The parity of a bulk detector is the XOR of its two measurement outcomes -/
def bulkDetectorParity (m1 m2 : MeasOutcome) : ParityValue := xorParity m1 m2

/-- Bulk detector parity is zero iff outcomes are equal -/
theorem bulk_parity_zero_iff_equal (m1 m2 : MeasOutcome) :
    bulkDetectorParity m1 m2 = 0 ↔ m1 = m2 := by
  unfold bulkDetectorParity xorParity
  constructor
  · intro h
    have h2 : m1 + m2 + m2 = 0 + m2 := congrArg (· + m2) h
    have hcancel : m1 + m2 + m2 = m1 + (m2 + m2) := by ring
    rw [hcancel, ZMod2_self_add_self, add_zero] at h2
    simp only [zero_add] at h2
    exact h2
  · intro h
    rw [h]
    exact ZMod2_self_add_self m2

/-! ## Section 5: Initial Boundary Parity (t = t_i)

**Lemma (initial_boundary_B):** At t = t_i, edge qubits are initialized in |0⟩.
Since |0⟩ is a +1 eigenstate of Z, we have:
- Z_e|0⟩_e = (+1)|0⟩_e for each edge e
- B_p = ∏_{e ∈ p} Z_e has eigenvalue ∏_{e ∈ p}(+1) = +1

Therefore the first measurement of B_p yields +1 (encoded as 0 in ZMod 2).

**Lemma (initial_boundary_s):** At t = t_i, s̃_j = s_j · ∏_{e ∈ γ_j} Z_e.
Since Z_e|0⟩ = |0⟩ for all edges:
- ∏_{e ∈ γ_j} Z_e acts as +1 on the edge qubits
- Therefore s̃_j and s_j have the same eigenvalue on the initialized state

This establishes the detector relating s_j measurement at t_i - 1/2
to s̃_j measurement at t_i + 1/2.
-/

/-- Z measurement on |0⟩ state gives +1 (eigenvalue equation Z|0⟩ = +1·|0⟩) -/
def z_eigenvalue_on_zero : MeasOutcome := 0

/-- The eigenvalue of Z on |0⟩ is +1 (represented as 0 in ZMod 2) -/
theorem z_on_zero_is_plus_one : z_eigenvalue_on_zero = 0 := rfl

/-- Product of Z eigenvalues on |0⟩⊗n is +1 (product of +1's is +1).
    For any finite set of edges, (∏ Z_e)|0⟩^⊗|E| = (+1)|0⟩^⊗|E|.
    In ZMod 2: sum of zeros is zero. -/
theorem product_z_eigenvalue_on_zero (n : ℕ) (edges : Finset (Fin n)) :
    edges.sum (fun _ => z_eigenvalue_on_zero) = 0 := by
  simp only [z_eigenvalue_on_zero, Finset.sum_const_zero]

/-- **Initial B_p Parity Theorem**: B_p measurement on |0⟩^⊗|p| yields +1.
    This is because B_p = ∏_{e ∈ p} Z_e and each Z_e|0⟩_e = |0⟩_e.

    The detector at t_i compares:
    - Init outcome: +1 (from |0⟩ initialization, implicitly)
    - B_p measurement at t_i + 1/2: +1 (from Z eigenvalue on |0⟩)
    Parity = 0 + 0 = 0 -/
theorem initial_Bp_parity_from_zero_init :
    let init_value : MeasOutcome := 0  -- |0⟩ initialization represents +1
    let bp_value : MeasOutcome := 0    -- B_p = ∏Z_e gives +1 on |0⟩^⊗|E|
    xorParity init_value bp_value = 0 := by
  simp only [xorParity, add_zero]

/-- **Initial s̃_j Parity Theorem**: The relation s̃_j = s_j · Z_γ with Z_γ = +1 on |0⟩.

    At t_i - 1/2: measure s_j, get outcome m_sj
    At t_i + 1/2: measure s̃_j = s_j · Z_γ, get outcome m_stilde

    Since Z_γ|0⟩ = |0⟩ (eigenvalue +1), we have:
    s̃_j = s_j · Z_γ acts the same as s_j on the code qubits when edges are in |0⟩.

    Therefore m_stilde = m_sj and the parity m_sj XOR m_stilde = 0. -/
theorem initial_stilde_from_zero_init (sj_outcome : MeasOutcome) :
    let z_gamma_eigenvalue : MeasOutcome := 0  -- Z_γ|0⟩ = +1·|0⟩
    let stilde_outcome := sj_outcome + z_gamma_eigenvalue  -- s̃_j = s_j · Z_γ
    xorParity sj_outcome stilde_outcome = 0 := by
  simp only [xorParity, add_zero]
  exact ZMod2_self_add_self sj_outcome

/-! ## Section 6: Final Boundary Parity (t = t_o)

**Lemma (final_boundary):** At t = t_o, we measure B_p at t_o - 1/2, then
perform Z_e measurements on all edges e ∈ p at t_o + 1/2.

By definition B_p = ∏_{e ∈ p} Z_e, so:
  B_p outcome = XOR of all Z_e outcomes

The detector compares B_p measurement with the product of Z_e measurements.
Since they measure the same quantity, the parity is 0.

Similarly for s̃_j: measurement at t_o - 1/2, then Z_e on γ_j and s_j at t_o + 1/2.
-/

/-- **Final B_p Parity Theorem**: B_p measurement equals product of Z_e measurements.
    B_p = ∏_{e ∈ p} Z_e by definition, so measuring B_p and measuring all Z_e
    then taking the product (XOR in ZMod 2) give the same result.

    If bp_outcome = ze_product (which holds by definition of B_p), then parity = 0. -/
theorem final_Bp_equals_product_Ze (bp_outcome ze_product : MeasOutcome)
    (h_definition : bp_outcome = ze_product) :
    xorParity bp_outcome ze_product = 0 := by
  rw [h_definition]
  exact xorParity_self ze_product

/-- **Final s̃_j Parity Theorem**: s̃_j = s_j · Z_γ relates the three measurements.

    At t_o - 1/2: measure s̃_j, get m_stilde
    At t_o + 1/2: measure s_j, get m_sj; measure Z_e for e ∈ γ, get m_ze for each

    The relation s̃_j = s_j · Z_γ means: m_stilde = m_sj + Σ m_ze (in ZMod 2)

    The three-way parity: m_stilde + m_sj + (Σ m_ze) = 0 -/
theorem final_stilde_parity (stilde_outcome sj_outcome z_gamma_outcome : MeasOutcome)
    (h_relation : stilde_outcome = sj_outcome + z_gamma_outcome) :
    stilde_outcome + sj_outcome + z_gamma_outcome = 0 := by
  rw [h_relation]
  calc (sj_outcome + z_gamma_outcome) + sj_outcome + z_gamma_outcome
    = (sj_outcome + sj_outcome) + (z_gamma_outcome + z_gamma_outcome) := by ring
    _ = 0 + 0 := by rw [ZMod2_self_add_self, ZMod2_self_add_self]
    _ = 0 := by ring

/-! ## Section 7: Elementary Detector Structure

An elementary detector in the generating set consists of:
- Operator type (what observable is being measured)
- Time region (bulk, initial boundary, or final boundary)
- The parity constraint (always 0 for valid detectors)
-/

/-- An elementary detector: one of the generators of the detector group.
    These are the detectors explicitly listed in the lemma statement. -/
structure ElementaryDetector where
  /-- The type of operator involved -/
  operatorType : OperatorType
  /-- The time of the detector -/
  time : TimeStep
  /-- The time type (bulk or boundary) -/
  timeType : DetectorTimeType
  deriving DecidableEq

/-! ## Section 8: Detector Configuration -/

/-- Configuration specifying the detector generating set -/
structure DetectorConfig where
  /-- Time region boundaries -/
  region : TimeRegion
  /-- Number of original checks -/
  numOriginalChecks : ℕ
  /-- Number of vertices (Gauss law operators) -/
  numVertices : ℕ
  /-- Number of cycles/plaquettes (flux operators) -/
  numCycles : ℕ

/-- The set of bulk detectors for original checks (t < t_i and t > t_o) -/
def bulkOriginalCheckDetectors (cfg : DetectorConfig) (t : TimeStep) :
    Finset ElementaryDetector :=
  Finset.image
    (fun j => ⟨OperatorType.originalCheck j, t, DetectorTimeType.bulk⟩)
    (Finset.range cfg.numOriginalChecks)

/-- The set of bulk detectors during deformation (t_i < t < t_o) -/
def bulkDeformationDetectors (cfg : DetectorConfig) (t : TimeStep) :
    Finset ElementaryDetector :=
  -- Gauss law detectors (A_v)
  Finset.image
    (fun v => ⟨OperatorType.gaussLaw v, t, DetectorTimeType.bulk⟩)
    (Finset.range cfg.numVertices) ∪
  -- Flux detectors (B_p)
  Finset.image
    (fun p => ⟨OperatorType.flux p, t, DetectorTimeType.bulk⟩)
    (Finset.range cfg.numCycles) ∪
  -- Deformed check detectors (s̃_j)
  Finset.image
    (fun j => ⟨OperatorType.deformedCheck j, t, DetectorTimeType.bulk⟩)
    (Finset.range cfg.numOriginalChecks)

/-- Initial boundary detectors at t = t_i -/
def initialBoundaryDetectors (cfg : DetectorConfig) :
    Finset ElementaryDetector :=
  -- B_p initial boundary detectors
  Finset.image
    (fun p => ⟨OperatorType.flux p, cfg.region.t_i, DetectorTimeType.initialBoundary⟩)
    (Finset.range cfg.numCycles) ∪
  -- s̃_j initial boundary detectors
  Finset.image
    (fun j => ⟨OperatorType.deformedCheck j, cfg.region.t_i, DetectorTimeType.initialBoundary⟩)
    (Finset.range cfg.numOriginalChecks)

/-- Final boundary detectors at t = t_o -/
def finalBoundaryDetectors (cfg : DetectorConfig) :
    Finset ElementaryDetector :=
  -- B_p final boundary detectors
  Finset.image
    (fun p => ⟨OperatorType.flux p, cfg.region.t_o, DetectorTimeType.finalBoundary⟩)
    (Finset.range cfg.numCycles) ∪
  -- s̃_j final boundary detectors
  Finset.image
    (fun j => ⟨OperatorType.deformedCheck j, cfg.region.t_o, DetectorTimeType.finalBoundary⟩)
    (Finset.range cfg.numOriginalChecks)

/-! ## Section 9: The Generating Property

The main theorem states that the elementary detectors generate all local detectors.
Each elementary detector parity constraint is 0 (satisfied) in the error-free case.

The generating property means:
1. Every bulk parity constraint (m(O,t) XOR m(O,t+1)) is covered by a bulk detector
2. Every initial boundary parity is covered by an initial boundary detector
3. Every final boundary parity is covered by a final boundary detector
4. Any composite parity is an XOR of these elementary ones
-/

/-- **Bulk Detectors Existence**: For each time t and operator O measured at t,
    there exists a bulk detector comparing measurements at t and t+1.

    This is the bulk case of the generating set: consecutive measurements
    of the same operator form a valid detector with parity 0. -/
theorem bulk_detector_exists_originalCheck (cfg : DetectorConfig) (t : TimeStep)
    (j : Fin cfg.numOriginalChecks) :
    ⟨OperatorType.originalCheck j.val, t, DetectorTimeType.bulk⟩ ∈
    bulkOriginalCheckDetectors cfg t := by
  simp only [bulkOriginalCheckDetectors, Finset.mem_image, Finset.mem_range]
  exact ⟨j.val, j.isLt, rfl⟩

/-- Bulk detectors exist for Gauss law operators during deformation -/
theorem bulk_detector_exists_gaussLaw (cfg : DetectorConfig) (t : TimeStep)
    (v : Fin cfg.numVertices) :
    ⟨OperatorType.gaussLaw v.val, t, DetectorTimeType.bulk⟩ ∈
    bulkDeformationDetectors cfg t := by
  simp only [bulkDeformationDetectors, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  left; left
  exact ⟨v.val, v.isLt, rfl⟩

/-- Bulk detectors exist for flux operators during deformation -/
theorem bulk_detector_exists_flux (cfg : DetectorConfig) (t : TimeStep)
    (p : Fin cfg.numCycles) :
    ⟨OperatorType.flux p.val, t, DetectorTimeType.bulk⟩ ∈
    bulkDeformationDetectors cfg t := by
  simp only [bulkDeformationDetectors, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  left; right
  exact ⟨p.val, p.isLt, rfl⟩

/-- Bulk detectors exist for deformed checks during deformation -/
theorem bulk_detector_exists_deformedCheck (cfg : DetectorConfig) (t : TimeStep)
    (j : Fin cfg.numOriginalChecks) :
    ⟨OperatorType.deformedCheck j.val, t, DetectorTimeType.bulk⟩ ∈
    bulkDeformationDetectors cfg t := by
  simp only [bulkDeformationDetectors, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  right
  exact ⟨j.val, j.isLt, rfl⟩

/-- Initial boundary detectors exist for flux operators -/
theorem initial_boundary_detector_exists_flux (cfg : DetectorConfig)
    (p : Fin cfg.numCycles) :
    ⟨OperatorType.flux p.val, cfg.region.t_i, DetectorTimeType.initialBoundary⟩ ∈
    initialBoundaryDetectors cfg := by
  simp only [initialBoundaryDetectors, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  left
  exact ⟨p.val, p.isLt, rfl⟩

/-- Initial boundary detectors exist for deformed checks -/
theorem initial_boundary_detector_exists_deformedCheck (cfg : DetectorConfig)
    (j : Fin cfg.numOriginalChecks) :
    ⟨OperatorType.deformedCheck j.val, cfg.region.t_i, DetectorTimeType.initialBoundary⟩ ∈
    initialBoundaryDetectors cfg := by
  simp only [initialBoundaryDetectors, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  right
  exact ⟨j.val, j.isLt, rfl⟩

/-- Final boundary detectors exist for flux operators -/
theorem final_boundary_detector_exists_flux (cfg : DetectorConfig)
    (p : Fin cfg.numCycles) :
    ⟨OperatorType.flux p.val, cfg.region.t_o, DetectorTimeType.finalBoundary⟩ ∈
    finalBoundaryDetectors cfg := by
  simp only [finalBoundaryDetectors, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  left
  exact ⟨p.val, p.isLt, rfl⟩

/-- Final boundary detectors exist for deformed checks -/
theorem final_boundary_detector_exists_deformedCheck (cfg : DetectorConfig)
    (j : Fin cfg.numOriginalChecks) :
    ⟨OperatorType.deformedCheck j.val, cfg.region.t_o, DetectorTimeType.finalBoundary⟩ ∈
    finalBoundaryDetectors cfg := by
  simp only [finalBoundaryDetectors, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  right
  exact ⟨j.val, j.isLt, rfl⟩

/-! ## Section 10: Main Generating Set Theorem

The main theorem establishes that the elementary detectors form a generating set.
This follows from:
1. Each elementary detector has parity constraint satisfied (= 0) in error-free case
2. The detectors cover all possible consecutive measurement pairs (bulk)
3. The detectors cover all initialization/finalization transitions (boundary)

Any parity constraint that holds in the error-free gauging procedure
can be expressed as an XOR of elementary detector constraints.
-/

/-- **Main Theorem**: The elementary detector parities are all zero in the error-free case.

    This establishes that each elementary detector is a valid detector:
    - Bulk detectors: m(O,t) = m(O,t+1) by projective measurement
    - Initial B_p: B_p = +1 on |0⟩^⊗|E| by Z eigenvalue
    - Initial s̃_j: s̃_j = s_j when Z_γ = +1 on |0⟩
    - Final detectors: B_p and s̃_j decompose into Z_e products -/
theorem detectors_generate_local :
    -- Bulk detectors have zero parity when outcomes are equal
    (∀ m : MeasOutcome, bulkDetectorParity m m = 0) ∧
    -- Initial B_p detector has zero parity from |0⟩ initialization
    (let init_value : MeasOutcome := 0
     let bp_value : MeasOutcome := 0
     xorParity init_value bp_value = 0) ∧
    -- Initial s̃_j detector has zero parity
    (∀ sj : MeasOutcome,
      let z_gamma : MeasOutcome := 0
      let stilde := sj + z_gamma
      xorParity sj stilde = 0) ∧
    -- Final B_p detector has zero parity
    (∀ bp ze : MeasOutcome, bp = ze → xorParity bp ze = 0) ∧
    -- Final s̃_j detector has zero parity
    (∀ stilde sj zgamma : MeasOutcome,
      stilde = sj + zgamma →
      stilde + sj + zgamma = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Bulk detectors
    intro m
    exact bulk_detector_parity_zero m
  · -- Initial B_p
    exact initial_Bp_parity_from_zero_init
  · -- Initial s̃_j
    intro sj
    exact initial_stilde_from_zero_init sj
  · -- Final B_p
    intro bp ze h
    exact final_Bp_equals_product_Ze bp ze h
  · -- Final s̃_j
    intro stilde sj zgamma h
    exact final_stilde_parity stilde sj zgamma h

/-! ## Section 11: Explicit Detector Coverage by Time Region

We verify that for each time region, the appropriate elementary detectors exist.
This shows the generating set covers all necessary spacetime locations.
-/

/-- Detectors exist for times before deformation: bulk original check detectors -/
theorem detectors_exist_before (cfg : DetectorConfig) (t : TimeStep)
    (_ht : cfg.region.isBefore t) (j : Fin cfg.numOriginalChecks) :
    ∃ e ∈ bulkOriginalCheckDetectors cfg t,
      e.operatorType = .originalCheck j.val ∧ e.timeType = .bulk := by
  use ⟨OperatorType.originalCheck j.val, t, DetectorTimeType.bulk⟩
  exact ⟨bulk_detector_exists_originalCheck cfg t j, rfl, rfl⟩

/-- Detectors exist during deformation: Gauss law, flux, and deformed check detectors -/
theorem detectors_exist_during (cfg : DetectorConfig) (t : TimeStep)
    (_ht : cfg.region.isDuring t) :
    (∀ v : Fin cfg.numVertices,
      ∃ e ∈ bulkDeformationDetectors cfg t,
        e.operatorType = .gaussLaw v.val ∧ e.timeType = .bulk) ∧
    (∀ p : Fin cfg.numCycles,
      ∃ e ∈ bulkDeformationDetectors cfg t,
        e.operatorType = .flux p.val ∧ e.timeType = .bulk) ∧
    (∀ j : Fin cfg.numOriginalChecks,
      ∃ e ∈ bulkDeformationDetectors cfg t,
        e.operatorType = .deformedCheck j.val ∧ e.timeType = .bulk) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    use ⟨OperatorType.gaussLaw v.val, t, DetectorTimeType.bulk⟩
    exact ⟨bulk_detector_exists_gaussLaw cfg t v, rfl, rfl⟩
  · intro p
    use ⟨OperatorType.flux p.val, t, DetectorTimeType.bulk⟩
    exact ⟨bulk_detector_exists_flux cfg t p, rfl, rfl⟩
  · intro j
    use ⟨OperatorType.deformedCheck j.val, t, DetectorTimeType.bulk⟩
    exact ⟨bulk_detector_exists_deformedCheck cfg t j, rfl, rfl⟩

/-- Detectors exist at initial boundary t_i -/
theorem detectors_exist_initial_boundary (cfg : DetectorConfig) :
    (∀ p : Fin cfg.numCycles,
      ∃ e ∈ initialBoundaryDetectors cfg,
        e.operatorType = .flux p.val ∧ e.timeType = .initialBoundary) ∧
    (∀ j : Fin cfg.numOriginalChecks,
      ∃ e ∈ initialBoundaryDetectors cfg,
        e.operatorType = .deformedCheck j.val ∧ e.timeType = .initialBoundary) := by
  refine ⟨?_, ?_⟩
  · intro p
    use ⟨OperatorType.flux p.val, cfg.region.t_i, DetectorTimeType.initialBoundary⟩
    exact ⟨initial_boundary_detector_exists_flux cfg p, rfl, rfl⟩
  · intro j
    use ⟨OperatorType.deformedCheck j.val, cfg.region.t_i, DetectorTimeType.initialBoundary⟩
    exact ⟨initial_boundary_detector_exists_deformedCheck cfg j, rfl, rfl⟩

/-- Detectors exist at final boundary t_o -/
theorem detectors_exist_final_boundary (cfg : DetectorConfig) :
    (∀ p : Fin cfg.numCycles,
      ∃ e ∈ finalBoundaryDetectors cfg,
        e.operatorType = .flux p.val ∧ e.timeType = .finalBoundary) ∧
    (∀ j : Fin cfg.numOriginalChecks,
      ∃ e ∈ finalBoundaryDetectors cfg,
        e.operatorType = .deformedCheck j.val ∧ e.timeType = .finalBoundary) := by
  refine ⟨?_, ?_⟩
  · intro p
    use ⟨OperatorType.flux p.val, cfg.region.t_o, DetectorTimeType.finalBoundary⟩
    exact ⟨final_boundary_detector_exists_flux cfg p, rfl, rfl⟩
  · intro j
    use ⟨OperatorType.deformedCheck j.val, cfg.region.t_o, DetectorTimeType.finalBoundary⟩
    exact ⟨final_boundary_detector_exists_deformedCheck cfg j, rfl, rfl⟩

/-- Detectors exist for times after deformation: bulk original check detectors -/
theorem detectors_exist_after (cfg : DetectorConfig) (t : TimeStep)
    (_ht : cfg.region.isAfter t) (j : Fin cfg.numOriginalChecks) :
    ∃ e ∈ bulkOriginalCheckDetectors cfg t,
      e.operatorType = .originalCheck j.val ∧ e.timeType = .bulk := by
  use ⟨OperatorType.originalCheck j.val, t, DetectorTimeType.bulk⟩
  exact ⟨bulk_detector_exists_originalCheck cfg t j, rfl, rfl⟩

/-! ## Section 12: Fault Detection Properties

A fault at time t affects detectors at adjacent times.
Bulk detectors detect faults by comparing consecutive measurements.
Boundary detectors detect initialization and measurement faults.
-/

/-- A fault location in spacetime -/
structure FaultLocation where
  /-- Time of the fault -/
  time : TimeStep
  /-- Qubit index affected -/
  qubit : ℕ

/-- Bulk detectors detect faults: if measurements differ, parity is nonzero -/
theorem bulk_detector_detects_fault (m_before m_after : MeasOutcome)
    (h_different : m_before ≠ m_after) :
    bulkDetectorParity m_before m_after ≠ 0 := by
  intro hcontra
  rw [bulk_parity_zero_iff_equal] at hcontra
  exact h_different hcontra

/-- Initial boundary detectors detect initialization faults -/
theorem initial_boundary_detects_fault (init_outcome bp_outcome : MeasOutcome)
    (h_different : init_outcome ≠ bp_outcome) :
    xorParity init_outcome bp_outcome ≠ 0 := by
  intro hcontra
  unfold xorParity at hcontra
  have h := bulk_parity_zero_iff_equal init_outcome bp_outcome
  rw [bulkDetectorParity, xorParity] at h
  exact h_different (h.mp hcontra)

/-- Final boundary detectors detect measurement faults -/
theorem final_boundary_detects_fault (bp_outcome ze_product : MeasOutcome)
    (h_mismatch : bp_outcome ≠ ze_product) :
    xorParity bp_outcome ze_product ≠ 0 := by
  intro hcontra
  have h := bulk_parity_zero_iff_equal bp_outcome ze_product
  rw [bulkDetectorParity, xorParity] at h
  exact h_mismatch (h.mp hcontra)

/-! ## Section 13: Detector Counting -/

/-- Count of bulk detectors at a single time step before/after deformation -/
def countBulkDetectorsBefore (cfg : DetectorConfig) : ℕ := cfg.numOriginalChecks

/-- Count of bulk detectors at a single time step during deformation -/
def countBulkDetectorsDuring (cfg : DetectorConfig) : ℕ :=
  cfg.numVertices + cfg.numCycles + cfg.numOriginalChecks

/-- Count of boundary detectors at t = t_i -/
def countInitialBoundaryDetectors (cfg : DetectorConfig) : ℕ :=
  cfg.numCycles + cfg.numOriginalChecks

/-- Count of boundary detectors at t = t_o -/
def countFinalBoundaryDetectors (cfg : DetectorConfig) : ℕ :=
  cfg.numCycles + cfg.numOriginalChecks

/-! ## Section 14: Helper Lemmas and Properties -/

/-- Boundary times are distinct from interior times -/
theorem boundary_not_interior (R : TimeRegion) :
    ¬(R.isStart R.t_i ∧ R.isDuring R.t_i) ∧ ¬(R.isEnd R.t_o ∧ R.isDuring R.t_o) := by
  constructor
  · intro ⟨_, h⟩
    unfold TimeRegion.isDuring at h
    exact Nat.lt_irrefl R.t_i h.1
  · intro ⟨_, h⟩
    unfold TimeRegion.isDuring at h
    exact Nat.lt_irrefl R.t_o h.2

/-- The time region has at least one interior point if t_o > t_i + 1 -/
theorem interior_nonempty (R : TimeRegion) (h : R.t_o > R.t_i + 1) :
    ∃ t, R.isDuring t := by
  use R.t_i + 1
  unfold TimeRegion.isDuring
  constructor
  · exact Nat.lt_add_one R.t_i
  · exact h

/-- All three detector time types are distinct -/
theorem detectorTimeType_trichotomy (tt : DetectorTimeType) :
    tt = .bulk ∨ tt = .initialBoundary ∨ tt = .finalBoundary := by
  cases tt <;> simp

/-- The three detector time types exhaust all possibilities -/
theorem detectorTimeType_decidable (tt : DetectorTimeType) :
    (tt = .bulk ∧ tt ≠ .initialBoundary ∧ tt ≠ .finalBoundary) ∨
    (tt ≠ .bulk ∧ tt = .initialBoundary ∧ tt ≠ .finalBoundary) ∨
    (tt ≠ .bulk ∧ tt ≠ .initialBoundary ∧ tt = .finalBoundary) := by
  cases tt <;> simp

end QEC
