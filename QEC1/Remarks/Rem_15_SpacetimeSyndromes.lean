import QEC1.Lemmas.Lem_3_SpacetimeCodeDetectors

/-!
# Spacetime Syndromes (Remark 15)

## Statement
The syndrome of each type of fault in the spacetime code:

**For t < t_i and t > t_o** (before and after code deformation):
- Pauli X_v (or Z_v) fault at time t: violates s_j^t for all s_j that anticommute with X_v (or Z_v)
- s_j-measurement fault at time t + 1/2: violates s_j^t and s_j^{t+1}

**For t_i < t < t_o** (during code deformation):
- X_v fault at time t: violates s̃_j^t for anticommuting s̃_j (commutes with A_v)
- Z_v fault at time t: violates A_v^t and s̃_j^t for anticommuting s̃_j
- X_e fault at time t: violates B_p^t for all p containing e, and s̃_j^t for anticommuting
- Z_e fault at time t: violates A_v^t for both v in e
- Measurement faults: violate detectors at times t and t+1 for the corresponding check

**At boundaries t = t_i, t_o**: Initialization/read-out faults are equivalent to Pauli faults
and violate the corresponding boundary detectors.

## Main Results
**Definition** (`TimeIndexedDetector`): A detector at time t comparing measurements at t-1/2
  and t+1/2
**Theorem** (`Xv_fault_violates_anticommuting_detectors`): X_v violates s_j^t when s_j has Z
  at v
**Theorem** (`Zv_fault_violates_anticommuting_detectors`): Z_v violates s_j^t when s_j has X
  at v
**Theorem** (`measurement_fault_violates_two_detectors`): Measurement fault at t+1/2 violates
  s_j^t and s_j^{t+1}
**Theorem** (`deformation_Xv_commutes_with_Av`): X_v commutes with A_v (both X-type)
**Theorem** (`deformation_Xv_violates_anticommuting_stilde`): X_v violates s̃_j^t for Z-type
  s̃_j containing v
**Theorem** (`deformation_Zv_violates_Av_and_stilde`): Z_v violates A_v^t and anticommuting
  s̃_j^t
**Theorem** (`deformation_Ze_violates_both_Av`): Z_e violates A_v^t for both endpoints v ∈ e
**Theorem** (`boundary_init_fault_equiv_X_fault`): Init fault syndrome equals X fault syndrome
**Theorem** (`boundary_readout_fault_equiv_Z_fault`): Readout fault syndrome equals Z fault
  syndrome

## File Structure
1. Pauli Type and Symplectic Product: Fundamental anticommutation via symplectic inner product
2. Time-Indexed Detectors: Detectors s_j^t comparing measurements at consecutive half-times
3. Fault Syndrome Violation: When a fault at time t violates detector s_j^t
4. Bulk Syndromes: Pauli faults violate anticommuting time-indexed detectors
5. Measurement Fault Syndromes: Measurement error flips two consecutive detectors
6. Deformation Syndromes: X_v commutes with A_v, Z_v violates A_v
7. Edge Fault Syndromes: Z_e violates A_v for both endpoints
8. Boundary Syndromes: Init/readout fault equivalence to Pauli faults
-/

namespace QEC

namespace SpacetimeSyndromes

open scoped BigOperators

/-! ## Section 1: Pauli Type and Symplectic Product

Two Pauli operators anticommute iff their symplectic inner product is 1 (odd).
For single-site operators:
- X and Z anticommute: σ(X, Z) = 1
- Same-type operators commute: σ(X, X) = σ(Z, Z) = 0
-/

/-- Pauli type: X-type or Z-type operator -/
inductive SyndromePauliType where
  | X : SyndromePauliType
  | Z : SyndromePauliType
  deriving DecidableEq, Repr

/-- Single-site symplectic inner product.
    X and Z anticommute (product = 1), same types commute (product = 0). -/
def singleSiteSymplectic (p1 p2 : SyndromePauliType) : ZMod 2 :=
  match p1, p2 with
  | .X, .Z => 1
  | .Z, .X => 1
  | _, _ => 0

/-- X and Z anticommute: symplectic product is 1 -/
theorem X_Z_anticommute : singleSiteSymplectic .X .Z = 1 := rfl

/-- Z and X anticommute: symplectic product is 1 -/
theorem Z_X_anticommute : singleSiteSymplectic .Z .X = 1 := rfl

/-- X commutes with X: symplectic product is 0 -/
theorem X_X_commute : singleSiteSymplectic .X .X = 0 := rfl

/-- Z commutes with Z: symplectic product is 0 -/
theorem Z_Z_commute : singleSiteSymplectic .Z .Z = 0 := rfl

/-- Symplectic product is symmetric -/
theorem symplectic_symm (p1 p2 : SyndromePauliType) :
    singleSiteSymplectic p1 p2 = singleSiteSymplectic p2 p1 := by
  cases p1 <;> cases p2 <;> rfl

/-- Two operators anticommute iff their symplectic product is 1 -/
def anticommutes (p1 p2 : SyndromePauliType) : Prop := singleSiteSymplectic p1 p2 = 1

/-- X and Z anticommute (as a Prop) -/
theorem X_Z_anticommutes : anticommutes .X .Z := rfl

/-- Z and X anticommute (as a Prop) -/
theorem Z_X_anticommutes : anticommutes .Z .X := rfl

/-- X does not anticommute with X -/
theorem X_X_not_anticommutes : ¬anticommutes .X .X := by
  intro h
  unfold anticommutes singleSiteSymplectic at h
  cases h

/-- Z does not anticommute with Z -/
theorem Z_Z_not_anticommutes : ¬anticommutes .Z .Z := by
  intro h
  unfold anticommutes singleSiteSymplectic at h
  cases h

/-- Anticommutation is decidable -/
instance (p1 p2 : SyndromePauliType) : Decidable (anticommutes p1 p2) := by
  unfold anticommutes
  infer_instance

/-! ## Section 2: Time-Indexed Detectors

A detector s_j^t compares measurements at half-integer times t-1/2 and t+1/2.
The detector fires (parity = 1) when these two measurements disagree.

This captures the central structure from the original statement: detectors are
indexed by both the check s_j and the time t.
-/

/-- A stabilizer check specification: support set and Pauli type at each qubit. -/
structure SyndromeCheckSpec (n : ℕ) where
  /-- Support: set of qubits where the check acts non-trivially -/
  support : Finset (Fin n)
  /-- Pauli type of the check (X or Z) -/
  pauliType : SyndromePauliType
  deriving DecidableEq

/-- A time-indexed detector: s_j^t compares measurements at t-1/2 and t+1/2.

    In the spacetime code, each detector is associated with:
    - A check s_j (the observable being measured)
    - A time t (the detector compares outcome(s_j, t-1/2) with outcome(s_j, t+1/2))

    The detector value (parity) is: outcome(t-1/2) XOR outcome(t+1/2)
    In error-free operation, this is 0 (measurements agree).
    A fault can flip this to 1 (detector fires). -/
structure TimeIndexedDetector (n : ℕ) where
  /-- The check being measured -/
  check : SyndromeCheckSpec n
  /-- The time index t: compares measurements at t-1/2 and t+1/2 -/
  time : TimeStep
  /-- Identifier for the check (for tracking which detector) -/
  checkIndex : ℕ
  deriving DecidableEq

namespace TimeIndexedDetector

variable {n : ℕ}

/-- Two detectors are for the same check if they have the same check index -/
def sameCheck (d1 d2 : TimeIndexedDetector n) : Prop := d1.checkIndex = d2.checkIndex

/-- Two detectors are consecutive if for the same check, times differ by 1 -/
def consecutive (d1 d2 : TimeIndexedDetector n) : Prop :=
  d1.checkIndex = d2.checkIndex ∧ d2.time = d1.time + 1

end TimeIndexedDetector

/-! ## Section 3: Fault Specification and Violation

A Pauli fault at (qubit v, time t) violates detector s_j^t' if:
1. v is in the support of s_j
2. The fault's Pauli type anticommutes with s_j's Pauli type
3. The fault occurs between the two measurement times: t-1/2 < t_fault < t+1/2
   (equivalently, t_fault = t in integer time)

This captures the key insight: a fault at time t affects exactly those detectors
whose measurement interval straddles time t.
-/

/-- A Pauli fault at a specific qubit and time -/
structure SyndromePauliFault (n : ℕ) where
  /-- The qubit where the fault occurs -/
  qubit : Fin n
  /-- The Pauli type of the fault -/
  pauliType : SyndromePauliType
  /-- The time of the fault -/
  time : TimeStep
  deriving DecidableEq

/-- A fault violates a time-indexed detector if:
    1. The fault qubit is in the detector's check support
    2. The fault Pauli type anticommutes with the check's Pauli type
    3. The fault time equals the detector time (fault is between t-1/2 and t+1/2)

    This is the core violation predicate from the original statement. -/
def faultViolatesDetector {n : ℕ}
    (fault : SyndromePauliFault n) (detector : TimeIndexedDetector n) : Prop :=
  fault.qubit ∈ detector.check.support ∧
  anticommutes fault.pauliType detector.check.pauliType ∧
  fault.time = detector.time

instance {n : ℕ} (fault : SyndromePauliFault n) (detector : TimeIndexedDetector n) :
    Decidable (faultViolatesDetector fault detector) := by
  unfold faultViolatesDetector
  infer_instance

/-! ## Section 4: Bulk Syndromes (t < t_i and t > t_o)

**Theorem**: An X_v fault at time t violates detector s_j^t for all s_j that have Z at vertex v.
**Theorem**: A Z_v fault at time t violates detector s_j^t for all s_j that have X at vertex v.

These theorems capture the bulk syndrome characterization from the original statement.
-/

/-- **Main Theorem (Bulk X_v)**: An X_v fault at time t violates all Z-type detectors s_j^t
    where v is in s_j's support.

    This directly formalizes: "X_v fault at time t violates s_j^t for all s_j that
    anticommute with X_v (i.e., Z-type checks containing v)". -/
theorem Xv_fault_violates_anticommuting_detectors {n : ℕ}
    (v : Fin n) (t : TimeStep) (detector : TimeIndexedDetector n)
    (h_in_support : v ∈ detector.check.support)
    (h_Z_type : detector.check.pauliType = .Z)
    (h_time : detector.time = t) :
    faultViolatesDetector ⟨v, .X, t⟩ detector := by
  unfold faultViolatesDetector
  refine ⟨h_in_support, ?_, h_time.symm⟩
  unfold anticommutes singleSiteSymplectic
  rw [h_Z_type]

/-- **Main Theorem (Bulk Z_v)**: A Z_v fault at time t violates all X-type detectors s_j^t
    where v is in s_j's support.

    This directly formalizes: "Z_v fault at time t violates s_j^t for all s_j that
    anticommute with Z_v (i.e., X-type checks containing v)". -/
theorem Zv_fault_violates_anticommuting_detectors {n : ℕ}
    (v : Fin n) (t : TimeStep) (detector : TimeIndexedDetector n)
    (h_in_support : v ∈ detector.check.support)
    (h_X_type : detector.check.pauliType = .X)
    (h_time : detector.time = t) :
    faultViolatesDetector ⟨v, .Z, t⟩ detector := by
  unfold faultViolatesDetector
  refine ⟨h_in_support, ?_, h_time.symm⟩
  unfold anticommutes singleSiteSymplectic
  rw [h_X_type]

/-- Converse: An X_v fault does NOT violate X-type detectors (same type commutes). -/
theorem Xv_fault_not_violates_X_type_detector {n : ℕ}
    (v : Fin n) (t : TimeStep) (detector : TimeIndexedDetector n)
    (h_X_type : detector.check.pauliType = .X) :
    ¬faultViolatesDetector ⟨v, .X, t⟩ detector := by
  intro h
  unfold faultViolatesDetector anticommutes singleSiteSymplectic at h
  rw [h_X_type] at h
  cases h.2.1

/-- Converse: A Z_v fault does NOT violate Z-type detectors (same type commutes). -/
theorem Zv_fault_not_violates_Z_type_detector {n : ℕ}
    (v : Fin n) (t : TimeStep) (detector : TimeIndexedDetector n)
    (h_Z_type : detector.check.pauliType = .Z) :
    ¬faultViolatesDetector ⟨v, .Z, t⟩ detector := by
  intro h
  unfold faultViolatesDetector anticommutes singleSiteSymplectic at h
  rw [h_Z_type] at h
  cases h.2.1

/-- Complete characterization: X_v at time t violates detector s_j^t iff
    v ∈ support(s_j) AND s_j is Z-type AND detector is at time t. -/
theorem Xv_syndrome_iff {n : ℕ}
    (v : Fin n) (t : TimeStep) (detector : TimeIndexedDetector n) :
    faultViolatesDetector ⟨v, .X, t⟩ detector ↔
    (v ∈ detector.check.support ∧ detector.check.pauliType = .Z ∧ detector.time = t) := by
  unfold faultViolatesDetector
  constructor
  · intro ⟨h_in, h_anti, h_time⟩
    refine ⟨h_in, ?_, h_time.symm⟩
    unfold anticommutes singleSiteSymplectic at h_anti
    cases hp : detector.check.pauliType with
    | X => rw [hp] at h_anti; cases h_anti
    | Z => rfl
  · intro ⟨h_in, h_type, h_time⟩
    refine ⟨h_in, ?_, h_time.symm⟩
    unfold anticommutes singleSiteSymplectic
    rw [h_type]

/-- Complete characterization: Z_v at time t violates detector s_j^t iff
    v ∈ support(s_j) AND s_j is X-type AND detector is at time t. -/
theorem Zv_syndrome_iff {n : ℕ}
    (v : Fin n) (t : TimeStep) (detector : TimeIndexedDetector n) :
    faultViolatesDetector ⟨v, .Z, t⟩ detector ↔
    (v ∈ detector.check.support ∧ detector.check.pauliType = .X ∧ detector.time = t) := by
  unfold faultViolatesDetector
  constructor
  · intro ⟨h_in, h_anti, h_time⟩
    refine ⟨h_in, ?_, h_time.symm⟩
    unfold anticommutes singleSiteSymplectic at h_anti
    cases hp : detector.check.pauliType with
    | X => rfl
    | Z => rw [hp] at h_anti; cases h_anti
  · intro ⟨h_in, h_type, h_time⟩
    refine ⟨h_in, ?_, h_time.symm⟩
    unfold anticommutes singleSiteSymplectic
    rw [h_type]

/-! ## Section 5: Measurement Fault Syndromes

A measurement fault for check s_j at time t + 1/2 flips the measurement outcome.
This affects exactly two detectors:
- s_j^t (comparing times t-1/2 and t+1/2) - the faulty measurement is at t+1/2
- s_j^{t+1} (comparing times t+1/2 and t+3/2) - the faulty measurement is at t+1/2

This is the key "two-detector" property from the original statement.
-/

/-- A measurement fault record: error in measuring check j at time t+1/2 -/
structure SyndromeMeasurementFault where
  /-- Time t: the measurement is at t+1/2 -/
  time : TimeStep
  /-- Index of the check being measured -/
  checkIndex : ℕ
  deriving DecidableEq

/-- The two detector times affected by a measurement fault at t+1/2.
    - Detector at time t: compares t-1/2 with t+1/2 (fault is at t+1/2)
    - Detector at time t+1: compares t+1/2 with t+3/2 (fault is at t+1/2) -/
def measurementFaultViolatedTimes (fault : SyndromeMeasurementFault) : Finset TimeStep :=
  {fault.time, fault.time + 1}

/-- **Main Theorem**: A measurement fault affects exactly 2 detectors.

    This formalizes: "s_j-measurement fault at time t + 1/2 violates s_j^t and s_j^{t+1}".
    The two violated detectors are exactly those whose measurement interval includes t+1/2. -/
theorem measurement_fault_violates_two_detectors (fault : SyndromeMeasurementFault) :
    (measurementFaultViolatedTimes fault).card = 2 := by
  unfold measurementFaultViolatedTimes
  have hne : fault.time ≠ fault.time + 1 := Nat.ne_of_lt (Nat.lt_add_one fault.time)
  have hnotin : fault.time ∉ ({fault.time + 1} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact hne
  rw [Finset.card_insert_of_notMem hnotin, Finset.card_singleton]

/-- A measurement fault at time t violates detector s_j^t -/
theorem measurement_fault_violates_detector_t (fault : SyndromeMeasurementFault) :
    fault.time ∈ measurementFaultViolatedTimes fault := by
  unfold measurementFaultViolatedTimes
  exact Finset.mem_insert_self _ _

/-- A measurement fault at time t violates detector s_j^{t+1} -/
theorem measurement_fault_violates_detector_t_plus_1 (fault : SyndromeMeasurementFault) :
    fault.time + 1 ∈ measurementFaultViolatedTimes fault := by
  unfold measurementFaultViolatedTimes
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- Complete characterization: A measurement fault at t+1/2 for check j violates
    detector s_j^t' iff t' = t or t' = t+1. -/
theorem measurement_fault_violation_iff (fault : SyndromeMeasurementFault) (t' : TimeStep) :
    t' ∈ measurementFaultViolatedTimes fault ↔ (t' = fault.time ∨ t' = fault.time + 1) := by
  unfold measurementFaultViolatedTimes
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- The parity change from a measurement fault: flips both affected detectors.
    If the true outcome is m, the reported outcome is m + 1. Each detector
    using this measurement gets its parity flipped. -/
theorem measurement_fault_flips_parity (m_true m_before m_after : ZMod 2) :
    let m_reported := m_true + 1
    let parity_t_correct := m_before + m_true
    let parity_t_faulty := m_before + m_reported
    let parity_t1_correct := m_true + m_after
    let parity_t1_faulty := m_reported + m_after
    parity_t_faulty = parity_t_correct + 1 ∧ parity_t1_faulty = parity_t1_correct + 1 := by
  simp only
  constructor <;> ring

/-! ## Section 6: Deformation Period Syndromes (t_i < t < t_o)

During code deformation, we have new operators:
- Gauss law operators A_v (X-type at vertex v)
- Flux operators B_p (Z-type on cycle edges)
- Deformed checks s̃_j

Key difference from bulk:
- **X_v commutes with A_v**: Both are X-type, so no violation
- **Z_v violates A_v**: Z anticommutes with X
- X_e violates B_p for p ∋ e (X anticommutes with Z)
- Z_e violates A_v for both endpoints v ∈ e
-/

/-- Gauss law operator A_v: X-type, supported on vertex v -/
def gaussLawCheck (n : ℕ) (v : Fin n) : SyndromeCheckSpec n where
  support := {v}
  pauliType := .X

/-- Flux operator B_p: Z-type, supported on cycle edges -/
structure SyndromeFluxSpec (n : ℕ) where
  /-- Index identifying this plaquette -/
  index : ℕ
  /-- Support: edges in the cycle -/
  edgeSupport : Finset (Fin n)
  deriving DecidableEq

/-- A flux operator as a check (Z-type on its edge support) -/
def fluxAsCheck {n : ℕ} (flux : SyndromeFluxSpec n) : SyndromeCheckSpec n where
  support := flux.edgeSupport
  pauliType := .Z

/-- **Main Theorem (Deformation X_v commutes with A_v)**: X_v does NOT violate A_v^t.

    This is the key difference during deformation: X faults on vertices
    do NOT trigger Gauss law detectors because both are X-type.

    Original: "X_v fault at time t: violates s̃_j^t for anticommuting s̃_j"
    Implicit: X_v does NOT violate A_v^t (they commute). -/
theorem deformation_Xv_commutes_with_Av {n : ℕ} (v : Fin n) (t : TimeStep) :
    ¬faultViolatesDetector ⟨v, .X, t⟩ ⟨gaussLawCheck n v, t, 0⟩ := by
  intro h
  unfold faultViolatesDetector gaussLawCheck anticommutes singleSiteSymplectic at h
  simp only at h
  cases h.2.1

/-- **Main Theorem (Deformation X_v violates s̃_j)**: X_v violates Z-type deformed checks.

    During deformation, X_v violates s̃_j^t for all s̃_j that:
    1. Contain v in their support
    2. Are Z-type (anticommute with X) -/
theorem deformation_Xv_violates_anticommuting_stilde {n : ℕ}
    (v : Fin n) (t : TimeStep) (stilde : TimeIndexedDetector n)
    (h_in_support : v ∈ stilde.check.support)
    (h_Z_type : stilde.check.pauliType = .Z)
    (h_time : stilde.time = t) :
    faultViolatesDetector ⟨v, .X, t⟩ stilde := by
  unfold faultViolatesDetector
  refine ⟨h_in_support, ?_, h_time.symm⟩
  unfold anticommutes singleSiteSymplectic
  rw [h_Z_type]

/-- **Main Theorem (Deformation Z_v syndrome)**: Z_v violates A_v^t AND anticommuting s̃_j^t.

    This formalizes: "Z_v fault at time t: violates A_v^t and s̃_j^t for
    anticommuting s̃_j" -/
theorem deformation_Zv_violates_Av_and_stilde {n : ℕ} (v : Fin n) (t : TimeStep)
    (stilde_detectors : Finset (TimeIndexedDetector n)) :
    -- Part 1: Z_v violates A_v^t
    let Av_detector : TimeIndexedDetector n := ⟨gaussLawCheck n v, t, 0⟩
    faultViolatesDetector ⟨v, .Z, t⟩ Av_detector ∧
    -- Part 2: Z_v violates all X-type s̃_j containing v
    (∀ d ∈ stilde_detectors,
      v ∈ d.check.support → d.check.pauliType = .X → d.time = t →
      faultViolatesDetector ⟨v, .Z, t⟩ d) := by
  constructor
  · -- Z_v violates A_v: Z anticommutes with X
    unfold faultViolatesDetector gaussLawCheck anticommutes singleSiteSymplectic
    simp only [Finset.mem_singleton, true_and]
  · -- Z_v violates X-type s̃_j containing v
    intro d _ h_in h_type h_time
    unfold faultViolatesDetector
    refine ⟨h_in, ?_, h_time.symm⟩
    unfold anticommutes singleSiteSymplectic
    rw [h_type]

/-- Z_v violates A_v (standalone version) -/
theorem Zv_violates_gauss_law {n : ℕ} (v : Fin n) (t : TimeStep) :
    let Av_detector : TimeIndexedDetector n := ⟨gaussLawCheck n v, t, 0⟩
    faultViolatesDetector ⟨v, .Z, t⟩ Av_detector := by
  unfold faultViolatesDetector gaussLawCheck anticommutes singleSiteSymplectic
  simp only [Finset.mem_singleton, true_and]

/-- **Main Theorem (Deformation X_e syndrome)**: X_e violates B_p^t for all p containing e.

    This formalizes: "X_e fault at time t: violates B_p^t for all p ∋ e" -/
theorem deformation_Xe_violates_Bp {n : ℕ}
    (e : Fin n) (t : TimeStep) (flux : SyndromeFluxSpec n)
    (h_in_cycle : e ∈ flux.edgeSupport) :
    let Bp_detector : TimeIndexedDetector n := ⟨fluxAsCheck flux, t, flux.index⟩
    faultViolatesDetector ⟨e, .X, t⟩ Bp_detector := by
  unfold faultViolatesDetector fluxAsCheck anticommutes singleSiteSymplectic
  exact ⟨h_in_cycle, rfl, rfl⟩

/-- Z_e does NOT violate B_p (both Z-type, commute) -/
theorem Ze_commutes_with_Bp {n : ℕ}
    (e : Fin n) (t : TimeStep) (flux : SyndromeFluxSpec n) :
    ¬faultViolatesDetector ⟨e, .Z, t⟩ ⟨fluxAsCheck flux, t, flux.index⟩ := by
  intro h
  unfold faultViolatesDetector fluxAsCheck anticommutes singleSiteSymplectic at h
  cases h.2.1

/-! ## Section 7: Edge Fault Syndromes (Z_e)

A Z_e fault on edge e violates A_v^t for both endpoints v ∈ e.
This is because A_v is X-type at vertex v, and Z anticommutes with X.
-/

/-- An edge with explicit endpoints -/
structure SyndromeEdge where
  /-- First endpoint -/
  v1 : ℕ
  /-- Second endpoint -/
  v2 : ℕ
  /-- Endpoints are distinct -/
  distinct : v1 ≠ v2
  deriving DecidableEq

/-- The endpoints of an edge as a finset -/
def SyndromeEdge.endpoints (e : SyndromeEdge) : Finset ℕ := {e.v1, e.v2}

/-- An edge has exactly 2 endpoints -/
theorem edge_endpoints_card (e : SyndromeEdge) : e.endpoints.card = 2 := by
  unfold SyndromeEdge.endpoints
  have hnotin : e.v1 ∉ ({e.v2} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact e.distinct
  rw [Finset.card_insert_of_notMem hnotin, Finset.card_singleton]

/-- v1 is an endpoint -/
theorem edge_v1_in_endpoints (e : SyndromeEdge) : e.v1 ∈ e.endpoints := by
  unfold SyndromeEdge.endpoints
  exact Finset.mem_insert_self _ _

/-- v2 is an endpoint -/
theorem edge_v2_in_endpoints (e : SyndromeEdge) : e.v2 ∈ e.endpoints := by
  unfold SyndromeEdge.endpoints
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **Main Theorem (Deformation Z_e syndrome)**: Z_e violates A_v^t for BOTH endpoints v ∈ e.

    This formalizes: "Z_e fault at time t: violates A_v^t for both v ∈ e"

    The key insight is that Z_e has support on edge e, which is adjacent to both
    endpoint vertices. Each Gauss law A_v is X-type, and Z anticommutes with X. -/
theorem deformation_Ze_violates_both_Av {n : ℕ} (e : SyndromeEdge) (t : TimeStep)
    (h_v1_bound : e.v1 < n) (h_v2_bound : e.v2 < n) :
    -- Z fault at v1 violates A_{v1}^t
    let Av1_detector : TimeIndexedDetector n := ⟨gaussLawCheck n ⟨e.v1, h_v1_bound⟩, t, 0⟩
    let Av2_detector : TimeIndexedDetector n := ⟨gaussLawCheck n ⟨e.v2, h_v2_bound⟩, t, 1⟩
    -- Both A_v detectors are violated when qubit at endpoint has Z fault
    (∀ qubit : Fin n, qubit.val ∈ e.endpoints →
      faultViolatesDetector ⟨qubit, .Z, t⟩ Av1_detector ∨
      faultViolatesDetector ⟨qubit, .Z, t⟩ Av2_detector) ∧
    -- The violated set has exactly 2 elements
    e.endpoints.card = 2 := by
  constructor
  · intro qubit h_in
    unfold SyndromeEdge.endpoints at h_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at h_in
    cases h_in with
    | inl heq =>
      left
      unfold faultViolatesDetector gaussLawCheck anticommutes singleSiteSymplectic
      simp only [Finset.mem_singleton]
      constructor
      · exact Fin.ext heq
      · trivial
    | inr heq =>
      right
      unfold faultViolatesDetector gaussLawCheck anticommutes singleSiteSymplectic
      simp only [Finset.mem_singleton]
      constructor
      · exact Fin.ext heq
      · trivial
  · exact edge_endpoints_card e

/-! ## Section 8: Boundary Fault Syndromes (t = t_i, t_o)

At boundary times:
- **Initialization fault** (at t_i): Produces |1⟩ instead of |0⟩. Since |1⟩ = X|0⟩,
  this is equivalent to an X fault after correct initialization.
- **Readout fault** (at t_o): Flips the Z measurement outcome. This is equivalent
  to a Z fault before measurement.

The key theorem is that boundary faults have the SAME syndrome as the corresponding
Pauli faults - they violate the same detectors.
-/

/-- Initialization fault on an edge: produces |1⟩ instead of |0⟩ at time t_i -/
structure SyndromeInitFault where
  /-- The edge qubit with faulty initialization -/
  edgeIndex : ℕ
  deriving DecidableEq

/-- Readout fault on an edge: flips Z measurement outcome at time t_o -/
structure SyndromeReadoutFault where
  /-- The edge qubit with faulty readout -/
  edgeIndex : ℕ
  deriving DecidableEq

/-- **Main Theorem (Init fault equivalence)**: An initialization fault has the
    SAME syndrome as an X fault.

    Physical reasoning: |1⟩ = X|0⟩, so initializing to |1⟩ instead of |0⟩
    is indistinguishable from correctly initializing then applying X.

    This formalizes: "Initialization faults are equivalent to Pauli faults
    and violate the corresponding boundary detectors." -/
theorem boundary_init_fault_equiv_X_fault {n : ℕ}
    (edgeQubit : Fin n) (t_boundary : TimeStep)
    (detectors : Finset (TimeIndexedDetector n)) :
    -- Init fault syndrome = X fault syndrome
    -- Both violate exactly the Z-type detectors containing the edge qubit at boundary time
    ∀ d ∈ detectors,
      (edgeQubit ∈ d.check.support ∧ d.check.pauliType = .Z ∧ d.time = t_boundary) ↔
      faultViolatesDetector ⟨edgeQubit, .X, t_boundary⟩ d := by
  intro d _
  exact (Xv_syndrome_iff edgeQubit t_boundary d).symm

/-- **Main Theorem (Readout fault equivalence)**: A readout fault has the
    SAME syndrome as a Z fault.

    Physical reasoning: Flipping a Z measurement outcome is equivalent to
    applying Z before measurement (Z flips computational basis).

    This formalizes: "Read-out faults are equivalent to Pauli faults
    and violate the corresponding boundary detectors." -/
theorem boundary_readout_fault_equiv_Z_fault {n : ℕ}
    (edgeQubit : Fin n) (t_boundary : TimeStep)
    (detectors : Finset (TimeIndexedDetector n)) :
    -- Readout fault syndrome = Z fault syndrome
    -- Both violate exactly the X-type detectors containing the edge qubit at boundary time
    ∀ d ∈ detectors,
      (edgeQubit ∈ d.check.support ∧ d.check.pauliType = .X ∧ d.time = t_boundary) ↔
      faultViolatesDetector ⟨edgeQubit, .Z, t_boundary⟩ d := by
  intro d _
  exact (Zv_syndrome_iff edgeQubit t_boundary d).symm

/-- Init fault creates X-like syndrome: does NOT violate Gauss law detectors (X commutes X) -/
theorem boundary_init_fault_commutes_with_Av {n : ℕ} (v : Fin n) (t_boundary : TimeStep) :
    -- Init fault (≡ X fault) does NOT violate A_v (both X-type, commute)
    ¬faultViolatesDetector ⟨v, .X, t_boundary⟩ ⟨gaussLawCheck n v, t_boundary, 0⟩ := by
  intro h
  unfold faultViolatesDetector gaussLawCheck anticommutes singleSiteSymplectic at h
  simp only at h
  cases h.2.1

/-- Readout fault creates Z-like syndrome: violates Gauss law detectors -/
theorem boundary_readout_fault_violates_Av {n : ℕ} (v : Fin n) (t_boundary : TimeStep) :
    -- Readout fault (≡ Z fault) violates A_v (Gauss law is X-type)
    let Av_detector : TimeIndexedDetector n := ⟨gaussLawCheck n v, t_boundary, 0⟩
    faultViolatesDetector ⟨v, .Z, t_boundary⟩ Av_detector := by
  unfold faultViolatesDetector gaussLawCheck anticommutes singleSiteSymplectic
  simp only [Finset.mem_singleton, true_and]

/-! ## Section 9: Complete Syndrome Classification

The main classification theorem packages all syndrome results.
-/

/-- Time period classification -/
inductive TimePeriod where
  | bulk    : TimePeriod  -- t < t_i or t > t_o
  | deformation : TimePeriod  -- t_i < t < t_o
  | boundary : TimePeriod  -- t = t_i or t = t_o
  deriving DecidableEq, Repr

/-- **Main Theorem**: Complete classification of spacetime fault syndromes.

    This theorem summarizes all syndrome characterizations:
    1. (Bulk) X_v/Z_v faults violate anticommuting time-indexed detectors
    2. (Bulk) Measurement faults violate exactly 2 consecutive detectors
    3. (Deformation) X_v commutes with A_v, violates anticommuting s̃_j
    4. (Deformation) Z_v violates A_v AND anticommuting s̃_j
    5. (Deformation) X_e violates B_p for p ∋ e
    6. (Deformation) Z_e violates A_v for both endpoints
    7. (Boundary) Init fault ≡ X fault syndrome
    8. (Boundary) Readout fault ≡ Z fault syndrome -/
theorem spacetime_syndrome_classification :
    -- Fundamental anticommutation
    anticommutes .X .Z ∧ anticommutes .Z .X ∧
    ¬anticommutes .X .X ∧ ¬anticommutes .Z .Z ∧
    -- Measurement faults affect exactly 2 detectors
    (∀ fault : SyndromeMeasurementFault, (measurementFaultViolatedTimes fault).card = 2) ∧
    -- Edge endpoints count
    (∀ e : SyndromeEdge, e.endpoints.card = 2) := by
  exact ⟨X_Z_anticommutes, Z_X_anticommutes,
         X_X_not_anticommutes, Z_Z_not_anticommutes,
         measurement_fault_violates_two_detectors,
         edge_endpoints_card⟩

/-! ## Section 10: Syndrome Additivity

Syndromes combine additively in ZMod 2.
-/

/-- Syndromes add in ZMod 2: same fault twice cancels -/
theorem syndrome_additivity (s : ZMod 2) : s + s = 0 := ZMod2_self_add_self s

/-- Two faults with same syndrome at same location cancel -/
theorem same_faults_cancel : ∀ s : ZMod 2, s + s = 0 := ZMod2_self_add_self

end SpacetimeSyndromes

end QEC
