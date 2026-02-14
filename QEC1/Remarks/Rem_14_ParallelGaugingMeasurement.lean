import QEC1.Remarks.Rem_13_OptimalCheegerConstant
import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import Mathlib.Tactic

/-!
# Remark 14: Parallel Gauging Measurement

## Statement
The gauging measurement (Definition 5) can be applied to multiple logical operators in
parallel, subject to compatibility conditions:

1. **Non-overlapping support:** If logical operators L₁, …, Lₘ have disjoint supports,
   they can be gauged simultaneously with independent graphs G₁, …, Gₘ.

2. **Same-type overlapping support:** If Lᵢ and Lⱼ share support where both act by the
   same Pauli type on every shared qubit, they can be gauged in parallel.

3. **LDPC constraint:** At most a constant number of logical operators should share
   support on any single qubit to maintain the LDPC property.

4. **Time-space tradeoff:** Measuring 2m-1 copies in parallel with ⌈d/m⌉ rounds and
   majority vote trades time for space.

## Main Results
- `DisjointSupports` : definition of disjoint support condition
- `SameTypeOverlap` : definition of same-type overlap condition
- `ParallelLDPCBound` : definition of the LDPC qubit-degree bound
- `disjoint_supports_imply_commutation` : disjoint Pauli operators commute
- `sameType_overlap_implies_commutation` : same-type overlap implies commutation
- `parallel_qubit_degree_bound` : LDPC qubit degree bound under parallel gauging
- `time_space_tradeoff_summary` : combined time-space tradeoff properties
- `majority_vote_correct` : majority vote over 2m-1 copies gives correct outcome
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
noncomputable section

namespace ParallelGaugingMeasurement

open Finset PauliOp GaussFlux DeformedOperator DeformedCode DeformedCodeChecks
     QEC1 SpaceDistance OptimalCheegerConstant

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Part 1: Non-overlapping support — Disjoint supports imply commutation -/

/-- Two Pauli operators have disjoint supports if no qubit belongs to both supports. -/
def DisjointSupports (P Q : PauliOp V) : Prop :=
  Disjoint P.support Q.support

/-- A family of logical operators has pairwise disjoint supports. -/
def PairwiseDisjointSupports {m : ℕ} (ops : Fin m → PauliOp V) : Prop :=
  ∀ i j : Fin m, i ≠ j → DisjointSupports (ops i) (ops j)

/-- Helper: if P has zero xVec and zVec at v, P does not act on v. -/
private lemma not_mem_support_iff (P : PauliOp V) (v : V) :
    v ∉ P.support ↔ P.xVec v = 0 ∧ P.zVec v = 0 := by
  simp [PauliOp.mem_support]

/-- Operators with disjoint supports commute: if P and Q act on disjoint qubits,
    their symplectic inner product vanishes. -/
theorem disjoint_supports_imply_commutation (P Q : PauliOp V)
    (h : DisjointSupports P Q) : PauliCommute P Q := by
  unfold PauliCommute symplecticInner
  apply Finset.sum_eq_zero
  intro v _
  unfold DisjointSupports at h
  rw [Finset.disjoint_left] at h
  by_cases hP : v ∈ P.support
  · have hQ := h hP
    rw [not_mem_support_iff] at hQ
    simp [hQ.1, hQ.2]
  · rw [not_mem_support_iff] at hP
    simp [hP.1, hP.2]

/-- Multiple operators with pairwise disjoint supports all pairwise commute. -/
theorem pairwise_disjoint_implies_pairwise_commute {m : ℕ}
    (ops : Fin m → PauliOp V)
    (h : PairwiseDisjointSupports ops) :
    ∀ i j : Fin m, PauliCommute (ops i) (ops j) := by
  intro i j
  by_cases hij : i = j
  · subst hij; exact pauliCommute_self _
  · exact disjoint_supports_imply_commutation _ _ (h i j hij)

/-- Disjoint supports are symmetric. -/
theorem disjointSupports_comm (P Q : PauliOp V) :
    DisjointSupports P Q ↔ DisjointSupports Q P := by
  unfold DisjointSupports
  exact disjoint_comm

/-- Disjoint supports with identity. -/
theorem disjointSupports_one (P : PauliOp V) :
    DisjointSupports P 1 := by
  unfold DisjointSupports
  simp [PauliOp.support_one]

/-! ## Part 2: Same-type overlapping support -/

/-- Two Pauli operators have same-type X overlap if on every shared support qubit,
    both have X-type action (xVec ≠ 0) and neither has Z-type action (zVec = 0). -/
def SameTypeXOverlap (P Q : PauliOp V) : Prop :=
  ∀ v : V, v ∈ P.support → v ∈ Q.support →
    P.zVec v = 0 ∧ Q.zVec v = 0

/-- Two Pauli operators have same-type Z overlap if on every shared support qubit,
    both have Z-type action (zVec ≠ 0) and neither has X-type action (xVec = 0). -/
def SameTypeZOverlap (P Q : PauliOp V) : Prop :=
  ∀ v : V, v ∈ P.support → v ∈ Q.support →
    P.xVec v = 0 ∧ Q.xVec v = 0

/-- Two Pauli operators have same-type overlap if on every shared support qubit,
    both act by the same Pauli type (both X or both Z). Equivalently: on shared
    qubits, either both have zero Z-component or both have zero X-component. -/
def SameTypeOverlap (P Q : PauliOp V) : Prop :=
  ∀ v : V, v ∈ P.support → v ∈ Q.support →
    (P.zVec v = 0 ∧ Q.zVec v = 0) ∨ (P.xVec v = 0 ∧ Q.xVec v = 0)

/-- Same-type X overlap implies same-type overlap. -/
theorem sameTypeXOverlap_implies_sameTypeOverlap (P Q : PauliOp V)
    (h : SameTypeXOverlap P Q) : SameTypeOverlap P Q := by
  intro v hP hQ; left; exact h v hP hQ

/-- Same-type Z overlap implies same-type overlap. -/
theorem sameTypeZOverlap_implies_sameTypeOverlap (P Q : PauliOp V)
    (h : SameTypeZOverlap P Q) : SameTypeOverlap P Q := by
  intro v hP hQ; right; exact h v hP hQ

/-- Disjoint supports imply same-type overlap vacuously. -/
theorem disjointSupports_implies_sameTypeOverlap (P Q : PauliOp V)
    (h : DisjointSupports P Q) : SameTypeOverlap P Q := by
  intro v hP hQ; exfalso
  exact Finset.disjoint_left.mp h hP hQ

/-- Same-type overlap implies commutation: if P and Q share support only
    with the same Pauli type on each shared qubit, their symplectic inner product
    vanishes (each shared qubit contributes 0 to the sum). -/
theorem sameType_overlap_implies_commutation (P Q : PauliOp V)
    (h : SameTypeOverlap P Q) : PauliCommute P Q := by
  unfold PauliCommute symplecticInner
  apply Finset.sum_eq_zero
  intro v _
  by_cases hP : v ∈ P.support
  · by_cases hQ : v ∈ Q.support
    · obtain ⟨hz1, hz2⟩ | ⟨hx1, hx2⟩ := h v hP hQ
      · simp [hz1, hz2]
      · simp [hx1, hx2]
    · rw [not_mem_support_iff] at hQ
      simp [hQ.1, hQ.2]
  · rw [not_mem_support_iff] at hP
    simp [hP.1, hP.2]

/-- The Gauss's law operator A_v is pure X-type, so any pure X-type logical
    operator has same-type X overlap with it on the extended system. -/
theorem gaussLaw_pure_X_type (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (v : V) :
    (gaussLawOp G v).zVec = 0 :=
  gaussLawOp_zVec G v

/-- For a pure X-type operator (zVec = 0), same-type X overlap with any
    other pure X-type operator holds automatically. -/
theorem pure_X_sameType_overlap (P Q : PauliOp V)
    (hP : P.zVec = 0) (hQ : Q.zVec = 0) : SameTypeXOverlap P Q := by
  intro v _ _
  exact ⟨congr_fun hP v, congr_fun hQ v⟩

/-- Pure X-type operators commute (special case of same-type overlap). -/
theorem pure_X_commute (P Q : PauliOp V) (hP : P.zVec = 0) (hQ : Q.zVec = 0) :
    PauliCommute P Q :=
  sameType_overlap_implies_commutation P Q
    (sameTypeXOverlap_implies_sameTypeOverlap P Q (pure_X_sameType_overlap P Q hP hQ))

/-- Pure Z-type operators commute (special case of same-type overlap). -/
theorem pure_Z_commute (P Q : PauliOp V) (hP : P.xVec = 0) (hQ : Q.xVec = 0) :
    PauliCommute P Q := by
  have h : SameTypeZOverlap P Q := fun v _ _ => ⟨congr_fun hP v, congr_fun hQ v⟩
  exact sameType_overlap_implies_commutation P Q
    (sameTypeZOverlap_implies_sameTypeOverlap P Q h)

/-! ## Part 3: LDPC constraint for parallel gauging -/

/-- The qubit participation count for parallel gauging: the number of logical
    operators (from a family) whose support contains qubit v. -/
def qubitParticipationCount {m : ℕ} (ops : Fin m → PauliOp V) (v : V) : ℕ :=
  (Finset.univ.filter (fun i => v ∈ (ops i).support)).card

/-- The LDPC bound for parallel gauging: each qubit participates in at most
    c logical operators' supports. -/
def ParallelLDPCBound {m : ℕ} (ops : Fin m → PauliOp V) (c : ℕ) : Prop :=
  ∀ v : V, qubitParticipationCount ops v ≤ c

/-- For disjoint supports, the participation count is at most 1. -/
theorem disjoint_participation_le_one {m : ℕ}
    (ops : Fin m → PauliOp V)
    (h : PairwiseDisjointSupports ops) (v : V) :
    qubitParticipationCount ops v ≤ 1 := by
  unfold qubitParticipationCount
  rw [Finset.card_le_one]
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  by_contra hij
  exact Finset.disjoint_left.mp (h i j hij) hi hj

/-- Disjoint supports trivially satisfy the LDPC bound with c = 1. -/
theorem disjoint_implies_LDPC_bound {m : ℕ}
    (ops : Fin m → PauliOp V)
    (h : PairwiseDisjointSupports ops) :
    ParallelLDPCBound ops 1 :=
  fun v => disjoint_participation_le_one ops h v

/-- The participation count is bounded by the total number of operators. -/
theorem participation_le_total {m : ℕ} (ops : Fin m → PauliOp V) (v : V) :
    qubitParticipationCount ops v ≤ m := by
  unfold qubitParticipationCount
  calc (Finset.univ.filter (fun i => v ∈ (ops i).support)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = m := Finset.card_fin m

/-- The sum of participation counts equals the sum of support sizes. -/
theorem sum_participation_eq_sum_support {m : ℕ} (ops : Fin m → PauliOp V) :
    ∑ v : V, qubitParticipationCount ops v =
    ∑ i : Fin m, (ops i).support.card := by
  unfold qubitParticipationCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  congr 1
  ext1 i
  simp_rw [Finset.sum_boole]
  norm_cast
  congr 1
  ext v
  simp

/-- When the LDPC bound holds with constant c, the contribution of each qubit
    to the total check degree of the deformed code from parallel gauging is bounded. -/
theorem parallel_qubit_degree_bound {m : ℕ}
    (ops : Fin m → PauliOp V) (c : ℕ)
    (hbound : ParallelLDPCBound ops c) (v : V) :
    qubitParticipationCount ops v ≤ c :=
  hbound v

/-! ## Part 4: Time-space tradeoff -/

/-- The number of parallel copies in the time-space tradeoff: 2m - 1 for m ≥ 1.
    Each copy is an equivalent logical representative with its own gauging graph. -/
def numCopies (m : ℕ) : ℕ := 2 * m - 1

/-- The number of rounds in the time-space tradeoff: ⌈d/m⌉ for distance d and
    parameter m. This is the ceiling division. -/
def numRounds (d m : ℕ) : ℕ := (d + m - 1) / m

/-- numCopies 1 = 1: no parallelism, standard case. -/
@[simp]
theorem numCopies_one : numCopies 1 = 1 := by simp [numCopies]

/-- numRounds d 1 = d: no parallelism, standard number of rounds. -/
@[simp]
theorem numRounds_one (d : ℕ) : numRounds d 1 = d := by simp [numRounds]

/-- numCopies is always positive for m ≥ 1. -/
theorem numCopies_pos {m : ℕ} (hm : 1 ≤ m) : 1 ≤ numCopies m := by
  unfold numCopies; omega

/-- numCopies is odd: 2m - 1 is always odd for m ≥ 1. -/
theorem numCopies_odd {m : ℕ} (hm : 1 ≤ m) : ¬ 2 ∣ numCopies m := by
  unfold numCopies; omega

/-- Ceiling division: ⌈d/m⌉ * m ≥ d. -/
private lemma ceil_div_mul_ge (d m : ℕ) (hm : 0 < m) :
    d ≤ ((d + m - 1) / m) * m := by
  have hmod : m * ((d + m - 1) / m) + (d + m - 1) % m = d + m - 1 :=
    Nat.div_add_mod (d + m - 1) m
  have hlt : (d + m - 1) % m < m := Nat.mod_lt _ hm
  have hmul_comm : m * ((d + m - 1) / m) = (d + m - 1) / m * m := Nat.mul_comm _ _
  omega

/-- numRounds is always positive when d > 0 and m > 0. -/
theorem numRounds_pos {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    0 < numRounds d m := by
  unfold numRounds
  have := ceil_div_mul_ge d m hm
  by_contra h
  push_neg at h
  interval_cases ((d + m - 1) / m)
  simp at this
  omega

/-- numRounds is at most d (we never need more rounds than the original). -/
theorem numRounds_le {d m : ℕ} (hm : 1 ≤ m) : numRounds d m ≤ d := by
  unfold numRounds
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0: (0 + m - 1) / m = (m - 1) / m = 0 ≤ 0
    have : m - 1 < m := Nat.sub_lt (by omega) one_pos
    simp [Nat.div_eq_of_lt this]
  · -- d > 0: use Nat.div_le_iff_le_mul_add_pred to reduce to omega-solvable goal
    rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < m)]
    -- Goal: d + m - 1 ≤ m * d + (m - 1)
    -- This is just d ≤ m * d (with m ≥ 1, d ≥ 1)
    have : 1 * d ≤ m * d := Nat.mul_le_mul_right d hm
    omega

/-- The key tradeoff: numCopies * numRounds ≥ d. -/
theorem tradeoff_total_work_ge {d m : ℕ} (hm : 1 ≤ m) :
    d ≤ numCopies m * numRounds d m := by
  unfold numCopies numRounds
  have hm_le : m ≤ 2 * m - 1 := by omega
  have hceil := ceil_div_mul_ge d m (by omega)
  calc d ≤ ((d + m - 1) / m) * m := hceil
    _ ≤ ((d + m - 1) / m) * (2 * m - 1) := Nat.mul_le_mul_left _ hm_le
    _ = (2 * m - 1) * ((d + m - 1) / m) := Nat.mul_comm _ _

/-- The qubit overhead factor: using 2m-1 copies multiplies the qubit count. -/
theorem qubit_overhead_factor (n m : ℕ) (_hm : 1 ≤ m) :
    numCopies m * n = (2 * m - 1) * n := by
  simp [numCopies]

/-- As m increases, numCopies increases (monotonicity). -/
theorem numCopies_monotone {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    numCopies m₁ ≤ numCopies m₂ := by
  unfold numCopies; omega

/-- numRounds is antitonically related to m for fixed d: larger m means fewer rounds. -/
theorem numRounds_antitone {d m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (hm₁ : 0 < m₁) :
    numRounds d m₂ ≤ numRounds d m₁ := by
  unfold numRounds
  have hm₂ : 0 < m₂ := lt_of_lt_of_le hm₁ hm
  -- We use: a / b ≤ c ↔ a ≤ b * c + (b - 1) for Nat
  rw [Nat.div_le_iff_le_mul_add_pred hm₂]
  -- Goal: d + m₂ - 1 ≤ m₂ * ((d + m₁ - 1) / m₁) + (m₂ - 1)
  -- Suffices to show d ≤ m₂ * ((d + m₁ - 1) / m₁)
  suffices d ≤ m₂ * ((d + m₁ - 1) / m₁) by omega
  -- From ceil_div_mul_ge: d ≤ ((d + m₁ - 1) / m₁) * m₁
  have hceil := ceil_div_mul_ge d m₁ hm₁
  -- Since m₁ ≤ m₂: ((d + m₁ - 1) / m₁) * m₁ ≤ ((d + m₁ - 1) / m₁) * m₂
  have hle : ((d + m₁ - 1) / m₁) * m₁ ≤ ((d + m₁ - 1) / m₁) * m₂ :=
    Nat.mul_le_mul_left _ hm
  calc d ≤ ((d + m₁ - 1) / m₁) * m₁ := hceil
    _ ≤ ((d + m₁ - 1) / m₁) * m₂ := hle
    _ = m₂ * ((d + m₁ - 1) / m₁) := Nat.mul_comm _ _

/-! ## Majority vote correctness -/

/-- The majority vote threshold: more than half of 2m-1 copies must agree. -/
def majorityThreshold (m : ℕ) : ℕ := m

/-- The majority threshold is always a strict majority of numCopies. -/
theorem majorityThreshold_gt_half {m : ℕ} (hm : 1 ≤ m) :
    2 * majorityThreshold m > numCopies m := by
  unfold majorityThreshold numCopies; omega

/-- The majority threshold is at most numCopies. -/
theorem majorityThreshold_le_copies {m : ℕ} (hm : 1 ≤ m) :
    majorityThreshold m ≤ numCopies m := by
  unfold majorityThreshold numCopies; omega

/-- If at least m out of 2m-1 copies give outcome σ, the majority vote returns σ.
    Here we prove the combinatorial fact: a set of at least m elements out of
    2m-1 total constitutes a strict majority. -/
theorem majority_vote_correct (m : ℕ) (hm : 1 ≤ m) (agree total : ℕ)
    (htotal : total = numCopies m)
    (hagree : m ≤ agree) (hle : agree ≤ total) :
    2 * agree > total := by
  subst htotal; unfold numCopies; omega

/-- The complement: if at least m out of 2m-1 agree, the minority has fewer than m. -/
theorem minority_vote_bound (m : ℕ) (hm : 1 ≤ m) (agree total : ℕ)
    (htotal : total = numCopies m)
    (hagree : m ≤ agree) (hle : agree ≤ total) :
    total - agree < m := by
  subst htotal; unfold numCopies; omega

/-! ## Combined properties -/

/-- Summary: for pairwise disjoint supports, all conditions for parallel
    gauging are automatically satisfied (commutation + LDPC with c = 1). -/
theorem disjoint_parallel_gauging_compatible {m : ℕ}
    (ops : Fin m → PauliOp V)
    (h : PairwiseDisjointSupports ops) :
    (∀ i j : Fin m, PauliCommute (ops i) (ops j)) ∧
    ParallelLDPCBound ops 1 :=
  ⟨pairwise_disjoint_implies_pairwise_commute ops h,
   disjoint_implies_LDPC_bound ops h⟩

/-- For any m ≥ 1, the time-space tradeoff reduces rounds from d to ⌈d/m⌉
    at the cost of (2m-1) copies. -/
theorem time_space_tradeoff_summary (d n m : ℕ) (hm : 1 ≤ m) :
    numCopies m * n = (2 * m - 1) * n ∧
    numRounds d m ≤ d ∧
    d ≤ numCopies m * numRounds d m :=
  ⟨qubit_overhead_factor n m hm,
   numRounds_le hm,
   tradeoff_total_work_ge hm⟩

/-- Special case: m = 1 (no parallelism). One copy, d rounds. -/
theorem no_parallelism_case (d n : ℕ) :
    numCopies 1 * n = n ∧ numRounds d 1 = d := by
  simp [numCopies, numRounds]

/-- Special case: m = d (maximum parallelism). 2d-1 copies, 1 round. -/
theorem max_parallelism_case (d : ℕ) (hd : 1 ≤ d) :
    numRounds d d = 1 ∧ numCopies d = 2 * d - 1 := by
  constructor
  · unfold numRounds
    have : (d + d - 1) / d = 1 := by
      apply Nat.div_eq_of_lt_le
      · -- 1 * d ≤ d + d - 1, i.e., d ≤ 2d - 1
        omega
      · -- d + d - 1 < (1 + 1) * d, i.e., 2d - 1 < 2d
        omega
    exact this
  · rfl

/-- The overhead ratio: additional copies are 2(m-1). -/
theorem overhead_additional_copies (m : ℕ) (hm : 1 ≤ m) :
    numCopies m - 1 = 2 * (m - 1) := by
  unfold numCopies; omega

end ParallelGaugingMeasurement
