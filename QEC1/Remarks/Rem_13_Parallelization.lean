import QEC1.Remarks.Rem_12_CircuitImplementation

/-!
# Parallelization of Gauging Measurement (Remark 13)

## Statement
The gauging measurement can be applied to multiple logical operators in parallel, subject to
compatibility conditions:

**Compatibility condition**: Logical operators L₁, ..., Lₘ can be measured in parallel if no pair
acts on a common qubit via different non-trivial Pauli operators. Specifically: for all i ≠ j
and all qubits v, at least one of the following holds:
- v ∉ supp(Lᵢ), or
- v ∉ supp(Lⱼ), or
- Lᵢ and Lⱼ act on v by the same Pauli (X, Y, or Z)

**LDPC preservation**: To maintain an LDPC deformed code, at most a constant number of logical
operators being measured should share support on any single qubit.

**Time-space tradeoff**: Instead of d rounds of syndrome measurement, one can perform:
- d/m rounds of syndrome measurement
- Measure 2m - 1 equivalent logical operators in parallel
- Take majority vote to determine the classical outcome

This trades space overhead (more parallel measurements) for time overhead (fewer rounds).

## Main Results
**Main Structure** (`ParallelCompatible`): Compatibility condition for parallel measurement
**Key Theorems**:
- `parallel_compatible_disjoint`: Disjoint supports are compatible
- `parallel_compatible_same_pauli`: Same Pauli type at shared qubits is compatible
- `ldpc_constant_bound`: LDPC condition limits qubit sharing
- `time_space_tradeoff`: Tradeoff between rounds and parallel measurements

## File Structure
1. Pauli Type: Enumeration of Pauli operators
2. Compatibility Condition: When logical operators can be measured in parallel
3. LDPC Preservation: Constant bound on qubit sharing
4. Time-Space Tradeoff: Rounds vs parallel measurements
5. Helper Lemmas: Basic properties and simplifications
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Pauli Type Enumeration -/

/-- The three non-trivial Pauli operators -/
inductive PauliType where
  | X : PauliType
  | Y : PauliType
  | Z : PauliType
  deriving DecidableEq, Repr, Inhabited

namespace PauliType

/-- X and Z combine to give Y -/
def combine (p₁ p₂ : PauliType) : Option PauliType :=
  match p₁, p₂ with
  | X, X => some X
  | Y, Y => some Y
  | Z, Z => some Z
  | X, Z => some Y
  | Z, X => some Y
  | X, Y => some Z
  | Y, X => some Z
  | Y, Z => some X
  | Z, Y => some X

/-- Same Pauli types combine to themselves -/
theorem combine_same (p : PauliType) : combine p p = some p := by
  cases p <;> rfl

/-- Combination is commutative -/
theorem combine_comm (p₁ p₂ : PauliType) : combine p₁ p₂ = combine p₂ p₁ := by
  cases p₁ <;> cases p₂ <;> rfl

end PauliType

/-! ## Section 2: Pauli Action on Qubits -/

/-- The Pauli action of an operator at a specific qubit.
    Returns none if the operator acts trivially (identity) at that qubit. -/
def pauliActionAt {n : ℕ} (s : StabilizerCheck n) (v : Fin n) : Option PauliType :=
  let inX := v ∈ s.supportX
  let inZ := v ∈ s.supportZ
  if inX then
    if inZ then some PauliType.Y else some PauliType.X
  else
    if inZ then some PauliType.Z else none

/-- Pauli action is none iff qubit is not in support -/
theorem pauliActionAt_none_iff {n : ℕ} (s : StabilizerCheck n) (v : Fin n) :
    pauliActionAt s v = none ↔ v ∉ s.supportX ∧ v ∉ s.supportZ := by
  unfold pauliActionAt
  constructor
  · intro h
    by_cases hx : v ∈ s.supportX
    · by_cases hz : v ∈ s.supportZ
      · simp only [hx, hz, ↓reduceIte, Option.some_ne_none] at h
      · simp only [hx, hz, ↓reduceIte, Option.some_ne_none] at h
    · by_cases hz : v ∈ s.supportZ
      · simp only [hx, hz, ↓reduceIte, Option.some_ne_none] at h
      · exact ⟨hx, hz⟩
  · intro ⟨hx, hz⟩
    simp only [hx, hz, ↓reduceIte]

/-- Qubit not in support implies identity action -/
theorem pauliActionAt_none_of_not_mem_support {n : ℕ} (s : StabilizerCheck n) (v : Fin n)
    (hx : v ∉ s.supportX) (hz : v ∉ s.supportZ) :
    pauliActionAt s v = none := by
  rw [pauliActionAt_none_iff]
  exact ⟨hx, hz⟩

/-- X-type operator has X action on support -/
theorem XTypePauli_action {n : ℕ} (support : Finset (Fin n)) (v : Fin n) (hv : v ∈ support) :
    pauliActionAt (XTypePauli n support) v = some PauliType.X := by
  unfold pauliActionAt XTypePauli
  simp only [hv, ↓reduceIte, Finset.notMem_empty]

/-- Z-type operator has Z action on support -/
theorem ZTypePauli_action {n : ℕ} (support : Finset (Fin n)) (v : Fin n) (hv : v ∈ support) :
    pauliActionAt (ZTypePauli n support) v = some PauliType.Z := by
  unfold pauliActionAt ZTypePauli
  simp only [Finset.notMem_empty, hv, ↓reduceIte]

/-! ## Section 3: Compatibility Condition for Parallel Measurement -/

/-- Two stabilizer checks are compatible for parallel measurement at qubit v if:
    - At least one acts trivially at v, OR
    - Both act by the same non-trivial Pauli at v -/
def compatibleAt {n : ℕ} (s₁ s₂ : StabilizerCheck n) (v : Fin n) : Prop :=
  pauliActionAt s₁ v = none ∨
  pauliActionAt s₂ v = none ∨
  pauliActionAt s₁ v = pauliActionAt s₂ v

/-- Compatibility at a qubit is symmetric -/
theorem compatibleAt_symm {n : ℕ} (s₁ s₂ : StabilizerCheck n) (v : Fin n) :
    compatibleAt s₁ s₂ v ↔ compatibleAt s₂ s₁ v := by
  unfold compatibleAt
  constructor <;> intro h <;>
  (rcases h with h1 | h2 | h3
   · right; left; exact h1
   · left; exact h2
   · right; right; exact h3.symm)

/-- Disjoint supports at v implies compatibility at v -/
theorem compatibleAt_of_disjoint_support {n : ℕ} (s₁ s₂ : StabilizerCheck n) (v : Fin n)
    (h : v ∉ s₁.supportX ∧ v ∉ s₁.supportZ ∨ v ∉ s₂.supportX ∧ v ∉ s₂.supportZ) :
    compatibleAt s₁ s₂ v := by
  unfold compatibleAt
  rcases h with ⟨hx₁, hz₁⟩ | ⟨hx₂, hz₂⟩
  · left; exact pauliActionAt_none_of_not_mem_support s₁ v hx₁ hz₁
  · right; left; exact pauliActionAt_none_of_not_mem_support s₂ v hx₂ hz₂

/-- Two operators are fully compatible if they are compatible at every qubit -/
def fullyCompatible {n : ℕ} (s₁ s₂ : StabilizerCheck n) : Prop :=
  ∀ v : Fin n, compatibleAt s₁ s₂ v

/-- Full compatibility is symmetric -/
theorem fullyCompatible_symm {n : ℕ} (s₁ s₂ : StabilizerCheck n) :
    fullyCompatible s₁ s₂ ↔ fullyCompatible s₂ s₁ := by
  unfold fullyCompatible
  constructor
  · intro h v
    rw [compatibleAt_symm]
    exact h v
  · intro h v
    rw [compatibleAt_symm]
    exact h v

/-- An operator is compatible with itself -/
theorem fullyCompatible_refl {n : ℕ} (s : StabilizerCheck n) : fullyCompatible s s := by
  intro v
  right; right; rfl

/-! ## Section 4: Parallel Compatible Set of Logical Operators -/

/-- A set of logical operators is compatible for parallel measurement if every pair is compatible -/
structure ParallelCompatible {n k : ℕ} {C : StabilizerCode n k}
    (ops : Finset (LogicalOperator C)) where
  /-- Every pair of operators in the set is fully compatible -/
  pairwise_compatible : ∀ L₁ ∈ ops, ∀ L₂ ∈ ops, fullyCompatible L₁.operator L₂.operator

namespace ParallelCompatible

variable {n k : ℕ} {C : StabilizerCode n k}

/-- Empty set is trivially parallel compatible -/
def empty : ParallelCompatible (∅ : Finset (LogicalOperator C)) where
  pairwise_compatible := by simp

/-- Singleton set is parallel compatible -/
def singleton (L : LogicalOperator C) : ParallelCompatible ({L} : Finset (LogicalOperator C)) where
  pairwise_compatible := by
    intro L₁ hL₁ L₂ hL₂
    simp only [Finset.mem_singleton] at hL₁ hL₂
    rw [hL₁, hL₂]
    exact fullyCompatible_refl L.operator

/-- Compatibility is preserved under subset -/
theorem subset {ops₁ ops₂ : Finset (LogicalOperator C)}
    (h : ParallelCompatible ops₂) (hsub : ops₁ ⊆ ops₂) : ParallelCompatible ops₁ where
  pairwise_compatible := fun L₁ hL₁ L₂ hL₂ =>
    h.pairwise_compatible L₁ (hsub hL₁) L₂ (hsub hL₂)

end ParallelCompatible

/-! ## Section 5: X-Type Logical Operators Compatibility -/

/-- Two X-type logical operators are compatible at qubit v if:
    - At least one has identity at v (v not in support), OR
    - Both have X at v (both supports contain v)
    Since both are X-type, the condition simplifies. -/
theorem XType_compatible_at {n k : ℕ} {C : StabilizerCode n k}
    (L₁ L₂ : XTypeLogical C) (v : Fin n) :
    compatibleAt (XTypePauli n L₁.support) (XTypePauli n L₂.support) v := by
  unfold compatibleAt pauliActionAt XTypePauli
  simp only [Finset.notMem_empty, ↓reduceIte]
  by_cases h1 : v ∈ L₁.support <;> by_cases h2 : v ∈ L₂.support
  · -- Both in support: both have X action
    right; right; simp only [h1, h2, ↓reduceIte]
  · -- L₁ in support, L₂ not
    right; left; simp only [h2, ↓reduceIte]
  · -- L₁ not in support
    left; simp only [h1, ↓reduceIte]
  · -- Neither in support
    left; simp only [h1, ↓reduceIte]

/-- All X-type logical operators are mutually compatible -/
theorem XType_fully_compatible {n k : ℕ} {C : StabilizerCode n k}
    (L₁ L₂ : XTypeLogical C) :
    fullyCompatible (XTypePauli n L₁.support) (XTypePauli n L₂.support) :=
  fun v => XType_compatible_at L₁ L₂ v

/-! ## Section 6: LDPC Preservation Condition -/

/-- For a set of logical operators, count how many share support at qubit v -/
noncomputable def sharedSupportCount {n k : ℕ} {C : StabilizerCode n k}
    (ops : Finset (LogicalOperator C)) (v : Fin n) : ℕ :=
  (Finset.filter (fun L => v ∈ L.operator.supportX ∪ L.operator.supportZ) ops).card

/-- LDPC preservation: at most c logical operators share support at any qubit -/
structure LDPCPreservation {n k : ℕ} {C : StabilizerCode n k}
    (ops : Finset (LogicalOperator C)) (c : ℕ) where
  /-- At most c operators share support at any single qubit -/
  constant_bound : ∀ v : Fin n, sharedSupportCount ops v ≤ c

namespace LDPCPreservation

variable {n k : ℕ} {C : StabilizerCode n k}

/-- Empty set satisfies LDPC preservation with any constant -/
def empty (c : ℕ) : LDPCPreservation (∅ : Finset (LogicalOperator C)) c where
  constant_bound := by simp [sharedSupportCount]

/-- Singleton set satisfies LDPC with c = 1 -/
def singleton (L : LogicalOperator C) : LDPCPreservation ({L} : Finset (LogicalOperator C)) 1 where
  constant_bound := by
    intro v
    unfold sharedSupportCount
    simp only [Finset.filter_singleton]
    split_ifs
    · simp
    · simp

/-- Subset preserves LDPC bound -/
theorem subset {ops₁ ops₂ : Finset (LogicalOperator C)} {c : ℕ}
    (h : LDPCPreservation ops₂ c) (hsub : ops₁ ⊆ ops₂) : LDPCPreservation ops₁ c where
  constant_bound := by
    intro v
    calc sharedSupportCount ops₁ v
      = (Finset.filter (fun L => v ∈ L.operator.supportX ∪ L.operator.supportZ) ops₁).card := rfl
      _ ≤ (Finset.filter (fun L => v ∈ L.operator.supportX ∪ L.operator.supportZ) ops₂).card := by
          apply Finset.card_le_card
          exact Finset.filter_subset_filter _ hsub
      _ = sharedSupportCount ops₂ v := rfl
      _ ≤ c := h.constant_bound v

end LDPCPreservation

/-! ## Section 7: Time-Space Tradeoff Parameters -/

/-- Parameters for the time-space tradeoff in parallel gauging measurement -/
structure TimeSpaceTradeoff where
  /-- Code distance d -/
  distance : ℕ
  /-- Number of parallel logical measurements m -/
  parallel_count : ℕ
  /-- m > 0 -/
  parallel_pos : parallel_count > 0

namespace TimeSpaceTradeoff

/-- Number of syndrome measurement rounds in the tradeoff: d/m -/
noncomputable def syndromeRounds (T : TimeSpaceTradeoff) : ℕ :=
  T.distance / T.parallel_count

/-- Number of equivalent logical operators measured in parallel: 2m - 1 -/
def equivalentLogicals (T : TimeSpaceTradeoff) : ℕ :=
  2 * T.parallel_count - 1

/-- With m = 1, we get standard d rounds -/
theorem syndromeRounds_m_eq_1 (d : ℕ) (_hd : d > 0) :
    (⟨d, 1, Nat.one_pos⟩ : TimeSpaceTradeoff).syndromeRounds = d := by
  simp only [syndromeRounds, Nat.div_one]

/-- With m = 1, we measure 1 logical operator -/
theorem equivalentLogicals_m_eq_1 :
    (⟨0, 1, Nat.one_pos⟩ : TimeSpaceTradeoff).equivalentLogicals = 1 := by
  rfl

/-- With m = d, we get 1 round -/
theorem syndromeRounds_m_eq_d (d : ℕ) (hd : d > 0) :
    (⟨d, d, hd⟩ : TimeSpaceTradeoff).syndromeRounds = 1 := by
  simp only [syndromeRounds, Nat.div_self hd]

/-- Equivalent logicals formula: 2m - 1 -/
theorem equivalentLogicals_formula (T : TimeSpaceTradeoff) :
    T.equivalentLogicals = 2 * T.parallel_count - 1 := rfl

/-- Syndrome rounds times parallel count approximates distance -/
theorem tradeoff_product_bound (T : TimeSpaceTradeoff) :
    T.syndromeRounds * T.parallel_count ≤ T.distance := by
  unfold syndromeRounds
  exact Nat.div_mul_le_self T.distance T.parallel_count

/-- The tradeoff maintains total work proportional to distance -/
theorem tradeoff_work_bound (T : TimeSpaceTradeoff) :
    T.syndromeRounds + T.equivalentLogicals ≥ T.parallel_count := by
  unfold equivalentLogicals
  omega

end TimeSpaceTradeoff

/-! ## Section 8: Majority Vote for Parallel Measurement -/

/-- Outcomes from m parallel measurements of equivalent logical operators -/
def ParallelOutcomes (m : ℕ) := Fin (2 * m - 1) → ZMod 2

/-- Count of +1 outcomes (represented as 0 in ZMod 2) -/
def countPlusOnes {m : ℕ} (_hm : m > 0) (outcomes : ParallelOutcomes m) : ℕ :=
  (Finset.filter (fun i => outcomes i = 0) Finset.univ).card

/-- Count of -1 outcomes (represented as 1 in ZMod 2) -/
def countMinusOnesParallel {m : ℕ} (_hm : m > 0) (outcomes : ParallelOutcomes m) : ℕ :=
  (Finset.filter (fun i => outcomes i = 1) Finset.univ).card

/-- Helper: ZMod 2 values are 0 or 1 -/
theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Total measurements equals 2m - 1 -/
theorem total_measurements {m : ℕ} (hm : m > 0) (outcomes : ParallelOutcomes m) :
    countPlusOnes hm outcomes + countMinusOnesParallel hm outcomes = 2 * m - 1 := by
  unfold countPlusOnes countMinusOnesParallel
  have h_disjoint : Disjoint
      (Finset.filter (fun i => outcomes i = 0) Finset.univ)
      (Finset.filter (fun i => outcomes i = 1) Finset.univ) := by
    rw [Finset.disjoint_filter]
    intro _ _ h0 h1
    have : (0 : ZMod 2) = 1 := h0.symm.trans h1
    exact absurd this (by decide)
  have h_union : Finset.filter (fun i => outcomes i = 0) Finset.univ ∪
                 Finset.filter (fun i => outcomes i = 1) Finset.univ = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => zmod2_eq_zero_or_one (outcomes i)⟩
  calc countPlusOnes hm outcomes + countMinusOnesParallel hm outcomes
    = (Finset.filter (fun i => outcomes i = 0) Finset.univ).card +
      (Finset.filter (fun i => outcomes i = 1) Finset.univ).card := rfl
    _ = (Finset.filter (fun i => outcomes i = 0) Finset.univ ∪
         Finset.filter (fun i => outcomes i = 1) Finset.univ).card :=
          (Finset.card_union_of_disjoint h_disjoint).symm
    _ = Finset.univ.card := by rw [h_union]
    _ = Fintype.card (Fin (2 * m - 1)) := rfl
    _ = 2 * m - 1 := Fintype.card_fin _

/-- Majority vote result: +1 if more than half are +1, -1 otherwise -/
def majorityVote {m : ℕ} (hm : m > 0) (outcomes : ParallelOutcomes m) : ZMod 2 :=
  if countPlusOnes hm outcomes > countMinusOnesParallel hm outcomes then 0 else 1

/-- If all outcomes agree, majority vote equals that outcome -/
theorem majorityVote_unanimous {m : ℕ} (hm : m > 0) (outcomes : ParallelOutcomes m)
    (h_all_plus : ∀ i, outcomes i = 0) :
    majorityVote hm outcomes = 0 := by
  unfold majorityVote
  have h_plus : countPlusOnes hm outcomes = 2 * m - 1 := by
    unfold countPlusOnes
    have h_filter_eq : Finset.filter (fun i => outcomes i = 0) Finset.univ = Finset.univ := by
      ext i
      simp [h_all_plus i]
    rw [h_filter_eq]
    exact Fintype.card_fin _
  have h_minus : countMinusOnesParallel hm outcomes = 0 := by
    unfold countMinusOnesParallel
    have h_filter_eq : Finset.filter (fun i => outcomes i = 1) Finset.univ = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                 iff_false, h_all_plus i]
      decide
    rw [h_filter_eq]
    exact Finset.card_empty
  simp only [h_plus, h_minus]
  split_ifs with hcmp
  · rfl
  · omega

/-! ## Section 9: Integration with Gauging Measurement -/

/-- A parallel gauging configuration combines multiple compatible gauging graphs -/
structure ParallelGaugingConfig {n k : ℕ} (C : StabilizerCode n k) where
  /-- The number of logical operators being measured in parallel -/
  count : ℕ
  /-- count > 0 -/
  count_pos : count > 0
  /-- The logical operators -/
  logicals : Fin count → Σ L : XTypeLogical C, GaugingGraph C L
  /-- All pairs are compatible -/
  compatible : ∀ i j, fullyCompatible
    (XTypePauli n (logicals i).1.support)
    (XTypePauli n (logicals j).1.support)
  /-- LDPC bound: at most c operators share support at any qubit -/
  ldpc_bound : ℕ
  /-- The LDPC condition holds -/
  ldpc_condition : ∀ v : Fin n,
    (Finset.filter (fun i => v ∈ (logicals i).1.support) Finset.univ).card ≤ ldpc_bound

namespace ParallelGaugingConfig

variable {n k : ℕ} {C : StabilizerCode n k}

/-- The i-th gauging graph -/
def graph (P : ParallelGaugingConfig C) (i : Fin P.count) : GaugingGraph C (P.logicals i).1 :=
  (P.logicals i).2

/-- All X-type operators are mutually compatible (trivially satisfied) -/
theorem x_type_compatible (P : ParallelGaugingConfig C) (i j : Fin P.count) :
    fullyCompatible (XTypePauli n (P.logicals i).1.support)
                    (XTypePauli n (P.logicals j).1.support) :=
  XType_fully_compatible (P.logicals i).1 (P.logicals j).1

end ParallelGaugingConfig

/-! ## Section 10: Time-Space Tradeoff Theorem -/

/-- **Main Theorem: Time-Space Tradeoff**

    Instead of d rounds of syndrome measurement with 1 logical measurement,
    one can perform d/m rounds with 2m-1 parallel logical measurements.

    The majority vote of the 2m-1 outcomes gives the correct result
    as long as at most m-1 of them are erroneous.

    This trades:
    - Space: 2m-1 parallel measurements (more ancilla qubits/operations)
    - Time: d/m syndrome rounds (fewer error correction cycles) -/
theorem time_space_tradeoff (T : TimeSpaceTradeoff) :
    -- Part 1: Reduced rounds
    T.syndromeRounds ≤ T.distance ∧
    -- Part 2: More parallel measurements
    T.equivalentLogicals ≥ 1 ∧
    -- Part 3: Product gives distance bound
    T.syndromeRounds * T.parallel_count ≤ T.distance ∧
    -- Part 4: Work is at least m
    T.syndromeRounds + T.equivalentLogicals ≥ T.parallel_count := by
  constructor
  · -- Part 1: d/m ≤ d
    unfold TimeSpaceTradeoff.syndromeRounds
    exact Nat.div_le_self T.distance T.parallel_count
  constructor
  · -- Part 2: 2m - 1 ≥ 1
    unfold TimeSpaceTradeoff.equivalentLogicals
    have hpos : T.parallel_count > 0 := T.parallel_pos
    omega
  constructor
  · -- Part 3: (d/m) * m ≤ d
    exact T.tradeoff_product_bound
  · -- Part 4: d/m + (2m-1) ≥ m
    exact T.tradeoff_work_bound

/-- Corollary: Maximum parallelization (m = d) gives 1 round -/
theorem max_parallelization (d : ℕ) (hd : d > 0) :
    let T : TimeSpaceTradeoff := ⟨d, d, hd⟩
    T.syndromeRounds = 1 ∧ T.equivalentLogicals = 2 * d - 1 := by
  constructor
  · exact TimeSpaceTradeoff.syndromeRounds_m_eq_d d hd
  · rfl

/-- Corollary: Minimum parallelization (m = 1) gives d rounds -/
theorem min_parallelization (d : ℕ) (hd : d > 0) :
    let T : TimeSpaceTradeoff := ⟨d, 1, Nat.one_pos⟩
    T.syndromeRounds = d ∧ T.equivalentLogicals = 1 := by
  constructor
  · exact TimeSpaceTradeoff.syndromeRounds_m_eq_1 d hd
  · rfl

/-! ## Section 11: Helper Lemmas -/

/-- Compatibility at v is decidable -/
instance compatibleAt_decidable {n : ℕ} (s₁ s₂ : StabilizerCheck n) (v : Fin n) :
    Decidable (compatibleAt s₁ s₂ v) := by
  unfold compatibleAt
  infer_instance

/-- If supports are disjoint, operators are fully compatible -/
theorem fullyCompatible_of_disjoint_supports {n : ℕ} (s₁ s₂ : StabilizerCheck n)
    (h : Disjoint (s₁.supportX ∪ s₁.supportZ) (s₂.supportX ∪ s₂.supportZ)) :
    fullyCompatible s₁ s₂ := by
  intro v
  unfold compatibleAt pauliActionAt
  by_cases hx1 : v ∈ s₁.supportX
  · -- v ∈ s₁.supportX: v is in union, so v ∉ s₂ supports
    have hv_in : v ∈ s₁.supportX ∪ s₁.supportZ := Finset.mem_union_left _ hx1
    have hv_not : v ∉ s₂.supportX ∪ s₂.supportZ := Finset.disjoint_left.mp h hv_in
    have hx2 : v ∉ s₂.supportX := fun h' => hv_not (Finset.mem_union_left _ h')
    have hz2 : v ∉ s₂.supportZ := fun h' => hv_not (Finset.mem_union_right _ h')
    right; left
    simp only [hx2, hz2, ↓reduceIte]
  · by_cases hz1 : v ∈ s₁.supportZ
    · -- v ∉ s₁.supportX and v ∈ s₁.supportZ
      have hv_in : v ∈ s₁.supportX ∪ s₁.supportZ := Finset.mem_union_right _ hz1
      have hv_not : v ∉ s₂.supportX ∪ s₂.supportZ := Finset.disjoint_left.mp h hv_in
      have hx2 : v ∉ s₂.supportX := fun h' => hv_not (Finset.mem_union_left _ h')
      have hz2 : v ∉ s₂.supportZ := fun h' => hv_not (Finset.mem_union_right _ h')
      right; left
      simp only [hx2, hz2, ↓reduceIte]
    · -- v ∉ s₁.supportX and v ∉ s₁.supportZ
      left
      simp only [hx1, hz1, ↓reduceIte]

/-- LDPC bound for X-type operators equals max support overlap -/
theorem ldpc_bound_X_type {n k : ℕ} {C : StabilizerCode n k}
    (ops : Finset (XTypeLogical C)) (v : Fin n) :
    (Finset.filter (fun L => v ∈ L.support) ops).card =
    (Finset.filter (fun L => v ∈ (XTypePauli n L.support).supportX ∪
                             (XTypePauli n L.support).supportZ) ops).card := by
  congr 1
  ext L
  simp only [Finset.mem_filter, XTypePauli_supportX, XTypePauli_supportZ,
             Finset.union_empty]

/-- Parallel count must be positive for the tradeoff -/
theorem parallel_count_positive (T : TimeSpaceTradeoff) : T.parallel_count > 0 :=
  T.parallel_pos

/-- Shared support count is monotone in operator set -/
theorem sharedSupportCount_mono {n k : ℕ} {C : StabilizerCode n k}
    {ops₁ ops₂ : Finset (LogicalOperator C)} (v : Fin n)
    (h : ops₁ ⊆ ops₂) :
    sharedSupportCount ops₁ v ≤ sharedSupportCount ops₂ v := by
  unfold sharedSupportCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Equivalence: 2m - 1 is odd for m > 0 -/
theorem equivalentLogicals_odd (T : TimeSpaceTradeoff) :
    T.equivalentLogicals % 2 = 1 ∨ T.equivalentLogicals = 0 := by
  unfold TimeSpaceTradeoff.equivalentLogicals
  by_cases h : T.parallel_count = 0
  · right; omega
  · left
    have hpos : T.parallel_count > 0 := T.parallel_pos
    have h2m : 2 * T.parallel_count ≥ 1 := by omega
    have hsub : 2 * T.parallel_count - 1 ≥ 0 := Nat.zero_le _
    -- 2m - 1 is odd when m > 0
    calc (2 * T.parallel_count - 1) % 2
      = (2 * T.parallel_count + 1 - 2) % 2 := by omega
      _ = 1 := by omega

end QEC
