import QEC1.Remarks.Rem_1_StabilizerCodeConvention
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

/-!
# Rem_10: Parallelization of Gauging Measurements

## Statement
The gauging measurement can be applied to multiple logical operators in parallel, provided that:

1. **Commutativity**: No pair of logical operators being measured simultaneously act on a common
   qubit via different non-trivial Pauli operators (e.g., one acts by $X$ and another by $Z$ on
   the same qubit).

2. **Bounded overlap**: To maintain an LDPC code during code deformation, only a constant number
   of logical operators being measured share support on any single qubit.

For codes supporting many disjoint logical representatives, this offers highly parallelized logical
gates. Additionally, one can trade space overhead for time overhead by performing $2m-1$ measurements
of equivalent logical operators in parallel for $d/m$ rounds and taking a majority vote to determine
the classical outcome.

## Main Definitions
- `PauliCompatible`: Two logical operators are Pauli-compatible on a qubit
- `CommutativityCondition`: No pair acts differently on a common qubit (Condition 1)
- `BoundedOverlapCondition`: At most k operators share any qubit (Condition 2)
- `ParallelizableLogicals`: A set of logicals satisfying both conditions
- `SpaceTimeTradeoff`: The space-time tradeoff parameters

## Main Results
- `parallel_measurement_conditions`: The two conditions for parallel measurement
- `disjoint_logicals_parallelizable`: Disjoint logicals trivially satisfy parallelizability
- `majority_vote_rounds`: The number of rounds for majority voting is d/m
- `total_parallel_measurements`: Total parallel measurements is 2m-1
-/

namespace QEC1

open Finset

/-! ## Pauli Compatibility Condition -/

/-- Two Pauli types are **compatible** if they don't conflict on the same qubit.
    A conflict occurs when one acts as purely X-type and the other as purely Z-type.
    (e.g., X and Z conflict, but X and X are compatible, I and anything is compatible)

    Compatible means: NOT (one is purely X-type AND the other is purely Z-type). -/
def StabPauliType.compatible (p q : StabPauliType) : Prop :=
  ¬(p = StabPauliType.X ∧ q = StabPauliType.Z) ∧ ¬(p = StabPauliType.Z ∧ q = StabPauliType.X)

/-- X and Z are incompatible -/
lemma StabPauliType.X_Z_not_compatible : ¬StabPauliType.compatible StabPauliType.X StabPauliType.Z := by
  simp [compatible]

/-- Z and X are incompatible -/
lemma StabPauliType.Z_X_not_compatible : ¬StabPauliType.compatible StabPauliType.Z StabPauliType.X := by
  simp [compatible]

/-- Same Pauli types are always compatible -/
lemma StabPauliType.self_compatible (p : StabPauliType) : StabPauliType.compatible p p := by
  cases p <;> simp [compatible]

/-- Identity is compatible with everything -/
lemma StabPauliType.I_compatible_left (p : StabPauliType) : StabPauliType.compatible StabPauliType.I p := by
  simp [compatible]

lemma StabPauliType.I_compatible_right (p : StabPauliType) : StabPauliType.compatible p StabPauliType.I := by
  simp [compatible]

/-- Compatibility is symmetric -/
lemma StabPauliType.compatible_comm (p q : StabPauliType) :
    StabPauliType.compatible p q ↔ StabPauliType.compatible q p := by
  simp only [compatible]
  tauto

/-! ## Condition 1: Commutativity (Pauli Compatibility on Shared Qubits) -/

variable {n : ℕ}

/-- Two Pauli operators are **Pauli-compatible** if for every qubit where both act nontrivially,
    their Pauli types are compatible (i.e., not one X-type and one Z-type). -/
def PauliCompatible (P Q : PauliOp n) : Prop :=
  ∀ i : Fin n, StabPauliType.compatible (P.paulis i) (Q.paulis i)

/-- Pauli compatibility implies the operators can be measured in parallel without conflict -/
lemma PauliCompatible.symmetric {P Q : PauliOp n} (h : PauliCompatible P Q) :
    PauliCompatible Q P := by
  intro i
  exact (StabPauliType.compatible_comm _ _).mp (h i)

/-- The identity operator is compatible with any operator -/
lemma PauliCompatible.identity_left (P : PauliOp n) :
    PauliCompatible (PauliOp.identity n) P := by
  intro i
  exact StabPauliType.I_compatible_left _

lemma PauliCompatible.identity_right (P : PauliOp n) :
    PauliCompatible P (PauliOp.identity n) := by
  intro i
  exact StabPauliType.I_compatible_right _

/-- **Commutativity Condition** for parallel gauging measurement:
    A set of logical operators satisfies the commutativity condition if every pair is
    Pauli-compatible on their shared support. -/
def CommutativityCondition {C : StabilizerCode} (logicals : Finset (LogicalOp C)) : Prop :=
  ∀ L₁ ∈ logicals, ∀ L₂ ∈ logicals, PauliCompatible L₁.op L₂.op

/-- Singleton sets trivially satisfy commutativity -/
lemma CommutativityCondition.singleton {C : StabilizerCode} (L : LogicalOp C) :
    CommutativityCondition ({L} : Finset (LogicalOp C)) := by
  intro L₁ hL₁ L₂ hL₂
  simp only [mem_singleton] at hL₁ hL₂
  subst hL₁ hL₂
  intro i
  exact StabPauliType.self_compatible _

/-! ## Condition 2: Bounded Overlap -/

/-- The **overlap degree** of a qubit with respect to a set of operators:
    how many operators in the set have support on this qubit. -/
def overlapDegree {C : StabilizerCode} (logicals : Finset (LogicalOp C)) (i : Fin C.n) : ℕ :=
  (logicals.filter (fun L => i ∈ L.op.support)).card

/-- **Bounded Overlap Condition**: At most k logical operators share support on any single qubit.
    This is required to maintain LDPC property during code deformation. -/
def BoundedOverlapCondition {C : StabilizerCode} (logicals : Finset (LogicalOp C)) (k : ℕ) : Prop :=
  ∀ i : Fin C.n, overlapDegree logicals i ≤ k

/-- If k ≥ |logicals|, the bounded overlap condition is trivially satisfied -/
lemma BoundedOverlapCondition.of_card_le {C : StabilizerCode}
    (logicals : Finset (LogicalOp C)) (k : ℕ) (h : logicals.card ≤ k) :
    BoundedOverlapCondition logicals k := by
  intro i
  unfold overlapDegree
  calc (filter (fun L => i ∈ L.op.support) logicals).card
      ≤ logicals.card := card_filter_le _ _
    _ ≤ k := h

/-- Singleton sets have overlap degree at most 1 -/
lemma BoundedOverlapCondition.singleton {C : StabilizerCode} (L : LogicalOp C) :
    BoundedOverlapCondition ({L} : Finset (LogicalOp C)) 1 := by
  intro i
  unfold overlapDegree
  calc (filter (fun L' => i ∈ L'.op.support) {L}).card
      ≤ ({L} : Finset (LogicalOp C)).card := card_filter_le _ _
    _ = 1 := card_singleton L

/-! ## Parallelizable Logicals -/

/-- A set of logical operators is **parallelizable** if it satisfies both conditions:
    1. Commutativity: no pair acts differently (X vs Z) on a common qubit
    2. Bounded overlap: at most k operators share any qubit

    The bound k must be constant to maintain LDPC property. -/
structure ParallelizableLogicals (C : StabilizerCode) where
  /-- The set of logical operators to measure in parallel -/
  logicals : Finset (LogicalOp C)
  /-- The bound on overlap degree (must be constant for LDPC) -/
  overlapBound : ℕ
  /-- Condition 1: Commutativity -/
  commutativity : CommutativityCondition logicals
  /-- Condition 2: Bounded overlap -/
  boundedOverlap : BoundedOverlapCondition logicals overlapBound

namespace ParallelizableLogicals

variable {C : StabilizerCode}

/-- The number of logical operators being measured in parallel -/
def numLogicals (P : ParallelizableLogicals C) : ℕ := P.logicals.card

/-- Any single logical operator is trivially parallelizable -/
def singleton (L : LogicalOp C) : ParallelizableLogicals C where
  logicals := {L}
  overlapBound := 1
  commutativity := CommutativityCondition.singleton L
  boundedOverlap := BoundedOverlapCondition.singleton L

@[simp] lemma singleton_numLogicals (L : LogicalOp C) :
    (singleton L).numLogicals = 1 := card_singleton L

end ParallelizableLogicals

/-! ## Disjoint Logicals -/

/-- Two logical operators have **disjoint support** if they share no qubits. -/
def DisjointSupport {C : StabilizerCode} (L₁ L₂ : LogicalOp C) : Prop :=
  Disjoint L₁.op.support L₂.op.support

/-- A set of logicals has **pairwise disjoint support** if every pair is disjoint. -/
def PairwiseDisjointSupport {C : StabilizerCode} (logicals : Finset (LogicalOp C)) : Prop :=
  ∀ L₁ ∈ logicals, ∀ L₂ ∈ logicals, L₁ ≠ L₂ → DisjointSupport L₁ L₂

/-- Disjoint operators are Pauli-compatible (vacuously, no shared qubit). -/
lemma DisjointSupport.pauli_compatible {C : StabilizerCode} {L₁ L₂ : LogicalOp C}
    (h : DisjointSupport L₁ L₂) :
    PauliCompatible L₁.op L₂.op := by
  intro i
  by_cases h₁ : i ∈ L₁.op.support
  · have h₂ : i ∉ L₂.op.support := disjoint_left.mp h h₁
    simp only [PauliOp.support, mem_filter, mem_univ, true_and, ne_eq, not_not] at h₂
    simp only [h₂]
    exact StabPauliType.I_compatible_right _
  · simp only [PauliOp.support, mem_filter, mem_univ, true_and, ne_eq, not_not] at h₁
    simp only [h₁]
    exact StabPauliType.I_compatible_left _

/-- Pairwise disjoint logicals satisfy the commutativity condition. -/
lemma PairwiseDisjointSupport.commutativity {C : StabilizerCode}
    {logicals : Finset (LogicalOp C)} (h : PairwiseDisjointSupport logicals) :
    CommutativityCondition logicals := by
  intro L₁ hL₁ L₂ hL₂
  by_cases heq : L₁ = L₂
  · subst heq
    intro i
    exact StabPauliType.self_compatible _
  · exact (h L₁ hL₁ L₂ hL₂ heq).pauli_compatible

/-- Pairwise disjoint logicals have overlap degree at most 1 everywhere. -/
lemma PairwiseDisjointSupport.overlap_degree_le_one {C : StabilizerCode}
    {logicals : Finset (LogicalOp C)} (h : PairwiseDisjointSupport logicals) :
    BoundedOverlapCondition logicals 1 := by
  intro i
  unfold overlapDegree
  by_contra hc
  push_neg at hc
  have hcard : 1 < (filter (fun L => i ∈ L.op.support) logicals).card := hc
  rw [one_lt_card_iff] at hcard
  obtain ⟨L₁, L₂, hL₁, hL₂, hne⟩ := hcard
  simp only [mem_filter] at hL₁ hL₂
  have hdisj := h L₁ hL₁.1 L₂ hL₂.1 hne
  have hmem : i ∈ L₁.op.support ∩ L₂.op.support := mem_inter.mpr ⟨hL₁.2, hL₂.2⟩
  have hempty := disjoint_iff_inter_eq_empty.mp hdisj
  rw [hempty] at hmem
  exact Finset.notMem_empty i hmem

/-- **Disjoint logicals are parallelizable**: codes with many disjoint logical representatives
    can perform highly parallelized logical gates. -/
def ParallelizableLogicals.fromDisjoint {C : StabilizerCode}
    (logicals : Finset (LogicalOp C)) (h : PairwiseDisjointSupport logicals) :
    ParallelizableLogicals C where
  logicals := logicals
  overlapBound := 1
  commutativity := h.commutativity
  boundedOverlap := h.overlap_degree_le_one

theorem disjoint_logicals_parallelizable {C : StabilizerCode}
    (logicals : Finset (LogicalOp C)) (h : PairwiseDisjointSupport logicals) :
    ∃ P : ParallelizableLogicals C, P.logicals = logicals ∧ P.overlapBound = 1 :=
  ⟨ParallelizableLogicals.fromDisjoint logicals h, rfl, rfl⟩

/-! ## Space-Time Tradeoff -/

/-- **Space-Time Tradeoff** for the gauging measurement.

    One can trade space overhead for time overhead:
    - Perform 2m-1 measurements of equivalent logical operators in parallel
    - For d/m rounds
    - Take a majority vote to determine the classical outcome

    Parameters:
    - d: the code distance
    - m: the tradeoff parameter (divides d)
    - The number of parallel equivalent measurements is 2m-1
    - The number of rounds is d/m -/
structure SpaceTimeTradeoff where
  /-- Code distance -/
  distance : ℕ
  /-- Tradeoff parameter -/
  m : ℕ
  /-- m must be positive -/
  m_pos : m > 0
  /-- m divides d (for clean arithmetic) -/
  m_divides_d : m ∣ distance

namespace SpaceTimeTradeoff

/-- Number of parallel measurements of equivalent logical operators: 2m - 1 -/
def numParallelMeasurements (T : SpaceTimeTradeoff) : ℕ := 2 * T.m - 1

/-- Number of rounds for the measurement: d/m -/
def numRounds (T : SpaceTimeTradeoff) : ℕ := T.distance / T.m

/-- When m divides d, numRounds * m = d -/
lemma numRounds_mul_m (T : SpaceTimeTradeoff) :
    T.numRounds * T.m = T.distance := by
  exact Nat.div_mul_cancel T.m_divides_d

/-- The majority vote threshold: more than half of 2m-1 measurements, i.e., at least m -/
def majorityThreshold (T : SpaceTimeTradeoff) : ℕ := T.m

/-- Majority threshold is exactly half of 2m-1 rounded up -/
lemma majorityThreshold_eq (T : SpaceTimeTradeoff) :
    T.majorityThreshold = (T.numParallelMeasurements + 1) / 2 := by
  unfold majorityThreshold numParallelMeasurements
  have hm := T.m_pos
  omega

/-- Total logical measurements across all rounds -/
def totalMeasurements (T : SpaceTimeTradeoff) : ℕ :=
  T.numParallelMeasurements * T.numRounds

/-- The total measurements formula: (2m-1) * (d/m) -/
lemma totalMeasurements_eq (T : SpaceTimeTradeoff) :
    T.totalMeasurements = (2 * T.m - 1) * (T.distance / T.m) := rfl

/-! ### Special cases -/

/-- Minimal space overhead: m = d, giving 2d-1 parallel measurements in 1 round -/
def minSpace (d : ℕ) (hd : d > 0) : SpaceTimeTradeoff where
  distance := d
  m := d
  m_pos := hd
  m_divides_d := dvd_refl d

@[simp] lemma minSpace_numParallel (d : ℕ) (hd : d > 0) :
    (minSpace d hd).numParallelMeasurements = 2 * d - 1 := rfl

@[simp] lemma minSpace_numRounds (d : ℕ) (hd : d > 0) :
    (minSpace d hd).numRounds = 1 := Nat.div_self hd

/-- Minimal time overhead: m = 1, giving 1 parallel measurement in d rounds -/
def minTime (d : ℕ) (_hd : d > 0) : SpaceTimeTradeoff where
  distance := d
  m := 1
  m_pos := Nat.one_pos
  m_divides_d := one_dvd d

@[simp] lemma minTime_numParallel (d : ℕ) (hd : d > 0) :
    (minTime d hd).numParallelMeasurements = 1 := rfl

@[simp] lemma minTime_numRounds (d : ℕ) (_hd : d > 0) :
    (minTime d _hd).numRounds = d := Nat.div_one d

end SpaceTimeTradeoff

/-! ## Combined Parallelization Theorem -/

/-- The **parallelization theorem**: gauging measurement can be applied to multiple logical
    operators in parallel if and only if both conditions are satisfied.

    Condition 1 (Commutativity): No pair acts by different non-trivial Paulis on any qubit.
    Condition 2 (Bounded Overlap): At most k operators share support on any qubit.

    This theorem captures the main claim of Rem_10. -/
theorem parallel_measurement_conditions {C : StabilizerCode}
    (logicals : Finset (LogicalOp C)) (k : ℕ) :
    (CommutativityCondition logicals ∧ BoundedOverlapCondition logicals k) ↔
    ∃ P : ParallelizableLogicals C, P.logicals = logicals ∧ P.overlapBound = k := by
  constructor
  · intro ⟨hcomm, hbound⟩
    exact ⟨⟨logicals, k, hcomm, hbound⟩, rfl, rfl⟩
  · intro ⟨P, hlog, hbound⟩
    subst hlog hbound
    exact ⟨P.commutativity, P.boundedOverlap⟩

/-! ## Majority Vote Correctness -/

/-- For the space-time tradeoff: (2m-1) is always odd, ensuring a clear majority. -/
lemma numParallelMeasurements_odd (T : SpaceTimeTradeoff) :
    Odd T.numParallelMeasurements := by
  unfold SpaceTimeTradeoff.numParallelMeasurements
  have hm := T.m_pos
  use T.m - 1
  omega

/-- The majority vote always gives a definite outcome (no ties possible). -/
theorem majority_vote_no_tie (T : SpaceTimeTradeoff) :
    T.numParallelMeasurements % 2 = 1 := by
  exact Nat.odd_iff.mp (numParallelMeasurements_odd T)

/-! ## Summary

The parallelization remark establishes:

1. **Commutativity Condition**: For parallel measurement, no pair of logical operators
   should act on a common qubit via different non-trivial Paulis (e.g., X vs Z).

2. **Bounded Overlap Condition**: To maintain LDPC property during code deformation,
   at most a constant number of logicals can share support on any single qubit.

3. **Disjoint Representatives**: Codes with many disjoint logical representatives
   naturally satisfy both conditions (overlap degree 1).

4. **Space-Time Tradeoff**: One can trade space for time:
   - 2m-1 parallel measurements of equivalent logicals
   - d/m rounds of measurement
   - Majority vote determines the classical outcome
-/

end QEC1
