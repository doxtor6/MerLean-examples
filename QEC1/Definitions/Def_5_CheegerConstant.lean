import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Cheeger Constant (Definition 5)

## Statement
Let $G = (V, E)$ be a finite graph with vertex set $V$ and edge set $E$.

For a subset $S \subseteq V$, the **edge boundary** of $S$ is:
$$\delta(S) = \{e \in E : |e \cap S| = 1\}$$
the set of edges with exactly one endpoint in S.

The **Cheeger constant** (isoperimetric number/expansion) of G is:
$$h(G) = \min_{\substack{S \subseteq V \\ 0 < |S| \leq |V|/2}} \frac{|\delta(S)|}{|S|}$$

## Main Results
**Main Definitions**: edgeBoundary, cheegerConstant
**Main Properties**: cheegerConstant_nonneg, edgeBoundary_ge_cheeger_mul_card

## File Structure
1. Edge Boundary Definition
2. Cheeger Constant
3. Basic Properties
4. Expander Definition
5. Helper Lemmas
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Edge Boundary Definition -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge has exactly one endpoint in S if one vertex is in S and the other is not. -/
def edgeHasOneEndpointIn (S : Finset V) (e : Sym2 V) : Prop :=
  ∃ v w : V, e = s(v, w) ∧ ((v ∈ S ∧ w ∉ S) ∨ (v ∉ S ∧ w ∈ S))

/-- Decidability for edgeHasOneEndpointIn -/
instance (S : Finset V) (e : Sym2 V) : Decidable (edgeHasOneEndpointIn S e) := by
  unfold edgeHasOneEndpointIn
  infer_instance

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edge boundary δ(S) of a subset S ⊆ V.
    This is the set of edges with exactly one endpoint in S. -/
def edgeBoundary (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => edgeHasOneEndpointIn S e)

/-! ## Section 2: Edge Boundary Size -/

/-- The number of edges in the boundary of S -/
noncomputable def edgeBoundaryCard (S : Finset V) : ℕ :=
  (edgeBoundary G S).card

/-- The expansion ratio |δ(S)|/|S| for a nonempty subset S -/
noncomputable def expansionRatio (S : Finset V) (_hS : S.Nonempty) : ℚ :=
  (edgeBoundaryCard G S : ℚ) / S.card

/-! ## Section 3: Valid Subsets for Cheeger -/

/-- A subset S is valid for the Cheeger definition if:
    - S is nonempty (0 < |S|)
    - |S| ≤ |V|/2 -/
def isValidCheegerSubset (S : Finset V) : Prop :=
  S.Nonempty ∧ 2 * S.card ≤ Fintype.card V

/-- Decidability for valid Cheeger subsets -/
instance (S : Finset V) : Decidable (isValidCheegerSubset S) := by
  unfold isValidCheegerSubset
  infer_instance

/-- The set of all valid subsets for computing the Cheeger constant -/
def validCheegerSubsets : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun S => isValidCheegerSubset S)

/-! ## Section 4: Cheeger Constant Definition -/

/-- The Cheeger constant h(G) is the minimum expansion ratio over valid subsets.
    If there are no valid subsets (i.e., |V| ≤ 1), we define h(G) = 0.

    h(G) = min_{S : 0 < |S| ≤ |V|/2} |δ(S)|/|S| -/
noncomputable def cheegerConstant : ℚ :=
  if h : (validCheegerSubsets (V := V)).Nonempty then
    (validCheegerSubsets (V := V)).inf' h (fun S =>
      if hS : S.Nonempty then expansionRatio G S hS else 0)
  else 0

/-! ## Section 5: Expander Definition -/

/-- A graph is an (c, n)-expander if |V| ≥ n and h(G) ≥ c -/
def isExpander (c : ℚ) (n : ℕ) : Prop :=
  Fintype.card V ≥ n ∧ cheegerConstant G ≥ c

/-- A graph is an expander (for some constant c > 0) -/
def isExpanderGraph : Prop :=
  ∃ c : ℚ, c > 0 ∧ cheegerConstant G ≥ c

/-! ## Section 6: Basic Properties -/

/-- The edge boundary of the empty set is empty -/
@[simp]
theorem edgeBoundary_empty : edgeBoundary G ∅ = ∅ := by
  unfold edgeBoundary
  simp only [Finset.filter_eq_empty_iff]
  intro e _he
  unfold edgeHasOneEndpointIn
  push_neg
  intro v w _
  constructor
  · intro hv_in
    exact absurd hv_in (Finset.notMem_empty v)
  · intro _hv_nin
    simp only [Finset.notMem_empty, not_false_eq_true]

/-- The edge boundary of the full set is empty -/
@[simp]
theorem edgeBoundary_univ : edgeBoundary G (Finset.univ : Finset V) = ∅ := by
  unfold edgeBoundary
  simp only [Finset.filter_eq_empty_iff]
  intro e _he
  unfold edgeHasOneEndpointIn
  push_neg
  intro v w _
  constructor
  · intro _
    simp only [Finset.mem_univ]
  · intro hv_nin
    exact absurd (Finset.mem_univ v) hv_nin

/-- Edge boundary cardinality is non-negative (trivially true for ℕ) -/
theorem edgeBoundaryCard_nonneg (S : Finset V) : 0 ≤ edgeBoundaryCard G S := Nat.zero_le _

/-- The Cheeger constant is non-negative -/
theorem cheegerConstant_nonneg : 0 ≤ cheegerConstant G := by
  unfold cheegerConstant
  split_ifs with h
  · apply Finset.le_inf'
    intro S _hS
    split_ifs with hS'
    · unfold expansionRatio
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    · rfl
  · rfl

/-! ## Section 7: Expansion Ratio Properties -/

/-- For any valid S, the edge boundary size is at least cheegerConstant * |S| -/
theorem edgeBoundary_ge_cheeger_mul_card (S : Finset V) (hvalid : isValidCheegerSubset S) :
    (edgeBoundaryCard G S : ℚ) ≥ cheegerConstant G * S.card := by
  unfold cheegerConstant
  have hS_ne : S.Nonempty := hvalid.1
  have hS_mem : S ∈ validCheegerSubsets (V := V) := by
    unfold validCheegerSubsets
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvalid
  have h_ne : (validCheegerSubsets (V := V)).Nonempty := ⟨S, hS_mem⟩
  simp only [h_ne, ↓reduceDIte]
  have hcard_pos : (0 : ℚ) < S.card := by
    rw [Nat.cast_pos]
    exact Finset.card_pos.mpr hS_ne
  -- The inf' is at most expansionRatio G S hS_ne
  have h_inf_le : (validCheegerSubsets (V := V)).inf' h_ne (fun T =>
      if hT : T.Nonempty then expansionRatio G T hT else 0) ≤ expansionRatio G S hS_ne := by
    have := Finset.inf'_le (fun T => if hT : T.Nonempty then expansionRatio G T hT else 0)
        (h := hS_mem)
    simp only [hS_ne, ↓reduceDIte] at this
    exact this
  unfold expansionRatio at h_inf_le ⊢
  calc (validCheegerSubsets (V := V)).inf' h_ne (fun T =>
        if hT : T.Nonempty then expansionRatio G T hT else 0) * S.card
    ≤ (edgeBoundaryCard G S : ℚ) / S.card * S.card := by
        apply mul_le_mul_of_nonneg_right h_inf_le
        exact le_of_lt hcard_pos
    _ = (edgeBoundaryCard G S : ℚ) := by
        rw [div_mul_cancel₀]
        exact ne_of_gt hcard_pos

/-! ## Section 8: Singleton Edge Boundary -/

/-- For a single vertex v, the edge boundary of {v} equals the incidence set -/
theorem edgeBoundary_singleton_eq_incidence (v : V) :
    edgeBoundary G {v} = G.incidenceFinset v := by
  unfold edgeBoundary
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_incidenceFinset]
  constructor
  · intro ⟨he_edge, h_one⟩
    unfold edgeHasOneEndpointIn at h_one
    obtain ⟨a, b, hab, h_or⟩ := h_one
    constructor
    · rw [SimpleGraph.mem_edgeFinset] at he_edge
      exact he_edge
    · rcases h_or with ⟨ha_in, _hb_nin⟩ | ⟨_ha_nin, hb_in⟩
      · simp only [Finset.mem_singleton] at ha_in
        rw [hab, ha_in]
        exact Sym2.mem_mk_left v b
      · simp only [Finset.mem_singleton] at hb_in
        rw [hab, hb_in]
        exact Sym2.mem_mk_right a v
  · intro ⟨he_edge, hv_in⟩
    refine ⟨SimpleGraph.mem_edgeFinset.mpr he_edge, ?_⟩
    unfold edgeHasOneEndpointIn
    -- e contains v, use Sym2.ind to get the representation
    revert hv_in he_edge
    refine Sym2.ind (fun a b => ?_) e
    intro he_edge hv_in
    simp only [Sym2.mem_iff] at hv_in
    -- Convert edgeSet membership to Adj
    rw [SimpleGraph.mem_edgeSet] at he_edge
    rcases hv_in with rfl | rfl
    · -- v = a, so he_edge : G.Adj v b
      use v, b, rfl
      left
      constructor
      · simp only [Finset.mem_singleton]
      · simp only [Finset.mem_singleton]
        -- Need: b ≠ v, have: G.Adj v b
        exact fun h => G.ne_of_adj he_edge h.symm
    · -- v = b, so he_edge : G.Adj a v
      use a, v, rfl
      right
      constructor
      · simp only [Finset.mem_singleton]
        -- Need: ¬(a = v), have: G.Adj a v
        exact G.ne_of_adj he_edge
      · simp only [Finset.mem_singleton]

/-- The edge boundary size of {v} equals the degree of v -/
theorem edgeBoundaryCard_singleton (v : V) :
    edgeBoundaryCard G {v} = G.degree v := by
  unfold edgeBoundaryCard
  rw [edgeBoundary_singleton_eq_incidence]
  exact G.card_incidenceFinset_eq_degree v

/-- Upper bound: the Cheeger constant is at most the minimum degree -/
theorem cheegerConstant_le_minDegree (hV : 2 ≤ Fintype.card V) :
    cheegerConstant G ≤ G.minDegree := by
  unfold cheegerConstant
  have h_card_pos : 0 < Fintype.card V := by omega
  have hne : Nonempty V := Fintype.card_pos_iff.mp h_card_pos
  -- Get a vertex that achieves the minimum degree
  obtain ⟨v, hv_min⟩ := G.exists_minimal_degree_vertex
  have h_singleton_valid : isValidCheegerSubset ({v} : Finset V) := by
    unfold isValidCheegerSubset
    constructor
    · exact Finset.singleton_nonempty v
    · simp only [Finset.card_singleton]
      omega
  have h_singleton_mem : {v} ∈ validCheegerSubsets (V := V) := by
    unfold validCheegerSubsets
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_singleton_valid
  have h_ne : (validCheegerSubsets (V := V)).Nonempty := ⟨{v}, h_singleton_mem⟩
  simp only [h_ne, ↓reduceDIte]
  have h_inf_le : (validCheegerSubsets (V := V)).inf' h_ne (fun T =>
      if hT : T.Nonempty then expansionRatio G T hT else 0) ≤
      expansionRatio G {v} (Finset.singleton_nonempty v) := by
    have := Finset.inf'_le (fun T => if hT : T.Nonempty then expansionRatio G T hT else 0)
        (h := h_singleton_mem)
    simp only [Finset.singleton_nonempty, ↓reduceDIte] at this
    exact this
  calc (validCheegerSubsets (V := V)).inf' h_ne (fun T =>
        if hT : T.Nonempty then expansionRatio G T hT else 0)
    ≤ expansionRatio G {v} (Finset.singleton_nonempty v) := h_inf_le
    _ = (edgeBoundaryCard G {v} : ℚ) / 1 := by
        unfold expansionRatio
        simp only [Finset.card_singleton, Nat.cast_one]
    _ = G.degree v := by
        rw [div_one, edgeBoundaryCard_singleton]
    _ = G.minDegree := by
        rw [hv_min]

/-! ## Section 9: Helper Lemmas -/

omit [DecidableEq V] in
/-- The valid Cheeger subsets are exactly the nonempty subsets with |S| ≤ |V|/2 -/
@[simp]
theorem mem_validCheegerSubsets (S : Finset V) :
    S ∈ validCheegerSubsets (V := V) ↔ isValidCheegerSubset S := by
  unfold validCheegerSubsets
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The expansion ratio is positive if the edge boundary is nonempty -/
theorem expansionRatio_pos {S : Finset V} (hS : S.Nonempty)
    (hB : (edgeBoundary G S).Nonempty) :
    0 < expansionRatio G S hS := by
  unfold expansionRatio edgeBoundaryCard
  apply div_pos
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hS)

/-- An expander graph has positive Cheeger constant -/
theorem isExpanderGraph_pos (h : isExpanderGraph G) : 0 < cheegerConstant G := by
  unfold isExpanderGraph at h
  obtain ⟨c, hc_pos, hc_le⟩ := h
  exact lt_of_lt_of_le hc_pos hc_le

/-- If the graph is a (c, n)-expander with c > 0, then it is an expander graph -/
theorem isExpander_to_isExpanderGraph {c : ℚ} {n : ℕ} (hc : c > 0) (h : isExpander G c n) :
    isExpanderGraph G := by
  unfold isExpanderGraph
  exact ⟨c, hc, h.2⟩

/-- The edge boundary is symmetric: δ(S) = δ(Sᶜ) -/
theorem edgeBoundary_compl (S : Finset V) :
    edgeBoundary G S = edgeBoundary G Sᶜ := by
  unfold edgeBoundary
  congr 1
  ext e
  unfold edgeHasOneEndpointIn
  constructor
  · intro ⟨v, w, hvw, h_or⟩
    use v, w, hvw
    rcases h_or with ⟨hv_in, hw_nin⟩ | ⟨hv_nin, hw_in⟩
    · right
      simp only [Finset.mem_compl, hv_in, not_true_eq_false, hw_nin, not_false_eq_true, and_self]
    · left
      simp only [Finset.mem_compl, hv_nin, not_false_eq_true, hw_in, not_true_eq_false, and_self]
  · intro ⟨v, w, hvw, h_or⟩
    use v, w, hvw
    rcases h_or with ⟨hv_in, hw_nin⟩ | ⟨hv_nin, hw_in⟩
    · simp only [Finset.mem_compl] at hv_in hw_nin
      push_neg at hw_nin
      right
      exact ⟨hv_in, hw_nin⟩
    · simp only [Finset.mem_compl] at hv_nin hw_in
      push_neg at hv_nin
      left
      exact ⟨hv_nin, hw_in⟩

end QEC
