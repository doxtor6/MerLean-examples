import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic

/-!
# Notation: Cheeger Constant

## Statement
For a finite simple graph G = (V, E), the Cheeger constant (also called isoperimetric number
or edge expansion) is defined as
  h(G) = min_{S ⊆ V, 0 < |S| ≤ |V|/2} |∂S| / |S|,
where ∂S = {e = {u,v} ∈ E : u ∈ S, v ∉ S} is the edge boundary of S. A graph with h(G) ≥ c
for some constant c > 0 is called an expander graph.

## Main Results
- `QEC1.SimpleGraph.edgeBoundary`: edge boundary of a vertex subset
- `QEC1.cheegerValidSubsets'`: collection of Cheeger-valid subsets
- `QEC1.cheegerConstant`: the Cheeger constant h(G)
- `QEC1.SimpleGraph.IsExpander`: expander graph property

## Corollaries
- `QEC1.SimpleGraph.edgeBoundary_empty`: ∂∅ = ∅
- `QEC1.SimpleGraph.edgeBoundary_univ`: ∂V = ∅
- `QEC1.SimpleGraph.edgeBoundary_compl`: ∂S = ∂Sᶜ
- `QEC1.SimpleGraph.cheegerConstant_nonneg`: h(G) ≥ 0
- `QEC1.SimpleGraph.edgeBoundary_card_ge_of_cheeger`: c ≤ h(G) → c·|S| ≤ |∂S|
- `QEC1.SimpleGraph.isExpander_iff`: characterization of expander graphs
-/

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace QEC1

/-! ## Edge Boundary -/

/-- The edge boundary of a vertex subset S in a simple graph G is the set of edges
with exactly one endpoint in S. Formally, it is the subfinset of G.edgeFinset
consisting of edges e such that |e.toFinset ∩ S| = 1. -/
noncomputable def SimpleGraph.edgeBoundary (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => (e.toFinset ∩ S).card = 1)

@[simp]
theorem SimpleGraph.mem_edgeBoundary_iff (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (e : Sym2 V) :
    e ∈ SimpleGraph.edgeBoundary G S ↔ e ∈ G.edgeFinset ∧ (e.toFinset ∩ S).card = 1 := by
  simp [SimpleGraph.edgeBoundary]

@[simp]
theorem SimpleGraph.edgeBoundary_empty (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph.edgeBoundary G ∅ = ∅ := by
  ext e
  simp [SimpleGraph.edgeBoundary]

private lemma inter_compl_card_partition (A S : Finset V) :
    (A ∩ S).card + (A ∩ Sᶜ).card = A.card := by
  rw [← Finset.sdiff_eq_inter_compl]
  exact Finset.card_inter_add_card_sdiff A S

@[simp]
theorem SimpleGraph.edgeBoundary_univ (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph.edgeBoundary G Finset.univ = ∅ := by
  ext e
  constructor
  · intro he
    rw [SimpleGraph.mem_edgeBoundary_iff] at he
    obtain ⟨he_mem, hcard⟩ := he
    have h_edge_card : e.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag e
        (G.not_isDiag_of_mem_edgeSet (by rwa [_root_.SimpleGraph.mem_edgeFinset] at he_mem))
    have h_inter : e.toFinset ∩ Finset.univ = e.toFinset := by simp
    rw [h_inter] at hcard
    omega
  · intro he
    exact absurd he (Finset.notMem_empty _)

theorem SimpleGraph.edgeBoundary_compl (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    SimpleGraph.edgeBoundary G S = SimpleGraph.edgeBoundary G Sᶜ := by
  ext e
  simp only [SimpleGraph.mem_edgeBoundary_iff]
  constructor
  · rintro ⟨he, hcard⟩
    refine ⟨he, ?_⟩
    have h_edge_card : e.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag e
        (G.not_isDiag_of_mem_edgeSet (by rwa [_root_.SimpleGraph.mem_edgeFinset] at he))
    have h_partition := inter_compl_card_partition e.toFinset S
    rw [h_edge_card, hcard] at h_partition
    omega
  · rintro ⟨he, hcard⟩
    refine ⟨he, ?_⟩
    have h_edge_card : e.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag e
        (G.not_isDiag_of_mem_edgeSet (by rwa [_root_.SimpleGraph.mem_edgeFinset] at he))
    have h_partition := inter_compl_card_partition e.toFinset S
    have h_partition2 := inter_compl_card_partition e.toFinset Sᶜ
    simp only [compl_compl] at h_partition2
    rw [h_edge_card, hcard] at h_partition2
    omega

/-! ## Cheeger Valid Subsets -/

/-- The set of Cheeger-valid subsets: nonempty subsets S ⊆ V with 2|S| ≤ |V|. -/
noncomputable def cheegerValidSubsets' (V : Type*) [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  Finset.univ.filter (fun S => S.Nonempty ∧ 2 * S.card ≤ Fintype.card V)

/-! ## Cheeger Constant -/

/-- The Cheeger constant h(G) of a finite simple graph G, defined as
  h(G) = inf_{S valid} |∂S| / |S|,
where the infimum is over all nonempty subsets S with 2|S| ≤ |V|.
Returns 0 if no valid subsets exist (i.e., when |V| ≤ 1). -/
noncomputable def cheegerConstant (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if h : (cheegerValidSubsets' V).Nonempty then
    (cheegerValidSubsets' V).inf' h
      (fun S => (SimpleGraph.edgeBoundary G S).card / (S.card : ℝ))
  else 0

/-! ## Expander Graph -/

/-- A graph G is a c-expander if 0 < c and c ≤ h(G). -/
def SimpleGraph.IsExpander (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  0 < c ∧ c ≤ cheegerConstant G

/-! ## Auxiliary Lemmas -/

theorem SimpleGraph.cheegerValidSubsets'_nonempty_of_card_ge_two
    (hcard : 2 ≤ Fintype.card V) :
    (cheegerValidSubsets' V).Nonempty := by
  rw [cheegerValidSubsets', Finset.filter_nonempty_iff]
  have hV : 0 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV
  exact ⟨{v}, Finset.mem_univ _, Finset.singleton_nonempty v, by simp; omega⟩

/-! ## Cheeger Constant Properties -/

theorem SimpleGraph.cheegerConstant_nonneg (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ cheegerConstant G := by
  unfold cheegerConstant
  split
  · rename_i h
    apply Finset.le_inf' h
    intro S _hS
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  · exact le_refl _

/-! ## Edge Boundary Lower Bound -/

theorem SimpleGraph.edgeBoundary_card_ge_of_cheeger (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj]
    (c : ℝ) (hc : c ≤ cheegerConstant G) (S : Finset V)
    (hne : S.Nonempty) (hsize : 2 * S.card ≤ Fintype.card V) :
    c * S.card ≤ (SimpleGraph.edgeBoundary G S).card := by
  have hvalid : S ∈ cheegerValidSubsets' V := by
    simp [cheegerValidSubsets', hne, hsize]
  have hnonempty : (cheegerValidSubsets' V).Nonempty := ⟨S, hvalid⟩
  have hcheeger : cheegerConstant G = (cheegerValidSubsets' V).inf' hnonempty
      (fun S => (SimpleGraph.edgeBoundary G S).card / (S.card : ℝ)) := by
    unfold cheegerConstant
    simp [hnonempty]
  have hS_pos : (0 : ℝ) < S.card :=
    Nat.cast_pos.mpr (Finset.Nonempty.card_pos hne)
  have hinf_le : cheegerConstant G ≤
      (SimpleGraph.edgeBoundary G S).card / (S.card : ℝ) := by
    rw [hcheeger]
    exact Finset.inf'_le _ hvalid
  calc c * S.card ≤ cheegerConstant G * S.card :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ ≤ ((SimpleGraph.edgeBoundary G S).card / (S.card : ℝ)) * S.card :=
        mul_le_mul_of_nonneg_right hinf_le (Nat.cast_nonneg _)
      _ = (SimpleGraph.edgeBoundary G S).card := by
        rw [div_mul_cancel₀]
        exact ne_of_gt hS_pos

/-! ## Expander Characterization -/

theorem SimpleGraph.isExpander_iff (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (c : ℝ) (hcard : 2 ≤ Fintype.card V) :
    SimpleGraph.IsExpander G c ↔
      0 < c ∧ ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        c * S.card ≤ (SimpleGraph.edgeBoundary G S).card := by
  constructor
  · rintro ⟨hc_pos, hc_le⟩
    exact ⟨hc_pos, fun S hne hsize =>
      SimpleGraph.edgeBoundary_card_ge_of_cheeger G c hc_le S hne hsize⟩
  · rintro ⟨hc_pos, hbound⟩
    refine ⟨hc_pos, ?_⟩
    have hnonempty := SimpleGraph.cheegerValidSubsets'_nonempty_of_card_ge_two hcard
    unfold cheegerConstant
    simp only [hnonempty, ↓reduceDIte]
    apply Finset.le_inf'
    intro S hS
    simp only [cheegerValidSubsets', Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨hne, hsize⟩ := hS
    have hS_pos : (0 : ℝ) < S.card :=
      Nat.cast_pos.mpr (Finset.Nonempty.card_pos hne)
    rw [le_div_iff₀ hS_pos]
    exact hbound S hne hsize

end QEC1
