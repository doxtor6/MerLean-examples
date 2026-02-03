import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Archimedean

/-!
# Cheeger Constant (Isoperimetric Number / Edge Expansion)

## Statement
For a graph $G = (V, E)$, the **Cheeger constant** (also called isoperimetric number or edge expansion)
is defined as $h(G) = \min_{S \subseteq V, 0 < |S| \leq |V|/2} \frac{|\partial S|}{|S|}$, where
$\partial S$ is the edge boundary of $S$, i.e., the set of edges with exactly one endpoint in $S$.
A graph is called an **expander** if $h(G) \geq c$ for some constant $c > 0$.
In this work, we require $h(G) \geq 1$ to ensure that the deformed code preserves the distance
of the original code.

## Main Results
- `edgeBoundary`: The edge boundary ∂S of a vertex set S
- `CheegerConstant`: The Cheeger constant h(G)
- `IsExpander`: Predicate for expander graphs (∃ c > 0, h(G) ≥ c)
- `IsStrongExpander`: Predicate for h(G) ≥ 1 (used in this work)
-/

namespace QEC1

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Edge Boundary -/

/-- Whether an edge crosses the boundary of S (exactly one endpoint in S) -/
def edgeCrossesBoundary (S : Finset V) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun u v => decide ((u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)), fun _ _ => by
    simp only [or_comm, and_comm, decide_eq_decide]⟩ e

/-- The edge boundary ∂S of a vertex set S is the set of edges with exactly one endpoint in S. -/
def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => edgeCrossesBoundary S e = true)

@[simp]
lemma mem_edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u v : V) :
    s(u, v) ∈ edgeBoundary G S ↔ G.Adj u v ∧ ((u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) := by
  simp only [edgeBoundary, mem_filter, mem_edgeFinset, mem_edgeSet, edgeCrossesBoundary,
    Sym2.lift_mk, decide_eq_true_eq]

/-! ## Cheeger Constant -/

/-- The Cheeger constant h(G) = min_{S : 0 < |S| ≤ |V|/2} |∂S|/|S|.
    Returns the infimum over all valid subsets. -/
noncomputable def CheegerConstant (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ⨅ (S : Finset V) (_ : S.Nonempty) (_ : 2 * S.card ≤ Fintype.card V),
    ((edgeBoundary G S).card : ℝ) / (S.card : ℝ)

/-! ## Expander Graphs -/

/-- A graph is an **expander** if h(G) ≥ c for some constant c > 0. -/
def IsExpander (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ c : ℝ, c > 0 ∧ CheegerConstant G ≥ c

/-- A **strong expander** has Cheeger constant at least 1: h(G) ≥ 1.
    This is the condition required in this work to preserve the distance of the original code. -/
def IsStrongExpander (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  CheegerConstant G ≥ 1

/-! ## Basic Properties -/

/-- The edge boundary of the empty set is empty -/
@[simp]
lemma edgeBoundary_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeBoundary G ∅ = ∅ := by
  simp only [edgeBoundary, edgeCrossesBoundary]
  ext e
  simp only [mem_filter, notMem_empty, iff_false, not_and]
  intro _
  induction e using Sym2.ind with
  | h u v =>
    simp only [Sym2.lift_mk, notMem_empty, false_and, and_false, or_self, decide_false,
      Bool.false_eq_true, not_false_eq_true]

/-- The edge boundary of the full vertex set is empty -/
@[simp]
lemma edgeBoundary_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeBoundary G Finset.univ = ∅ := by
  simp only [edgeBoundary, edgeCrossesBoundary]
  ext e
  simp only [mem_filter, notMem_empty, iff_false, not_and]
  intro _
  induction e using Sym2.ind with
  | h u v =>
    simp only [Sym2.lift_mk, mem_univ, not_true_eq_false, and_false, false_and, or_self,
      decide_false, Bool.false_eq_true, not_false_eq_true]

/-- The edge boundary is symmetric: ∂S = ∂(V \ S) -/
lemma edgeBoundary_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgeBoundary G S = edgeBoundary G Sᶜ := by
  ext e
  simp only [edgeBoundary, mem_filter, edgeCrossesBoundary, mem_compl]
  induction e using Sym2.ind with
  | h u v =>
    simp only [Sym2.lift_mk, mem_compl, decide_eq_true_eq]
    constructor <;> intro ⟨he, hb⟩ <;> refine ⟨he, ?_⟩
    · -- Need: (u ∉ S ∧ ¬v ∉ S) ∨ (¬u ∉ S ∧ v ∉ S) from (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)
      cases hb with
      | inl h => exact Or.inr ⟨not_not.mpr h.1, h.2⟩
      | inr h => exact Or.inl ⟨h.1, not_not.mpr h.2⟩
    · -- Need: (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S) from (u ∉ S ∧ ¬v ∉ S) ∨ (¬u ∉ S ∧ v ∉ S)
      cases hb with
      | inl h => exact Or.inr ⟨h.1, not_not.mp h.2⟩
      | inr h => exact Or.inl ⟨not_not.mp h.1, h.2⟩

/-- A strong expander is an expander (with c = 1) -/
lemma IsStrongExpander.isExpander {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsStrongExpander G) : IsExpander G :=
  ⟨1, one_pos, h⟩

/-- Cheeger constant is nonnegative -/
lemma CheegerConstant_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ CheegerConstant G := by
  apply Real.iInf_nonneg
  intro S
  apply Real.iInf_nonneg
  intro _
  apply Real.iInf_nonneg
  intro _
  apply div_nonneg <;> exact Nat.cast_nonneg _

end QEC1
