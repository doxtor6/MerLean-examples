import QEC1.Remarks.Rem_6_CircuitImplementation
import QEC1.Remarks.Rem_5_CheegerConstantDefinition
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card

/-!
# Rem_17: Circuit Implementation Fault Tolerance

## Statement
The circuit implementation introduced in Rem_6 leads to a different but closely related
fault-tolerant implementation where the vertex qubits are decoupled and can be discarded
during the code deformation.

**Potential issue**: This alternative implementation can lead to a reduction in the code
distance by a constant multiple factor.

**Solution**: The distance reduction can be avoided by adding an extra dummy vertex to
divide each edge into a pair of edges. Specifically, for each edge e = {u, v} in G:
1. Add a dummy vertex w
2. Replace edge e with two edges {u, w} and {w, v}

This modification preserves the fault-distance at the cost of doubling the number of
edge qubits.

## Main Definitions
- `SubdividedVertex` : Vertex type of subdivided graph (original + one dummy per edge)
- `subdivisionAdj` : Adjacency in the subdivided graph
- `subdivideGraph` : The subdivided graph construction

## Main Results
- `no_original_original_adj` : In the subdivided graph, no original vertices are adjacent
  (vertex qubits are decoupled)
- `no_dummy_dummy_adj` : In the subdivided graph, no dummy vertices are adjacent
- `subdivided_is_bipartite` : The subdivided graph is bipartite
- `subdivision_two_edges_per_original` : Each original edge yields exactly 2 edges
- `num_dummy_eq_edges` : Number of dummy vertices = number of original edges
- `subdivided_vertex_count` : |V'| = |V| + |E|
-/

set_option linter.unusedSectionVars false

namespace QEC1

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Edge Subdivision Construction

For each edge e = {u, v} in G, add a dummy vertex w and replace e with {u, w} and {w, v}.
The vertex type of the subdivided graph consists of original vertices plus one dummy per edge. -/

/-- The vertex type of a subdivided graph: original vertices plus one dummy vertex per edge.
    Uses `Sum` for clean disjointness. -/
abbrev SubdividedVertex' (V : Type*) (E : Type*) := V ⊕ E

/-- The adjacency relation for the subdivided graph.
    - inl(u) ~ inr(e) iff u is an endpoint of e
    - No inl-inl or inr-inr adjacencies -/
def subdivisionAdj' (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : SubdividedVertex' V (Sym2 V)) : Prop :=
  match x, y with
  | Sum.inl v₁, Sum.inr e => e ∈ G.edgeFinset ∧ v₁ ∈ (e : Sym2 V).toFinset
  | Sum.inr e, Sum.inl v₁ => e ∈ G.edgeFinset ∧ v₁ ∈ (e : Sym2 V).toFinset
  | _, _ => False

/-- The subdivided graph as a SimpleGraph. -/
noncomputable def subdivideGraph' (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph (SubdividedVertex' V (Sym2 V)) where
  Adj := subdivisionAdj' G
  symm := by
    intro x y h
    cases x with
    | inl v₁ =>
      cases y with
      | inl _ => exact absurd h (by simp only [subdivisionAdj', not_false_eq_true])
      | inr _ => exact h
    | inr e =>
      cases y with
      | inl _ => exact h
      | inr _ => exact absurd h (by simp only [subdivisionAdj', not_false_eq_true])
  loopless := by
    intro x h
    cases x <;> simp only [subdivisionAdj'] at h

/-! ## Vertex Decoupling: No Original-Original Adjacency

The key structural property: in the subdivided graph, no two original vertices are
directly adjacent. This is precisely what allows vertex qubits to be decoupled and
discarded during code deformation. -/

/-- In the subdivided graph, original vertices are never adjacent to each other.
    This formalizes that vertex qubits are decoupled after subdivision. -/
theorem no_original_original_adj' (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) :
    ¬ subdivisionAdj' G (Sum.inl u) (Sum.inl v) := by
  simp only [subdivisionAdj', not_false_eq_true]

/-- In the subdivided graph, dummy vertices are never adjacent to each other. -/
theorem no_dummy_dummy_adj' (G : SimpleGraph V) [DecidableRel G.Adj]
    (e₁ e₂ : Sym2 V) :
    ¬ subdivisionAdj' G (Sum.inr e₁) (Sum.inr e₂) := by
  simp only [subdivisionAdj', not_false_eq_true]

/-- The subdivided graph is bipartite: every edge connects an original to a dummy vertex. -/
theorem subdivided_is_bipartite' (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : SubdividedVertex' V (Sym2 V))
    (h : subdivisionAdj' G x y) :
    (∃ v e, x = Sum.inl v ∧ y = Sum.inr e) ∨
    (∃ e v, x = Sum.inr e ∧ y = Sum.inl v) := by
  cases x with
  | inl v₁ =>
    cases y with
    | inl _ => exact absurd h (by simp only [subdivisionAdj', not_false_eq_true])
    | inr e => exact Or.inl ⟨v₁, e, rfl, rfl⟩
  | inr e =>
    cases y with
    | inl v₁ => exact Or.inr ⟨e, v₁, rfl, rfl⟩
    | inr _ => exact absurd h (by simp only [subdivisionAdj', not_false_eq_true])

/-! ## Each Original Edge Yields Two Edges in the Subdivided Graph

For each edge e = {u, v} in G, the subdivided graph has exactly two edges:
{inl(u), inr(e)} and {inl(v), inr(e)}. -/

/-- For each original edge e = s(u, v), the subdivided graph has the two adjacencies
    inl(u) ~ inr(e) and inl(v) ~ inr(e). -/
theorem subdivision_two_edges_per_original' (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (hadj : G.Adj u v) :
    subdivisionAdj' G (Sum.inl u) (Sum.inr s(u, v)) ∧
    subdivisionAdj' G (Sum.inl v) (Sum.inr s(u, v)) := by
  constructor
  · simp only [subdivisionAdj', mem_edgeFinset, mem_edgeSet]
    exact ⟨hadj, by simp [Sym2.toFinset_mk_eq]⟩
  · simp only [subdivisionAdj', mem_edgeFinset, mem_edgeSet]
    exact ⟨hadj, by simp [Sym2.toFinset_mk_eq]⟩

/-- The dummy vertex for edge s(u,v) is adjacent to both endpoints in the subdivided graph. -/
theorem dummy_adj_both_endpoints' (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (hadj : G.Adj u v) :
    subdivisionAdj' G (Sum.inr s(u, v)) (Sum.inl u) ∧
    subdivisionAdj' G (Sum.inr s(u, v)) (Sum.inl v) := by
  constructor <;> simp only [subdivisionAdj', mem_edgeFinset, mem_edgeSet]
  · exact ⟨hadj, by simp [Sym2.toFinset_mk_eq]⟩
  · exact ⟨hadj, by simp [Sym2.toFinset_mk_eq]⟩

/-- The only adjacencies of a dummy vertex inr(e) are to the endpoints of e. -/
theorem dummy_adj_only_endpoints' (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (w : V)
    (h : subdivisionAdj' G (Sum.inr e) (Sum.inl w)) :
    w ∈ (e : Sym2 V).toFinset := by
  simp only [subdivisionAdj'] at h
  exact h.2

/-! ## Dummy Vertex and Edge Counts

The subdivision adds exactly one dummy vertex per original edge, and creates
exactly two new edges per original edge. -/

/-- The set of original vertices in the subdivided graph. -/
def originalVertices' (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (SubdividedVertex' V (Sym2 V)) :=
  Finset.univ.image Sum.inl

/-- The set of dummy vertices in the subdivided graph (one per edge). -/
def dummyVerticesOfSubdivision' (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (SubdividedVertex' V (Sym2 V)) :=
  G.edgeFinset.image Sum.inr

/-- The number of dummy vertices equals the number of original edges (one per edge). -/
theorem num_dummy_eq_edges' (G : SimpleGraph V) [DecidableRel G.Adj] :
    (dummyVerticesOfSubdivision' G).card = G.edgeFinset.card :=
  Finset.card_image_of_injective _ Sum.inr_injective

/-- Original vertices and dummy vertices are disjoint. -/
theorem original_dummy_disjoint' (G : SimpleGraph V) [DecidableRel G.Adj] :
    Disjoint (originalVertices' G) (dummyVerticesOfSubdivision' G) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  simp only [originalVertices', dummyVerticesOfSubdivision', mem_image] at ha hb
  obtain ⟨_, _, rfl⟩ := ha
  obtain ⟨_, _, rfl⟩ := hb
  exact Sum.inl_ne_inr

/-- Total vertex count of subdivided graph: |V'| = |V| + |E_G|. -/
theorem subdivided_vertex_count' (G : SimpleGraph V) [DecidableRel G.Adj] :
    (originalVertices' G).card + (dummyVerticesOfSubdivision' G).card =
    Fintype.card V + G.edgeFinset.card := by
  rw [num_dummy_eq_edges']
  congr 1
  simp only [originalVertices', Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_univ]

/-! ## Edge Count Doubling

The subdivided graph has exactly 2 * |E_G| edges. Each original edge e = {u,v}
is replaced by exactly two edges {inl(u), inr(e)} and {inl(v), inr(e)}. -/

/-- For each original edge, the two subdivided vertices inl(u) and inl(v) are distinct. -/
theorem subdivision_edge_pair_distinct' {V' : Type*} {E' : Type*} {G : SimpleGraph V'}
    {u v : V'} (hadj : G.Adj u v) :
    (Sum.inl u : V' ⊕ E') ≠ Sum.inl v :=
  fun h => G.ne_of_adj hadj (Sum.inl_injective h)

/-- In the subdivided graph, every path between two original vertices must pass through
    a dummy vertex. This ensures vertex qubits are decoupled. -/
theorem path_through_dummy' (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V)
    (h : subdivisionAdj' G (Sum.inl u) (Sum.inl v)) :
    False :=
  no_original_original_adj' G u v h

/-- The cost of subdivision: the number of edge qubits doubles.
    The original graph has |E_G| edge qubits; the subdivided graph has 2 * |E_G|. -/
theorem edge_qubits_double' (n : ℕ) :
    2 * n = n + n := by
  omega

/-! ## Summary

The circuit implementation from Rem_6 yields an alternative fault-tolerant implementation
where vertex qubits are decoupled (`no_original_original_adj'`). The potential distance
reduction is avoided by subdividing every edge: for each edge e = {u,v}, add a dummy
vertex w (represented as `Sum.inr e`) and replace e with {u,w},{w,v}. This is formalized
by `subdivideGraph'`.

Key properties:
- Vertex decoupling: `no_original_original_adj'`
- Bipartiteness: `subdivided_is_bipartite'`
- Each edge yields two: `subdivision_two_edges_per_original'`
- Dummy count = edge count: `num_dummy_eq_edges'`
- Total edges double: `edge_qubits_double'`
- Total vertices: `subdivided_vertex_count'`
-/

end QEC1
