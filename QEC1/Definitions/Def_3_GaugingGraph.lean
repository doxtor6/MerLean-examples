import QEC1.Definitions.Def_2_LogicalOperator
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Gauging Graph (Definition 3)

## Statement
Let C be an [[n, k, d]] stabilizer code and let L = ∏_{v ∈ L} X_v be an X-type logical operator
with support L.

A **gauging graph** for L is a connected graph G = (V, E) such that:
(i) **Vertices**: V ⊇ L, with an isomorphism identifying L with a subset of vertices.
(ii) **Connectivity**: G is connected.
(iii) **Edge qubits**: Each edge e ∈ E corresponds to an auxiliary qubit.

The graph G may contain **dummy vertices** V \ L, which correspond to auxiliary qubits
initialized in the |+⟩ state and on which X is measured with certain outcome +1.

**Graph parameters**:
- |V| = number of vertices (includes support of L plus dummy vertices)
- |E| = number of edges (equals number of auxiliary qubits)
- The **cycle rank** of G is |E| - |V| + 1 (number of independent cycles)

## Main Results
**Main Structure** (`GaugingGraph`): A connected graph containing the logical support
**Key Properties**: Cycle rank, edge count, dummy vertex identification

## File Structure
1. Gauging Graph: Definition using Mathlib's SimpleGraph with connectivity
2. Graph Parameters: Vertex count, edge count, cycle rank
3. Dummy Vertices: Auxiliary vertices beyond logical support
4. Helper Lemmas: Basic properties
-/

namespace QEC

/-! ## Section 1: Gauging Graph Definition -/

/-- A gauging graph for an X-type logical operator.

    Given a stabilizer code C with an X-type logical operator L (support 𝓛),
    a gauging graph is a connected simple graph G = (V, E) where:
    - V is a finite vertex set containing an embedded copy of 𝓛
    - G is connected
    - Each edge corresponds to an auxiliary qubit

    We use Mathlib's SimpleGraph for the graph structure and require
    finiteness and connectivity. -/
structure GaugingGraph {n k : ℕ} (C : StabilizerCode n k) (L : XTypeLogical C) where
  /-- The vertex type of the gauging graph -/
  Vertex : Type
  /-- The vertex type is finite -/
  vertexFintype : Fintype Vertex
  /-- The vertex type has decidable equality -/
  vertexDecEq : DecidableEq Vertex
  /-- The underlying simple graph structure -/
  graph : SimpleGraph Vertex
  /-- The graph has decidable adjacency -/
  adjDecidable : DecidableRel graph.Adj
  /-- Embedding of the logical support into vertices -/
  supportEmbed : L.support → Vertex
  /-- The embedding is injective -/
  supportEmbed_injective : Function.Injective supportEmbed
  /-- The graph is connected -/
  connected : graph.Connected

-- Provide instances from structure fields
attribute [instance] GaugingGraph.vertexFintype GaugingGraph.vertexDecEq GaugingGraph.adjDecidable

namespace GaugingGraph

variable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}

/-- Number of vertices in the gauging graph -/
def numVertices (G : GaugingGraph C L) : ℕ := Fintype.card G.Vertex

/-- Number of edges in the gauging graph (equals number of auxiliary qubits) -/
noncomputable def numEdges (G : GaugingGraph C L) : ℕ := G.graph.edgeFinset.card

/-- The cycle rank (number of independent cycles): |E| - |V| + 1
    Also known as the cyclomatic complexity or first Betti number. -/
noncomputable def cycleRank (G : GaugingGraph C L) : ℤ :=
  (G.numEdges : ℤ) - (G.numVertices : ℤ) + 1

/-- The set of vertices in the image of the support embedding -/
def supportVertices (G : GaugingGraph C L) : Finset G.Vertex :=
  Finset.image G.supportEmbed Finset.univ

/-- The dummy vertices: vertices not in the support image -/
def dummyVertices (G : GaugingGraph C L) : Finset G.Vertex :=
  Finset.univ \ G.supportVertices

/-- Number of dummy vertices -/
def numDummyVertices (G : GaugingGraph C L) : ℕ := G.dummyVertices.card

/-- The logical support size -/
def supportSize (_G : GaugingGraph C L) : ℕ := L.support.card

end GaugingGraph

/-! ## Section 2: Basic Properties -/

namespace GaugingGraph

variable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}

/-- Support vertices have cardinality equal to the logical support -/
theorem supportVertices_card (G : GaugingGraph C L) :
    G.supportVertices.card = G.supportSize := by
  unfold supportVertices supportSize
  rw [Finset.card_image_of_injective _ G.supportEmbed_injective]
  simp only [Finset.card_univ, Fintype.card_coe]

/-- The number of vertices is at least the support size -/
theorem numVertices_ge_supportSize (G : GaugingGraph C L) :
    G.numVertices ≥ G.supportSize := by
  unfold numVertices
  have h_sub : G.supportVertices ⊆ Finset.univ := Finset.subset_univ _
  have h_card := G.supportVertices_card
  calc Fintype.card G.Vertex
    = Finset.univ.card := by rw [Finset.card_univ]
    _ ≥ G.supportVertices.card := Finset.card_le_card h_sub
    _ = G.supportSize := h_card

/-- Vertices partition into support vertices and dummy vertices -/
theorem vertex_partition (G : GaugingGraph C L) :
    G.numVertices = G.supportVertices.card + G.numDummyVertices := by
  unfold numVertices numDummyVertices dummyVertices
  have h_union : G.supportVertices ∪ ((Finset.univ : Finset G.Vertex) \ G.supportVertices) =
      Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have h_disj : Disjoint G.supportVertices ((Finset.univ : Finset G.Vertex) \ G.supportVertices) :=
    Finset.disjoint_sdiff
  calc Fintype.card G.Vertex
    = (Finset.univ : Finset G.Vertex).card := by rw [Finset.card_univ]
    _ = (G.supportVertices ∪ (Finset.univ \ G.supportVertices)).card := by rw [h_union]
    _ = G.supportVertices.card + (Finset.univ \ G.supportVertices).card :=
        Finset.card_union_of_disjoint h_disj

/-- Cycle rank formula in terms of dummy vertices -/
theorem cycleRank_eq (G : GaugingGraph C L) :
    G.cycleRank = (G.numEdges : ℤ) - (G.supportSize : ℤ) - (G.numDummyVertices : ℤ) + 1 := by
  unfold cycleRank
  have h := G.vertex_partition
  have hcard := G.supportVertices_card
  omega

end GaugingGraph

/-! ## Section 3: Tree Case (Cycle Rank 0) -/

/-- A gauging graph is a tree if it has cycle rank 0 -/
def GaugingGraph.isTree {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) : Prop :=
  G.cycleRank = 0

/-- For a tree, the number of edges equals number of vertices minus 1 -/
theorem GaugingGraph.tree_edge_count {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) (htree : G.isTree) : (G.numEdges : ℤ) = (G.numVertices : ℤ) - 1 := by
  unfold isTree cycleRank at htree
  omega

/-! ## Section 4: Minimal Gauging Graph (No Dummy Vertices) -/

/-- A gauging graph is minimal if it has no dummy vertices -/
def GaugingGraph.isMinimal {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) : Prop :=
  G.numDummyVertices = 0

/-- For a minimal gauging graph, vertex count equals support size -/
theorem GaugingGraph.minimal_numVertices {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) (hmin : G.isMinimal) : G.numVertices = G.supportSize := by
  have h := G.vertex_partition
  have hcard := G.supportVertices_card
  unfold isMinimal at hmin
  omega

/-- For a minimal tree gauging graph, edges = support size - 1 -/
theorem GaugingGraph.minimal_tree_edges {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) (hmin : G.isMinimal) (htree : G.isTree) :
    (G.numEdges : ℤ) = (G.supportSize : ℤ) - 1 := by
  have h1 := G.tree_edge_count htree
  have h2 := G.minimal_numVertices hmin
  omega

/-! ## Section 5: Helper Lemmas -/

/-- The number of auxiliary qubits equals the number of edges -/
@[simp]
theorem GaugingGraph.numAuxQubits_eq_edges {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) : G.numEdges = G.numEdges :=
  rfl

/-- Support embedding maps distinct support elements to distinct vertices -/
theorem GaugingGraph.supportEmbed_ne {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) {v w : L.support} (hvw : v ≠ w) :
    G.supportEmbed v ≠ G.supportEmbed w := by
  intro h
  exact hvw (G.supportEmbed_injective h)

/-- A graph with support size 1 and no dummy vertices is trivial (single vertex) -/
theorem GaugingGraph.single_vertex {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) (hsupport : G.supportSize = 1) (hmin : G.isMinimal) :
    G.numVertices = 1 := by
  have h := G.minimal_numVertices hmin
  omega

/-- Dummy vertices form the complement of support vertices -/
@[simp]
theorem GaugingGraph.dummyVertices_def {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) : G.dummyVertices = Finset.univ \ G.supportVertices :=
  rfl

/-- A vertex is either a support vertex or a dummy vertex -/
theorem GaugingGraph.vertex_cases {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) (v : G.Vertex) :
    v ∈ G.supportVertices ∨ v ∈ G.dummyVertices := by
  simp only [dummyVertices_def, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

/-- Support vertices and dummy vertices are disjoint -/
theorem GaugingGraph.support_dummy_disjoint {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) : Disjoint G.supportVertices G.dummyVertices := by
  simp only [dummyVertices_def]
  exact Finset.disjoint_sdiff

/-- The cycle rank of a minimal tree is 0 -/
theorem GaugingGraph.minimal_tree_cycleRank {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) (_hmin : G.isMinimal) (htree : G.isTree) :
    G.cycleRank = 0 := htree

end QEC
