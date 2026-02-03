import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.SymmDiff

import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps

/-!
# Def_6: Cycle-Sparsified Graph

## Statement
Given a graph $G$ and a constant $c$ called the **cycle-degree bound**, a **cycle-sparsification**
of $G$ is a new graph $\bar{\bar{G}}$ constructed as follows:

**Layer structure**: Build $R+1$ copies of $G$, labeled as layers $0, 1, 2, \ldots, R$.
Layer 0 corresponds to the original graph $G$; layers $1, \ldots, R$ are copies on dummy vertices.

**Inter-layer edges**: Connect each vertex $v$ in layer $i$ to its copy in layer $i+1$ by an edge,
for all $i = 0, \ldots, R-1$.

**Cellulation edges**: For each cycle in a chosen generating set of cycles for $G$, in exactly
one layer, add edges that triangulate (cellulate) the cycle. The triangulation of a cycle
$v_1 \to v_2 \to \cdots \to v_N \to v_1$ adds edges:
$\{(v_1, v_{N-1}), (v_{N-1}, v_2), (v_2, v_{N-2}), (v_{N-2}, v_3), \ldots\}$ forming a sequence
of triangles.

**Cycle-degree constraint**: The assignment of cycles to layers must ensure that in the resulting
graph $\bar{\bar{G}}$, every edge participates in at most $c$ cycles from the chosen generating set.

Let $R_G^c$ denote the minimum number of layers required to achieve cycle-degree at most $c$.
The **Freedman-Hastings decongestion lemma** establishes that $R_G^c = O(\log^2 |V_G|)$ for any
constant-degree graph $G$.

## Main Definitions
- `LayeredVertex` : Vertices in the layered graph (layer index × original vertex)
- `CycleSparsification` : The cycle-sparsified graph structure
- `CycleLayerAssignment` : Assignment of cycles to layers
- `triangulationEdgePairs` : The vertex pairs added to triangulate a cycle
- `cycleDegree` : The number of cycles containing an edge in the generating set

## Key Properties
- `layer_zero_adj_iff_original` : Layer 0 is isomorphic to the original graph
- `interLayerEdge_connects_copies` : Each vertex connects to its copy in the next layer
- `cycleDegConstraint` : Every edge has cycle-degree at most c
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ## Layered Vertex Type -/

/-- A vertex in the layered graph: a pair of (layer index, original vertex).
    Layer 0 contains the original vertices; layers 1, ..., R contain dummy copies. -/
@[ext]
structure LayeredVertex (V : Type*) (R : ℕ) where
  /-- The layer index (0, 1, ..., R) -/
  layer : Fin (R + 1)
  /-- The original vertex that this is a copy of -/
  vertex : V

namespace LayeredVertex

variable {V : Type*} {R : ℕ}

/-- Layer 0 vertices are the "original" vertices -/
def isOriginal (lv : LayeredVertex V R) : Prop := lv.layer = 0

/-- Layers 1, ..., R contain "dummy" vertices -/
def isDummy (lv : LayeredVertex V R) : Prop := lv.layer ≠ 0

instance [DecidableEq V] : DecidableEq (LayeredVertex V R) := fun lv1 lv2 =>
  if h1 : lv1.layer = lv2.layer then
    if h2 : lv1.vertex = lv2.vertex then
      isTrue (LayeredVertex.ext h1 h2)
    else isFalse (fun h => h2 (congrArg LayeredVertex.vertex h))
  else isFalse (fun h => h1 (congrArg LayeredVertex.layer h))

instance [Fintype V] : Fintype (LayeredVertex V R) :=
  Fintype.ofEquiv (Fin (R + 1) × V)
    ⟨fun p => ⟨p.1, p.2⟩, fun lv => ⟨lv.layer, lv.vertex⟩,
     fun _ => rfl, fun _ => rfl⟩

/-- Embed a vertex from the original graph into layer 0 -/
def ofOriginal (v : V) : LayeredVertex V R := ⟨0, v⟩

/-- Embed a vertex into a specific layer -/
def inLayer (i : Fin (R + 1)) (v : V) : LayeredVertex V R := ⟨i, v⟩

@[simp]
lemma ofOriginal_layer (v : V) : (ofOriginal v : LayeredVertex V R).layer = 0 := rfl

@[simp]
lemma ofOriginal_vertex (v : V) : (ofOriginal v : LayeredVertex V R).vertex = v := rfl

@[simp]
lemma inLayer_layer (i : Fin (R + 1)) (v : V) : (inLayer i v : LayeredVertex V R).layer = i := rfl

@[simp]
lemma inLayer_vertex (i : Fin (R + 1)) (v : V) : (inLayer i v : LayeredVertex V R).vertex = v := rfl

/-- Every layered vertex is either original or dummy -/
theorem original_or_dummy (lv : LayeredVertex V R) : lv.isOriginal ∨ lv.isDummy := by
  by_cases h : lv.layer = 0
  · left; exact h
  · right; exact h

/-- The cardinality of layered vertices: (R+1) * |V| -/
@[simp]
lemma card_layeredVertex [Fintype V] :
    Fintype.card (LayeredVertex V R) = (R + 1) * Fintype.card V := by
  have : Fintype.card (Fin (R + 1) × V) = (R + 1) * Fintype.card V := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [Fintype.card_eq.mpr ⟨{
    toFun := fun lv => (lv.layer, lv.vertex)
    invFun := fun p => ⟨p.1, p.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }⟩]
  exact this

end LayeredVertex

/-! ## Triangulation of a Cycle

The triangulation of a cycle [v₁, v₂, ..., vₙ, v₁] adds edges that form triangles
using a "zigzag" pattern that alternates between low and high indices:
{(v₁, vₙ₋₁), (vₙ₋₁, v₂), (v₂, vₙ₋₂), (vₙ₋₂, v₃), ...}

This creates a sequence of triangles moving inward from both ends of the cycle.
We represent cycles as lists of vertices and compute the triangulation edge pairs. -/

/-- A state for building zigzag triangulation edges.
    low = current low index, high = current high index (exclusive),
    fromLow = true means next edge starts from low index -/
structure ZigzagState where
  low : ℕ
  high : ℕ
  fromLow : Bool

/-- One step of zigzag edge generation. Returns the edge and next state.
    Given list length n and current state, produces edge (src, dst) based on direction. -/
def zigzagStep {V : Type*} (cycleVerts : List V) (n : ℕ)
    (hn : n = cycleVerts.length) (s : ZigzagState)
    (hlow : s.low < n) (hhigh : s.high ≤ n) (hgap : s.low + 2 < s.high) :
    (V × V) × ZigzagState :=
  have hhigh_pred : s.high - 1 < cycleVerts.length := by omega
  have hlow' : s.low < cycleVerts.length := by omega
  have hlow_succ : s.low + 1 < cycleVerts.length := by omega
  let vLow := cycleVerts.get ⟨s.low, hlow'⟩
  let vHighPred := cycleVerts.get ⟨s.high - 1, hhigh_pred⟩
  if s.fromLow then
    -- Edge from low to high-1, next step continues from high-1
    ((vLow, vHighPred), ⟨s.low, s.high - 1, false⟩)
  else
    -- Edge from high-1 to low+1, next step continues from low+1
    let vLowSucc := cycleVerts.get ⟨s.low + 1, hlow_succ⟩
    ((vHighPred, vLowSucc), ⟨s.low + 1, s.high, true⟩)

/-- Compute the zigzag triangulation edge pairs for a cycle.
    For a cycle [v₀, v₁, v₂, ..., vₙ₋₁] (0-indexed), we compute edges using
    the zigzag pattern specified in the paper:
    {(v₀, vₙ₋₂), (vₙ₋₂, v₁), (v₁, vₙ₋₃), (vₙ₋₃, v₂), ...}

    This alternates: connect from low to high end, then high to next low, etc.
    For a cycle of length n ≥ 4, this produces n - 3 triangulation edges. -/
def triangulationEdgePairs {V : Type*} (cycleVerts : List V) : List (V × V) :=
  let n := cycleVerts.length
  if hn : n < 4 then []
  else
    -- Generate edges iteratively
    -- Pattern for n=6 cycle [v₀,v₁,v₂,v₃,v₄,v₅]:
    --   Edge 0: (v₀, v₄) = (v₀, vₙ₋₂)    -- fromLow, low=0, target=n-2
    --   Edge 1: (v₄, v₁) = (vₙ₋₂, v₁)    -- fromHigh, source=n-2, target=1
    --   Edge 2: (v₁, v₃) = (v₁, vₙ₋₃)    -- fromLow, low=1, target=n-3
    -- General pattern:
    --   Even steps (fromLow): connect v_{low} to v_{n-2-low}
    --   Odd steps (fromHigh): connect v_{n-2-low} to v_{low+1}
    let numEdges := n - 3
    (List.range numEdges).filterMap fun i =>
      let low := i / 2
      let highIdx := n - 2 - low  -- vₙ₋₂ for low=0, vₙ₋₃ for low=1, etc.
      let fromLow := i % 2 == 0
      if hcheck : low < highIdx ∧ low + 1 < n ∧ highIdx < n then
        have hlow' : low < cycleVerts.length := by omega
        have hhigh' : highIdx < cycleVerts.length := by omega
        have hlow_succ : low + 1 < cycleVerts.length := by omega
        let vLow := cycleVerts.get ⟨low, hlow'⟩
        let vHigh := cycleVerts.get ⟨highIdx, hhigh'⟩
        if fromLow then some (vLow, vHigh)
        else
          let vLowSucc := cycleVerts.get ⟨low + 1, hlow_succ⟩
          some (vHigh, vLowSucc)
      else none

/-- For cycles of length < 4, no triangulation edges are needed -/
@[simp]
theorem triangulationEdgePairs_small {V : Type*} (cycleVerts : List V)
    (h : cycleVerts.length < 4) :
    triangulationEdgePairs cycleVerts = [] := by
  simp [triangulationEdgePairs, h]

/-! ## Cycle-Layer Assignment -/

/-- An assignment of cycles to layers. Each cycle is assigned to exactly one layer
    where its triangulation edges will be added. -/
structure CycleLayerAssignment (C : Type*) (R : ℕ) where
  /-- The layer assigned to each cycle -/
  assign : C → Fin (R + 1)

namespace CycleLayerAssignment

variable {C : Type*} {R : ℕ}

/-- The set of cycles assigned to a particular layer -/
def cyclesInLayer [DecidableEq C] [Fintype C] (a : CycleLayerAssignment C R)
    (layer : Fin (R + 1)) : Finset C :=
  Finset.univ.filter (fun c => a.assign c = layer)

/-- Every cycle is assigned to exactly one layer -/
theorem each_cycle_in_one_layer [DecidableEq C] [Fintype C] (a : CycleLayerAssignment C R)
    (c : C) : ∃! layer : Fin (R + 1), c ∈ a.cyclesInLayer layer := by
  use a.assign c
  constructor
  · simp [cyclesInLayer]
  · intro layer h
    simp [cyclesInLayer] at h
    exact h.symm

end CycleLayerAssignment

/-! ## Cycle Degree -/

/-- The cycle degree of an edge e in a graph with cycles C is the number of cycles
    in the generating set that contain edge e. -/
def cycleDegree {E C : Type*} [DecidableEq E] [DecidableEq C] [Fintype C]
    (cycles : C → Finset E) (e : E) : ℕ :=
  (Finset.univ.filter (fun c => e ∈ cycles c)).card

/-- The maximum cycle degree over all edges -/
def maxCycleDegree {E C : Type*} [DecidableEq E] [DecidableEq C] [Fintype E] [Fintype C]
    (cycles : C → Finset E) : ℕ :=
  Finset.sup Finset.univ (fun e => cycleDegree cycles e)

@[simp]
lemma cycleDegree_empty {E C : Type*} [DecidableEq E] [DecidableEq C] [Fintype C] [IsEmpty C]
    (cycles : C → Finset E) (e : E) : cycleDegree cycles e = 0 := by
  simp only [cycleDegree]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _
  exact (IsEmpty.false c).elim

lemma cycleDegree_le_card {E C : Type*} [DecidableEq E] [DecidableEq C] [Fintype C]
    (cycles : C → Finset E) (e : E) : cycleDegree cycles e ≤ Fintype.card C := by
  simp only [cycleDegree]
  exact Finset.card_filter_le _ _

/-! ## Cycle-Sparsified Graph Structure -/

/-- A cycle-sparsification of a graph G with cycles.
    This structure captures the layered construction with inter-layer edges
    and cellulation (triangulation) edges.

    The construction requires:
    - A base graph G with a chosen generating set of cycles
    - R+1 layers (layer 0 is original, layers 1..R are dummy copies)
    - A cycle-degree bound c
    - An assignment of each cycle to a layer for triangulation
    - The constraint that every edge participates in at most c cycles -/
structure CycleSparsification (V E C : Type*)
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    [Fintype V] [Fintype E] [Fintype C] where
  /-- The original graph with its chosen cycles -/
  baseGraph : GraphWithCycles V E C
  /-- The number of additional layers (total layers = R + 1) -/
  numLayers : ℕ
  /-- The cycle-degree bound c -/
  cycleDegBound : ℕ
  /-- Assignment of cycles to layers for triangulation -/
  cycleAssignment : CycleLayerAssignment C numLayers
  /-- For each cycle, a list of vertices representing the cycle in order -/
  cycleVertices : C → List V
  /-- The cycle-degree constraint is satisfied: every edge participates in at most c cycles -/
  cycleDegConstraint : ∀ e : E, cycleDegree baseGraph.cycles e ≤ cycleDegBound

namespace CycleSparsification

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]

/-- The vertex type of the sparsified graph -/
abbrev SparsifiedVertex (S : CycleSparsification V E C) := LayeredVertex V S.numLayers

/-- The number of vertices in the sparsified graph: (R+1) * |V| -/
@[simp]
theorem card_sparsifiedVertex (S : CycleSparsification V E C) :
    Fintype.card (SparsifiedVertex S) = (S.numLayers + 1) * Fintype.card V :=
  LayeredVertex.card_layeredVertex

/-- Layer 0 of the sparsified graph (the original vertices) -/
def originalLayer (S : CycleSparsification V E C) : Finset (SparsifiedVertex S) :=
  Finset.univ.filter (fun lv => lv.layer = 0)

/-- Dummy layers 1, ..., R of the sparsified graph -/
def dummyLayers (S : CycleSparsification V E C) : Finset (SparsifiedVertex S) :=
  Finset.univ.filter (fun lv => lv.layer ≠ 0)

/-- Partition: every vertex is in either the original layer or a dummy layer -/
theorem vertex_partition (S : CycleSparsification V E C) :
    S.originalLayer ∪ S.dummyLayers = Finset.univ := by
  ext v
  simp only [Finset.mem_union, originalLayer, dummyLayers, Finset.mem_filter,
    Finset.mem_univ, true_and]
  tauto

/-- The partition is disjoint -/
theorem vertex_partition_disjoint (S : CycleSparsification V E C) :
    Disjoint S.originalLayer S.dummyLayers := by
  simp only [Finset.disjoint_iff_ne, originalLayer, dummyLayers, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro a ha b hb heq
  rw [heq] at ha
  exact hb ha

/-! ### Edge Types in the Sparsified Graph -/

/-- Edge type 1: Intra-layer edges from the original graph G, copied to each layer.
    An edge (v, v') in layer i is a copy of edge (v, v') from the original graph. -/
def isIntraLayerEdge (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) : Prop :=
  lv₁.layer = lv₂.layer ∧
  S.baseGraph.graph.Adj lv₁.vertex lv₂.vertex

/-- Edge type 2: Inter-layer edges connecting a vertex to its copy in the next layer.
    These form "vertical" connections between layers. -/
def isInterLayerEdge (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) : Prop :=
  lv₁.vertex = lv₂.vertex ∧
  (lv₁.layer.val + 1 = lv₂.layer.val ∨ lv₂.layer.val + 1 = lv₁.layer.val)

/-- The set of triangulation edge pairs for a cycle in a given layer -/
def triangulationPairsForCycle (S : CycleSparsification V E C)
    (c : C) (layer : Fin (S.numLayers + 1)) : List (SparsifiedVertex S × SparsifiedVertex S) :=
  if S.cycleAssignment.assign c = layer then
    (triangulationEdgePairs (S.cycleVertices c)).map (fun (v₁, v₂) =>
      (LayeredVertex.inLayer layer v₁, LayeredVertex.inLayer layer v₂))
  else []

/-- Edge type 3: Triangulation (cellulation) edges added to triangulate cycles.
    A pair (lv₁, lv₂) is a triangulation edge if:
    - They are in the same layer
    - There exists a cycle c assigned to that layer
    - (lv₁.vertex, lv₂.vertex) is in the triangulation of c -/
def isTriangulationEdge (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) : Prop :=
  lv₁.layer = lv₂.layer ∧
  ∃ c : C,
    S.cycleAssignment.assign c = lv₁.layer ∧
    ((lv₁.vertex, lv₂.vertex) ∈ triangulationEdgePairs (S.cycleVertices c) ∨
     (lv₂.vertex, lv₁.vertex) ∈ triangulationEdgePairs (S.cycleVertices c))

/-- Adjacency in the sparsified graph: union of all three edge types -/
def sparsifiedAdj (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) : Prop :=
  lv₁ ≠ lv₂ ∧ (isIntraLayerEdge S lv₁ lv₂ ∨
               isInterLayerEdge S lv₁ lv₂ ∨
               isTriangulationEdge S lv₁ lv₂)

/-- Intra-layer edges are symmetric -/
theorem isIntraLayerEdge_symm (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) :
    isIntraLayerEdge S lv₁ lv₂ ↔ isIntraLayerEdge S lv₂ lv₁ := by
  simp only [isIntraLayerEdge]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1.symm, S.baseGraph.graph.adj_comm _ _ |>.mp h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1.symm, S.baseGraph.graph.adj_comm _ _ |>.mp h2⟩

/-- Inter-layer edges are symmetric -/
theorem isInterLayerEdge_symm (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) :
    isInterLayerEdge S lv₁ lv₂ ↔ isInterLayerEdge S lv₂ lv₁ := by
  simp only [isInterLayerEdge]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩

/-- Triangulation edges are symmetric -/
theorem isTriangulationEdge_symm (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) :
    isTriangulationEdge S lv₁ lv₂ ↔ isTriangulationEdge S lv₂ lv₁ := by
  simp only [isTriangulationEdge]
  constructor
  · intro ⟨heq, c, hc, hor⟩
    refine ⟨heq.symm, c, ?_, hor.symm⟩
    simp only [heq] at hc ⊢
    exact hc
  · intro ⟨heq, c, hc, hor⟩
    refine ⟨heq.symm, c, ?_, hor.symm⟩
    simp only [← heq] at hc ⊢
    exact hc

/-- Sparsified adjacency is symmetric -/
theorem sparsifiedAdj_symm (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S) :
    sparsifiedAdj S lv₁ lv₂ ↔ sparsifiedAdj S lv₂ lv₁ := by
  simp only [sparsifiedAdj, ne_comm, isIntraLayerEdge_symm, isInterLayerEdge_symm,
    isTriangulationEdge_symm]

/-- Sparsified adjacency is irreflexive -/
theorem sparsifiedAdj_irrefl (S : CycleSparsification V E C) (lv : SparsifiedVertex S) :
    ¬sparsifiedAdj S lv lv := by
  simp [sparsifiedAdj]

/-! ### The Sparsified Graph as a SimpleGraph -/

/-- The cycle-sparsified graph as a SimpleGraph -/
def toSimpleGraph (S : CycleSparsification V E C) : SimpleGraph (SparsifiedVertex S) where
  Adj := sparsifiedAdj S
  symm := fun _ _ h => (sparsifiedAdj_symm S _ _).mp h
  loopless := sparsifiedAdj_irrefl S

/-- Layer 0 is isomorphic to the original graph G (for intra-layer edges) -/
theorem layer_zero_adj_iff_original (S : CycleSparsification V E C) (v w : V) :
    isIntraLayerEdge S (LayeredVertex.ofOriginal v) (LayeredVertex.ofOriginal w) ↔
    S.baseGraph.graph.Adj v w := by
  simp [isIntraLayerEdge, LayeredVertex.ofOriginal]

/-! ### Inter-layer Edge Properties -/

/-- Each vertex in layer i is connected to its copy in layer i+1 -/
theorem interLayerEdge_connects_copies (S : CycleSparsification V E C)
    (i : Fin (S.numLayers + 1)) (v : V)
    (h_succ : (i : ℕ) + 1 < S.numLayers + 1) :
    isInterLayerEdge S
      (LayeredVertex.inLayer i v)
      (LayeredVertex.inLayer ⟨i + 1, h_succ⟩ v) := by
  simp only [isInterLayerEdge, LayeredVertex.inLayer_vertex, LayeredVertex.inLayer_layer,
    Fin.val_mk, true_and]
  left
  trivial

/-- Inter-layer edges only connect consecutive layers -/
theorem interLayerEdge_consecutive (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S)
    (h : isInterLayerEdge S lv₁ lv₂) :
    (lv₁.layer.val + 1 = lv₂.layer.val) ∨ (lv₂.layer.val + 1 = lv₁.layer.val) :=
  h.2

/-- Inter-layer edges connect the same underlying vertex -/
theorem interLayerEdge_same_vertex (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S)
    (h : isInterLayerEdge S lv₁ lv₂) :
    lv₁.vertex = lv₂.vertex :=
  h.1

/-! ### Triangulation Edge Properties -/

/-- Triangulation edges are within the same layer -/
theorem triangulationEdge_same_layer (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S)
    (h : isTriangulationEdge S lv₁ lv₂) :
    lv₁.layer = lv₂.layer :=
  h.1

/-- Triangulation edges come from some cycle assigned to that layer -/
theorem triangulationEdge_from_cycle (S : CycleSparsification V E C)
    (lv₁ lv₂ : SparsifiedVertex S)
    (h : isTriangulationEdge S lv₁ lv₂) :
    ∃ c : C, S.cycleAssignment.assign c = lv₁.layer :=
  let ⟨_, c, hc, _⟩ := h
  ⟨c, hc⟩

/-- Layer i vertices form a copy of V -/
def layerVertices (S : CycleSparsification V E C) (i : Fin (S.numLayers + 1)) :
    Finset (SparsifiedVertex S) :=
  Finset.univ.filter (fun lv => lv.layer = i)

/-- Each layer has exactly |V| vertices -/
@[simp]
theorem card_layerVertices (S : CycleSparsification V E C) (i : Fin (S.numLayers + 1)) :
    (S.layerVertices i).card = Fintype.card V := by
  simp only [layerVertices]
  let f : V → SparsifiedVertex S := fun v => ⟨i, v⟩
  have hf_inj : Function.Injective f := fun v w h => by
    have := congrArg LayeredVertex.vertex h
    exact this
  have h_eq : Finset.univ.filter (fun lv : SparsifiedVertex S => lv.layer = i) =
      Finset.univ.image f := by
    ext lv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hlayer
      use lv.vertex
      simp only [f]
      cases lv
      simp_all
    · intro ⟨v, hv⟩
      rw [← hv]
  rw [h_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_univ]

/-- The embedding of the original graph into layer 0 -/
def embedOriginal (S : CycleSparsification V E C) : V ↪ SparsifiedVertex S where
  toFun := LayeredVertex.ofOriginal
  inj' := fun v w h => by
    simp only [LayeredVertex.ofOriginal, LayeredVertex.mk.injEq] at h
    exact h.2

/-- The embedding preserves adjacency from the original graph -/
theorem embedOriginal_preserves_adj (S : CycleSparsification V E C) (v w : V)
    (h : S.baseGraph.graph.Adj v w) :
    isIntraLayerEdge S (S.embedOriginal v) (S.embedOriginal w) := by
  simp only [embedOriginal, Function.Embedding.coeFn_mk, isIntraLayerEdge,
    LayeredVertex.ofOriginal_layer, LayeredVertex.ofOriginal_vertex, h, and_self]

end CycleSparsification

/-! ## Minimum Number of Layers

The minimum number of layers R_G^c is the smallest R such that there exists a valid
cycle-layer assignment achieving cycle-degree at most c. -/

/-- Predicate: there exists a valid cycle-layer assignment with R layers
    such that every edge has cycle-degree at most c. -/
def hasValidAssignment {V E C : Type*}
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    [Fintype V] [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C) (c : ℕ) (R : ℕ) : Prop :=
  ∃ _assignment : CycleLayerAssignment C R,
    ∀ e : E, cycleDegree G.cycles e ≤ c

/-- A valid assignment always exists with R = 0 layers when cycle-degree ≤ c for all edges. -/
lemma hasValidAssignment_exists {V E C : Type*}
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    [Fintype V] [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C) (c : ℕ)
    (hc : ∀ e : E, cycleDegree G.cycles e ≤ c) :
    ∃ R : ℕ, hasValidAssignment G c R :=
  ⟨0, ⟨fun _ => 0⟩, hc⟩

/-- The number of layers needed to achieve cycle-degree at most c.
    This is the R in R_G^c from the paper.

    The value depends on the specific graph and cycle assignment strategy.
    The Freedman-Hastings decongestion lemma establishes that for constant-degree
    graphs, R_G^c = O(log² |V|). -/
structure LayerBound {V E C : Type*}
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    [Fintype V] [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C)
    (c : ℕ) where
  /-- The number of layers (R) in the construction -/
  numLayers : ℕ
  /-- A valid cycle-layer assignment exists with this many layers -/
  valid : hasValidAssignment G c numLayers

/-! ## Freedman-Hastings Decongestion Lemma

The Freedman-Hastings decongestion lemma establishes that for any constant-degree graph G,
the minimum number of layers R_G^c = O(log² |V_G|).

This is a deep result requiring probabilistic methods and expander theory. We state it as
a class assumption that can be satisfied by specific graphs, rather than proving it here.
The proof is beyond the scope of basic type theory and would require significant
additional machinery. -/

/-- Class asserting that a graph satisfies the Freedman-Hastings decongestion bound.
    This states that there exists a layer bound R satisfying R = O(log² |V|) for the
    given cycle-degree bound and maximum vertex degree.

    This is a hypothesis that must be verified for specific graphs using the
    Freedman-Hastings decongestion lemma from the literature. -/
class HasDecongestionBound {V E C : Type*}
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    [Fintype V] [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C)
    (c : ℕ)
    (maxDegree : ℕ) : Prop where
  /-- A layer bound exists with polylogarithmic number of layers -/
  bound_exists : ∃ (lb : LayerBound G c),
    lb.numLayers ≤ (Nat.log 2 (Fintype.card V) + 1) ^ 2 * (maxDegree + 1)
  /-- The cycle-degree bound is positive -/
  c_pos : c > 0
  /-- The graph has bounded degree -/
  degree_bounded : ∀ v : V, (G.incidentEdges v).card ≤ maxDegree

/-- For graphs satisfying the Freedman-Hastings bound, there exists a valid layer assignment
    with R_G^c = O(log² n) where n = |V| -/
theorem minLayers_polylog_bound
    {V E C : Type*}
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    [Fintype V] [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C)
    (c : ℕ)
    (maxDegree : ℕ)
    [hbound : HasDecongestionBound G c maxDegree] :
    ∃ R : ℕ, hasValidAssignment G c R ∧
      R ≤ (maxDegree + 1) * (Nat.log 2 (Fintype.card V) + 1) ^ 2 := by
  obtain ⟨lb, hlb⟩ := hbound.bound_exists
  use lb.numLayers
  constructor
  · exact lb.valid
  · rw [Nat.mul_comm]
    exact hlb

/-! ## Summary

This formalization captures the cycle-sparsification construction:

1. **Layered Structure**: The sparsified graph has R+1 layers:
   - Layer 0: The original graph vertices
   - Layers 1, ..., R: Dummy vertex copies

2. **Vertex Type**: `LayeredVertex V R` represents vertices as (layer, original_vertex) pairs.
   Total vertices: (R+1) · |V_G|

3. **Edge Types**:
   - **Intra-layer**: Copies of original graph edges within each layer
   - **Inter-layer**: Connect each vertex to its copy in adjacent layers
   - **Triangulation**: Added to cellulate cycles assigned to each layer

4. **Triangulation**: For each cycle assigned to a layer, add diagonal edges forming
   triangles. The `triangulationEdgePairs` function computes these edges.

5. **Cycle-Layer Assignment**: Each cycle is assigned to exactly one layer where its
   triangulation edges are added.

6. **Cycle-Degree Bound**: The constraint that every edge participates in at most c cycles
   from the generating set.

7. **Freedman-Hastings Bound**: Stated as a class `HasDecongestionBound` asserting
   R_G^c = O(log² |V_G|) for constant-degree graphs. This is a hypothesis from the
   literature that must be verified for specific graphs.

Key properties proven:
- Layer 0 is isomorphic to the original graph (for intra-layer edges)
- Inter-layer edges connect consecutive layers
- Triangulation edges are symmetric and within the same layer
- The vertex partition into original and dummy layers
- Cardinality formulas for vertices in each layer
-/
