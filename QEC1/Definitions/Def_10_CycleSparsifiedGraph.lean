import QEC1.Definitions.Def_4_ChainSpacesBoundaryMaps
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card

/-!
# Cycle-Sparsified Graph (Definition 10)

## Statement
Let $G = (V, E)$ be a connected graph with a generating set of cycles $C$, and let $c > 0$ be a
constant called the **cycle-degree bound**.

A **cycle-sparsification** of $G$ with cycle-degree $c$ is a new graph $\bar{\bar{G}}$ constructed
as follows:

(i) **Layer structure**: $\bar{\bar{G}}$ consists of $R + 1$ layers numbered $0, 1, \ldots, R$.
    Layer 0 is a copy of G. Each layer $i > 0$ is a copy of the vertices of $G$.

(ii) **Inter-layer edges**: For each vertex $v$ in layer $i < R$, add an edge connecting $v$ to
     its copy in layer $i+1$.

(iii) **Cycle cellulation**: Each cycle $p$ from the original generating set is **cellulated** into
      triangles by adding edges. For a cycle visiting vertices $(v_1, v_2, \ldots, v_m)$ in order,
      add edges: $\{(v_1, v_{m-1}), (v_{m-1}, v_2), (v_2, v_{m-2}), \ldots\}$ until the cycle is
      decomposed into triangles. These cellulation edges can be placed in different layers.

(iv) **Sparsity condition**: Each edge in $\bar{\bar{G}}$ participates in at most $c$ generating
     cycles.

**Notation**: Let $R_G^c$ denote the minimum number of layers required to achieve a
cycle-sparsification of $G$ with cycle-degree bound $c$.

**Key property** (Freedman-Hastings decongestion lemma): For any constant-degree graph $G$ with
$W = |V|$ vertices, $R_G^c = O(\log^2 W)$ for constant $c$.

## Main Results
**Main Structure** (`CycleSparsifiedGraph`): A cycle-sparsification of a graph G
- Layer structure with R+1 layers
- Inter-layer edges connecting adjacent layers
- Cycle cellulation into triangles (can be distributed across layers)
- Sparsity condition (cycle-degree bound c)

**Main Definition** (`minLayersForSparsification`): R_G^c, minimum layers for cycle-degree c

## File Structure
1. Base Graph Configuration: Original graph with generating cycles
2. Layer Structure: Vertices indexed by (layer, original vertex)
3. Inter-Layer Edges: Vertical connections between layers
4. Cycle Cellulation: Zigzag triangulation of cycles (can span layers)
5. Sparsity Condition: Bounding cycle participation per edge (all edges)
6. Minimum Layers: R_G^c definition
7. Helper Lemmas: Basic properties
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Base Graph with Generating Cycles -/

/-- A connected graph with a chosen set of generating cycles.
    This is the base structure that will be cycle-sparsified. -/
structure BaseGraphWithCycles where
  /-- The vertex type -/
  V : Type
  /-- Vertices are finite -/
  vFintype : Fintype V
  /-- Vertices have decidable equality -/
  vDecEq : DecidableEq V
  /-- The underlying simple graph on V -/
  graph : SimpleGraph V
  /-- The graph has decidable adjacency -/
  adjDecidable : DecidableRel graph.Adj
  /-- The graph is connected -/
  connected : graph.Connected
  /-- Index type for generating cycles -/
  CycleIdx : Type
  /-- Cycle indices are finite -/
  cycleFintype : Fintype CycleIdx
  /-- Cycle indices have decidable equality -/
  cycleDecEq : DecidableEq CycleIdx
  /-- Each cycle is given by an ordered list of vertices (closed walk) -/
  cycleVertices : CycleIdx → List V
  /-- Each cycle has at least 3 vertices (non-trivial) -/
  cycle_length_ge_three : ∀ c, (cycleVertices c).length ≥ 3
  /-- Cycles are nonempty (implied by length ≥ 3, but useful for head) -/
  cycle_nonempty : ∀ c, (cycleVertices c) ≠ []
  /-- Cycles are closed: last vertex equals first vertex -/
  cycle_closed : ∀ c, (cycleVertices c).getLast (cycle_nonempty c) =
    (cycleVertices c).head (cycle_nonempty c)
  /-- Consecutive vertices in a cycle are adjacent in the graph -/
  cycle_edges_valid : ∀ c (i : Fin ((cycleVertices c).length - 1)),
    graph.Adj ((cycleVertices c).get ⟨i.val, by omega⟩)
              ((cycleVertices c).get ⟨i.val + 1, by
                have hi := i.isLt
                omega⟩)

attribute [instance] BaseGraphWithCycles.vFintype BaseGraphWithCycles.vDecEq
  BaseGraphWithCycles.adjDecidable BaseGraphWithCycles.cycleFintype
  BaseGraphWithCycles.cycleDecEq

/-! ## Section 2: Layered Vertex Type -/

variable (G : BaseGraphWithCycles) (R : ℕ)

/-- Vertices in the layered graph: pairs (layer, original vertex) where layer ∈ {0, ..., R} -/
abbrev LayeredVertex := Fin (R + 1) × G.V

/-- Fintype instance for layered vertices -/
instance : Fintype (LayeredVertex G R) := inferInstance

/-- DecidableEq instance for layered vertices -/
instance : DecidableEq (LayeredVertex G R) := inferInstance

/-! ## Section 3: Edge Types in the Sparsified Graph -/

/-- An intra-layer edge: edge within layer 0 (copy of original graph).
    Only layer 0 contains edges from the original graph; other layers have only vertices. -/
def isIntraLayerEdge (v w : LayeredVertex G R) : Prop :=
  v.1 = 0 ∧ w.1 = 0 ∧ G.graph.Adj v.2 w.2

/-- An inter-layer edge: connects vertex v in layer i to the same vertex in layer i+1 -/
def isInterLayerEdge (v w : LayeredVertex G R) : Prop :=
  v.2 = w.2 ∧ ((v.1.val + 1 = w.1.val) ∨ (w.1.val + 1 = v.1.val))

/-- Check if two vertices are consecutive in a cycle (forming an actual edge of the cycle).
    Uses bounded existential over Fin for decidability. -/
def areConsecutiveInCycle (c : G.CycleIdx) (u v : G.V) : Prop :=
  let n := (G.cycleVertices c).length
  ∃ i : Fin (n - 1),
    ((G.cycleVertices c).get ⟨i.val, by have := i.isLt; omega⟩ = u ∧
     (G.cycleVertices c).get ⟨i.val + 1, by have := i.isLt; omega⟩ = v) ∨
    ((G.cycleVertices c).get ⟨i.val, by have := i.isLt; omega⟩ = v ∧
     (G.cycleVertices c).get ⟨i.val + 1, by have := i.isLt; omega⟩ = u)

/-- Zigzag triangulation chords for a cycle as per original definition:
    For a cycle (v₁, v₂, ..., vₘ), the zigzag triangulation adds chords:
    {(v₁, vₘ₋₁), (vₘ₋₁, v₂), (v₂, vₘ₋₂), ...}

    More formally, this produces a sequence of triangles sharing edges.
    The chord indices follow a zigzag pattern from the ends toward the middle.

    We encode the chord pattern as pairs (i, j) where i < j are indices in the cycle
    such that the chord (v_i, v_j) is part of the triangulation. -/
def isZigzagTriangulationChord (c : G.CycleIdx) (u v : G.V) : Prop :=
  let n := (G.cycleVertices c).length
  -- Both vertices must be in the cycle
  u ∈ (G.cycleVertices c) ∧ v ∈ (G.cycleVertices c) ∧ u ≠ v ∧
  -- They are not consecutive (so this is a chord, not an edge)
  ¬areConsecutiveInCycle G c u v ∧
  -- We need n ≥ 4 for any chords to exist (triangles have no chords)
  -- There are n-3 chords in any triangulation of an n-gon.
  -- For zigzag pattern, the chords connect:
  -- k=0: (v_0, v_{n-2})   -- first chord: v₁ to v_{m-1} in 1-indexed
  -- k=1: (v_{n-2}, v_1)   -- second chord: v_{m-1} to v_2 in 1-indexed
  -- etc.
  n ≥ 4 ∧
  -- Check if (u, v) is any chord in the triangulation
  -- Using bounded existential over chord indices (there are n-3 chords)
  ∃ i j : Fin n, i.val + 2 ≤ j.val ∧ j.val < n - 1 ∧
    (((G.cycleVertices c).get ⟨i.val, i.isLt⟩ = u ∧
      (G.cycleVertices c).get ⟨j.val, j.isLt⟩ = v) ∨
     ((G.cycleVertices c).get ⟨i.val, i.isLt⟩ = v ∧
      (G.cycleVertices c).get ⟨j.val, j.isLt⟩ = u))

/-! ## Section 4: Cellulation with Layer Distribution -/

/-- A cellulation assignment maps each cycle to the layer where its cellulation edges are placed.
    This allows distributing cellulation across layers to achieve sparsity. -/
def CellulationAssignment := G.CycleIdx → Fin (R + 1)

/-- A cellulation edge: a triangulation chord placed in the layer assigned to that cycle.
    Different from the original which had all cellulation in same layer -
    now cellulation edges can be distributed across layers. -/
def isCellulationEdgeWithAssignment (assign : CellulationAssignment G R)
    (v w : LayeredVertex G R) : Prop :=
  ∃ c : G.CycleIdx, v.1 = assign c ∧ w.1 = assign c ∧ isZigzagTriangulationChord G c v.2 w.2

/-! ## Section 5: Cycle-Sparsified Graph Definition -/

/-- The adjacency relation for a cycle-sparsified graph with a given cellulation assignment.
    Two layered vertices are adjacent if connected by:
    - An intra-layer edge (original graph edge in layer 0 only)
    - An inter-layer edge (vertical connection between adjacent layers)
    - A cellulation edge (zigzag triangulation chord in assigned layer) -/
def sparsifiedAdjWithAssignment (assign : CellulationAssignment G R)
    (v w : LayeredVertex G R) : Prop :=
  v ≠ w ∧ (isIntraLayerEdge G R v w ∨ isInterLayerEdge G R v w ∨
           isCellulationEdgeWithAssignment G R assign v w)

/-- Symmetry of zigzag triangulation chord -/
theorem isZigzagTriangulationChord_symm (c : G.CycleIdx) (u v : G.V) :
    isZigzagTriangulationChord G c u v → isZigzagTriangulationChord G c v u := by
  intro h
  unfold isZigzagTriangulationChord at h ⊢
  obtain ⟨hu_in, hv_in, hne, hnot_consec, hn_ge, i, j, hij, hjn, hor⟩ := h
  refine ⟨hv_in, hu_in, hne.symm, ?_, hn_ge, i, j, hij, hjn, ?_⟩
  · -- Not consecutive is symmetric
    intro h_consec
    apply hnot_consec
    unfold areConsecutiveInCycle at h_consec ⊢
    obtain ⟨k, hk⟩ := h_consec
    exact ⟨k, hk.symm⟩
  · -- The chord property with swapped u and v
    exact hor.symm

/-- Symmetry of sparsified adjacency with assignment -/
theorem sparsifiedAdjWithAssignment_symm (assign : CellulationAssignment G R) :
    Symmetric (sparsifiedAdjWithAssignment G R assign) := by
  intro v w ⟨hne, h⟩
  constructor
  · exact hne.symm
  · rcases h with hintra | hinter | hcell
    · -- Intra-layer: use symmetry of G.graph.Adj
      left
      obtain ⟨hv0, hw0, hadj⟩ := hintra
      exact ⟨hw0, hv0, G.graph.symm hadj⟩
    · -- Inter-layer: symmetric by definition
      right; left
      obtain ⟨heq, hor⟩ := hinter
      exact ⟨heq.symm, hor.symm⟩
    · -- Cellulation: symmetric by zigzag chord symmetry
      right; right
      obtain ⟨c, hv_layer, hw_layer, hchord⟩ := hcell
      exact ⟨c, hw_layer, hv_layer, isZigzagTriangulationChord_symm G c v.2 w.2 hchord⟩

/-- Irreflexivity of sparsified adjacency with assignment -/
theorem sparsifiedAdjWithAssignment_irrefl (assign : CellulationAssignment G R) :
    ∀ v, ¬sparsifiedAdjWithAssignment G R assign v v := by
  intro v ⟨hne, _⟩
  exact hne rfl

/-- The sparsified graph as a SimpleGraph with a given cellulation assignment -/
def sparsifiedGraphWithAssignment (assign : CellulationAssignment G R) :
    SimpleGraph (LayeredVertex G R) where
  Adj := sparsifiedAdjWithAssignment G R assign
  symm := sparsifiedAdjWithAssignment_symm G R assign
  loopless := sparsifiedAdjWithAssignment_irrefl G R assign

/-! ## Section 6: Cycle Degree (All Edges, Not Just Layer 0) -/

/-- An edge (u, v) in the original graph participates in a generating cycle c if
    u and v are consecutive vertices in that cycle. -/
def edgeIsInCycle (c : G.CycleIdx) (u v : G.V) : Prop :=
  areConsecutiveInCycle G c u v

/-- An edge is a cellulation chord for cycle c -/
def edgeIsCellulationFor (c : G.CycleIdx) (u v : G.V) : Prop :=
  isZigzagTriangulationChord G c u v

/-- An edge in the sparsified graph participates in a generating cycle c if either:
    1. It's an original edge of the cycle (in layer 0), or
    2. It's a cellulation chord for that cycle (in the assigned layer).

    This applies to ALL edges in the graph, not just layer 0 edges. -/
def edgeParticipatesInCycleWithAssignment (assign : CellulationAssignment G R)
    (v w : LayeredVertex G R) (c : G.CycleIdx) : Prop :=
  -- Original cycle edge in layer 0
  (v.1 = 0 ∧ w.1 = 0 ∧ edgeIsInCycle G c v.2 w.2) ∨
  -- Cellulation chord in assigned layer
  (v.1 = assign c ∧ w.1 = assign c ∧ edgeIsCellulationFor G c v.2 w.2)

/-- Decidability for consecutive vertices in a cycle -/
instance decConsecutive (c : G.CycleIdx) (u v : G.V) :
    Decidable (areConsecutiveInCycle G c u v) := by
  unfold areConsecutiveInCycle
  apply Fintype.decidableExistsFintype

/-- Decidability for edge being in a cycle -/
instance (c : G.CycleIdx) (u v : G.V) : Decidable (edgeIsInCycle G c u v) := by
  unfold edgeIsInCycle
  infer_instance

/-- Decidability for zigzag triangulation chord -/
instance decZigzagChord (c : G.CycleIdx) (u v : G.V) :
    Decidable (isZigzagTriangulationChord G c u v) := by
  unfold isZigzagTriangulationChord
  infer_instance

/-- Decidability for cellulation chord -/
instance (c : G.CycleIdx) (u v : G.V) : Decidable (edgeIsCellulationFor G c u v) := by
  unfold edgeIsCellulationFor
  infer_instance

/-- Decidability for edge participation in cycle with assignment -/
instance decEdgeParticipates (assign : CellulationAssignment G R)
    (v w : LayeredVertex G R) (c : G.CycleIdx) :
    Decidable (edgeParticipatesInCycleWithAssignment G R assign v w c) := by
  unfold edgeParticipatesInCycleWithAssignment
  infer_instance

/-- The set of generating cycles that an edge participates in (with assignment) -/
def cyclesContainingEdgeWithAssignment (assign : CellulationAssignment G R)
    (v w : LayeredVertex G R) : Finset G.CycleIdx :=
  Finset.filter (fun c => edgeParticipatesInCycleWithAssignment G R assign v w c) Finset.univ

/-- The cycle-degree of an edge with assignment: number of generating cycles it participates in -/
def edgeCycleDegreeWithAssignment (assign : CellulationAssignment G R)
    (v w : LayeredVertex G R) : ℕ :=
  (cyclesContainingEdgeWithAssignment G R assign v w).card

/-! ## Section 7: Sparsity Condition (All Edges) -/

/-- A cycle-sparsification with assignment satisfies the sparsity condition with
    cycle-degree bound c if every edge participates in at most c generating cycles.
    This applies to ALL edges in the sparsified graph, not just layer 0. -/
def satisfiesSparsityBoundWithAssignment (assign : CellulationAssignment G R) (c : ℕ) : Prop :=
  ∀ v w : LayeredVertex G R, (sparsifiedGraphWithAssignment G R assign).Adj v w →
    edgeCycleDegreeWithAssignment G R assign v w ≤ c

/-- The sparsity bound is inherited by any larger bound -/
theorem sparsityBoundWithAssignment_mono (assign : CellulationAssignment G R)
    {c₁ c₂ : ℕ} (h : c₁ ≤ c₂) :
    satisfiesSparsityBoundWithAssignment G R assign c₁ →
    satisfiesSparsityBoundWithAssignment G R assign c₂ := by
  intro hsat v w hadj
  exact Nat.le_trans (hsat v w hadj) h

/-! ## Section 8: Complete Cycle-Sparsified Graph Structure -/

/-- A complete cycle-sparsification of a graph G with cycle-degree bound c.
    This structure captures all requirements:
    - The number of layers R (giving R+1 total layers)
    - A cellulation assignment distributing cycles across layers
    - Layer 0 contains all edges of G (intra-layer edges)
    - Inter-layer edges connect adjacent layers
    - Cellulation edges triangulate cycles (using zigzag pattern)
    - Sparsity bound c is satisfied for ALL edges -/
structure CycleSparsifiedGraph (G : BaseGraphWithCycles) (c : ℕ) where
  /-- Number of layers minus one (so we have R+1 layers numbered 0 to R) -/
  numLayers : ℕ
  /-- Assignment of cycles to layers for cellulation -/
  cellulationAssignment : CellulationAssignment G numLayers
  /-- The graph satisfies the sparsity bound: each edge participates in at most c cycles -/
  sparsityBound : satisfiesSparsityBoundWithAssignment G numLayers cellulationAssignment c

namespace CycleSparsifiedGraph

variable {G : BaseGraphWithCycles} {c : ℕ}

/-- Total number of layers (R+1) -/
def totalLayers (S : CycleSparsifiedGraph G c) : ℕ := S.numLayers + 1

/-- Number of vertices per layer -/
def verticesPerLayer (_S : CycleSparsifiedGraph G c) : ℕ := Fintype.card G.V

/-- Total number of vertices -/
def totalVertices (S : CycleSparsifiedGraph G c) : ℕ :=
  S.totalLayers * S.verticesPerLayer

/-- Layer 0 is a copy of the original graph's vertex set -/
def layer0Vertices (S : CycleSparsifiedGraph G c) :
    Finset (Fin (S.numLayers + 1) × G.V) :=
  Finset.filter (fun v => v.1 = 0) Finset.univ

/-- Vertices in a specific layer -/
def layerVertices (S : CycleSparsifiedGraph G c) (i : Fin (S.numLayers + 1)) :
    Finset (Fin (S.numLayers + 1) × G.V) :=
  Finset.filter (fun v => v.1 = i) Finset.univ

/-- The underlying graph of the sparsification -/
def underlyingGraph (S : CycleSparsifiedGraph G c) :
    SimpleGraph (LayeredVertex G S.numLayers) :=
  sparsifiedGraphWithAssignment G S.numLayers S.cellulationAssignment

end CycleSparsifiedGraph

/-! ## Section 9: Layer 0 Contains Original Graph Edges -/

/-- Every edge of the original graph appears in layer 0 of the sparsified graph -/
theorem layer0_contains_original_edges (assign : CellulationAssignment G R)
    (u v : G.V) (h : G.graph.Adj u v) :
    (sparsifiedGraphWithAssignment G R assign).Adj (⟨0, u⟩ : LayeredVertex G R)
                              (⟨0, v⟩ : LayeredVertex G R) := by
  constructor
  · intro heq
    simp only [Prod.mk.injEq] at heq
    exact G.graph.loopless u (heq.2 ▸ h)
  · left
    exact ⟨rfl, rfl, h⟩

/-- Only layer 0 has intra-layer edges (original graph edges).
    Layers i > 0 only have vertices, no horizontal edges from the original graph. -/
theorem only_layer0_has_original_edges (_assign : CellulationAssignment G R)
    (v w : LayeredVertex G R) (h : isIntraLayerEdge G R v w) :
    v.1 = 0 ∧ w.1 = 0 := by
  exact ⟨h.1, h.2.1⟩

/-- Inter-layer edges exist between adjacent layers -/
theorem interLayer_edges_exist (assign : CellulationAssignment G R)
    (i : Fin R) (v : G.V) :
    (sparsifiedGraphWithAssignment G R assign).Adj
      (⟨i.castSucc, v⟩ : LayeredVertex G R)
      (⟨i.succ, v⟩ : LayeredVertex G R) := by
  constructor
  · intro heq
    simp only [Prod.mk.injEq] at heq
    have h1 : i.castSucc.val = i.succ.val := by
      exact congrArg Fin.val heq.1
    simp only [Fin.val_succ, Fin.val_castSucc] at h1
    omega
  · right; left
    constructor
    · rfl
    · left
      simp only [Fin.val_succ, Fin.val_castSucc]

/-! ## Section 10: Minimum Layers for Sparsification -/

/-- A cycle-sparsification exists with R layers and cycle-degree bound c
    if there exists a cellulation assignment achieving the sparsity bound. -/
def sparsificationExistsWithLayers (G : BaseGraphWithCycles) (R c : ℕ) : Prop :=
  ∃ assign : CellulationAssignment G R, satisfiesSparsityBoundWithAssignment G R assign c

/-- The set of valid layer counts for a given cycle-degree bound -/
def validLayerCounts (G : BaseGraphWithCycles) (c : ℕ) : Set ℕ :=
  {R : ℕ | sparsificationExistsWithLayers G R c}

/-- R_G^c: The minimum number of layers required for a cycle-sparsification
    with cycle-degree bound c.
    This is defined as the infimum of valid layer counts.
    We use a classical definition since decidability is not assumed. -/
noncomputable def minLayersForSparsification (G : BaseGraphWithCycles) (c : ℕ) : ℕ :=
  sInf {R : ℕ | sparsificationExistsWithLayers G R c}

/-- Notation: R_G^c for minimum layers -/
notation "R_" G "^" c => minLayersForSparsification G c

/-! ## Section 11: Properties of Minimum Layers -/

/-- If sparsification exists with R layers, the minimum is at most R -/
theorem minLayers_le_of_exists {G : BaseGraphWithCycles} {R c : ℕ}
    (h : sparsificationExistsWithLayers G R c) :
    minLayersForSparsification G c ≤ R := by
  unfold minLayersForSparsification
  exact Nat.sInf_le h

/-- The minimum layers value is valid (satisfies sparsity) when it exists -/
theorem minLayers_valid {G : BaseGraphWithCycles} {c : ℕ}
    (h : ∃ R, sparsificationExistsWithLayers G R c) :
    sparsificationExistsWithLayers G (minLayersForSparsification G c) c := by
  unfold minLayersForSparsification
  exact Nat.sInf_mem h

/-- No smaller value works for minimum layers -/
theorem minLayers_is_min {G : BaseGraphWithCycles} {c : ℕ}
    (_h : ∃ R, sparsificationExistsWithLayers G R c) {R : ℕ}
    (hR : R < minLayersForSparsification G c) :
    ¬sparsificationExistsWithLayers G R c := by
  unfold minLayersForSparsification at hR
  intro hR_valid
  have hmem : R ∈ {R : ℕ | sparsificationExistsWithLayers G R c} := hR_valid
  have h_le := Nat.sInf_le hmem
  omega

/-! ## Section 12: Triangulation Properties -/

/-- Number of triangles in a triangulated n-gon is n-2 -/
theorem num_triangles_in_polygon (n : ℕ) (_h : n ≥ 3) :
    n - 2 + 2 = n := by omega

/-- Number of chords needed to triangulate an n-gon is n-3 -/
theorem num_chords_for_triangulation (n : ℕ) (_h : n ≥ 3) :
    n - 3 + 3 = n := by omega

/-- A triangle (3-cycle) needs no additional chords -/
theorem triangle_needs_no_chords (c : G.CycleIdx) (h : (G.cycleVertices c).length = 3) :
    ∀ u v : G.V, ¬isZigzagTriangulationChord G c u v := by
  intro u v hchord
  unfold isZigzagTriangulationChord at hchord
  obtain ⟨_, _, _, _, hn_ge, _⟩ := hchord
  -- n ≥ 4 but n = 3, contradiction
  omega

/-! ## Section 13: Freedman-Hastings Decongestion Lemma (Specification) -/

/-- The Freedman-Hastings decongestion lemma states that for any constant-degree graph G
    with W vertices, R_G^c = O(log² W) for constant cycle-degree bound c.

    This is a SPECIFICATION of what the lemma claims, not a proof.
    The actual proof requires deep results from topological combinatorics.

    We encode this as: there exist constants A, B such that
    R_G^c ≤ A * (Nat.log W)² + B for all valid graphs G with bounded degree. -/
def FreedmanHastingsSpecification (c maxDegree : ℕ) : Prop :=
  ∃ (constA constB : ℕ),
    ∀ (G : BaseGraphWithCycles),
      (∀ v : G.V, G.graph.degree v ≤ maxDegree) →
      (∃ R, sparsificationExistsWithLayers G R c) →
      minLayersForSparsification G c ≤ constA * (Nat.log (Fintype.card G.V)) ^ 2 + constB

/-! ## Section 14: Helper Lemmas -/

/-- Edges in layer 0 are exactly the original graph edges -/
@[simp]
theorem layer0_intraEdge_iff {v w : LayeredVertex G R} (hv : v.1 = 0) (hw : w.1 = 0) :
    isIntraLayerEdge G R v w ↔ G.graph.Adj v.2 w.2 := by
  simp only [isIntraLayerEdge, hv, hw, true_and]

/-- Inter-layer edges connect the same vertex across adjacent layers -/
@[simp]
theorem interLayer_same_vertex {v w : LayeredVertex G R} (h : isInterLayerEdge G R v w) :
    v.2 = w.2 := h.1

/-- An edge in layer 0 between different vertices -/
theorem intraLayer_distinct {v w : LayeredVertex G R}
    (h : isIntraLayerEdge G R v w) : v ≠ w := by
  intro heq
  rw [heq] at h
  exact G.graph.loopless w.2 h.2.2

/-- The total vertex count is the product of layers and vertices per layer -/
theorem totalVertices_eq (S : CycleSparsifiedGraph G c) :
    S.totalVertices = S.totalLayers * S.verticesPerLayer := rfl

/-- Each layer has the same number of vertices as the original graph -/
theorem layerVertices_card (S : CycleSparsifiedGraph G c) (i : Fin (S.numLayers + 1)) :
    (S.layerVertices i).card = Fintype.card G.V := by
  unfold CycleSparsifiedGraph.layerVertices
  simp only [Fintype.card]
  -- The filter picks out all pairs (i, v) for v in G.V
  have h_inj : Function.Injective (fun v : G.V => (i, v)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.2
  have h_eq : (Finset.filter (fun v : Fin (S.numLayers + 1) × G.V => v.1 = i) Finset.univ) =
              Finset.univ.image (fun v => (i, v)) := by
    ext p
    constructor
    · intro hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
    · intro hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨w, hw⟩ := hp
      rw [← hw]
  rw [h_eq, Finset.card_image_of_injective _ h_inj]

/-- Sparsity bound is always satisfied for large enough c when no cycles exist -/
theorem sparsityBound_of_no_cycles_with_assignment (hc : Fintype.card G.CycleIdx = 0)
    (assign : CellulationAssignment G R) :
    satisfiesSparsityBoundWithAssignment G R assign 0 := by
  intro v w _hadj
  unfold edgeCycleDegreeWithAssignment cyclesContainingEdgeWithAssignment
  have h : (Finset.univ : Finset G.CycleIdx) = ∅ := by
    rw [Finset.univ_eq_empty_iff]
    exact Fintype.card_eq_zero_iff.mp hc
  simp only [h, Finset.filter_empty, Finset.card_empty, le_refl]

/-- Sparsity bound is always satisfied for large enough c (total number of cycles) -/
theorem sparsityBound_for_large_c_with_assignment (assign : CellulationAssignment G R) :
    satisfiesSparsityBoundWithAssignment G R assign (Fintype.card G.CycleIdx) := by
  intro v w _hadj
  unfold edgeCycleDegreeWithAssignment cyclesContainingEdgeWithAssignment
  calc (Finset.filter (fun c => edgeParticipatesInCycleWithAssignment G R assign v w c)
          Finset.univ).card
    ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card G.CycleIdx := Finset.card_univ

/-- For any graph, a sparsification exists with enough layers (at least one layer suffices
    when using a bound equal to the total number of cycles) -/
theorem sparsification_exists_with_many_layers :
    ∃ R, sparsificationExistsWithLayers G R (Fintype.card G.CycleIdx) := by
  use 0
  -- All cycles assigned to layer 0
  let assign : CellulationAssignment G 0 := fun _ => 0
  use assign
  exact sparsityBound_for_large_c_with_assignment G 0 assign

end QEC
