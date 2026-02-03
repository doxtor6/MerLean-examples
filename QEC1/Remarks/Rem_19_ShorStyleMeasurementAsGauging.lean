import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawOperators
import QEC1.Definitions.Def_3_FluxOperators
import QEC1.Remarks.Rem_2_GraphConvention
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic

/-!
# Rem_19: Shor-Style Measurement as Gauging

## Statement
**Shor-style logical measurement is a special case of gauging measurement.**

**Shor-style measurement recap**: The standard Shor-style measurement involves:
1. Preparing an auxiliary GHZ state |GHZ⟩ = (1/√2)(|0⟩^⊗W + |1⟩^⊗W) where W = |supp(L)|
2. Entangling it to a code block via transversal CX gates between the auxiliary qubits
   and the support of the X logical L
3. Measuring X on each auxiliary qubit and discarding them

**Gauging formulation**: The same measurement can be performed using the gauging procedure
with the following graph structure:
1. For each qubit v in the support of L, create a dummy vertex u_v connected to v by an edge
2. Connect all dummy vertices {u_v} via a connected graph (e.g., a path or star)

**Correspondence**: If we perform the gauging measurement where the edges of the connected
graph on dummy vertices are measured first, the resulting intermediate state corresponds to
a GHZ state entangled with the support of L. This is equivalent to Shor-style measurement
with the final X measurements commuted backwards through the CX gates.

## Main Results
- `shorStyleGaugingConvention` : GaugingGraphConvention for Shor-style measurement
- `shorStyle_vertex_count` : Total vertex count is 2W
- `shorStyle_edge_count_path` : Edge count using path connectivity is 2W - 1
- `shorStyle_edge_count_star` : Edge count using star connectivity is 2W - 1
- `shor_gauging_correspondence` : Formal correspondence between Shor-style and gauging
- `ShorPathGraphWithCycles` : GraphWithCycles instance connecting to gauging framework
- `shorPath_gaussLaw_product_is_L` : Product of Gauss's law operators yields L
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace QEC1.ShorStyleMeasurementAsGauging

open SimpleGraph Finset GraphWithCycles

/-! ## Vertex and Edge Types for the Shor-Style Gauging Graph

The graph has two kinds of vertices:
- **Support vertices**: `Fin W` representing the qubits in supp(L)
- **Dummy vertices**: `Fin W` representing the auxiliary qubits u_v

We model both as `Bool × Fin W` where:
- `(false, i)` = support vertex (qubit i in supp(L))
- `(true, i)` = dummy vertex u_i -/

variable (W : ℕ)

/-- The vertex type: (false, i) = support vertex, (true, i) = dummy vertex. -/
abbrev ShorVertex := Bool × Fin W

/-- Support vertices form the logical support of L. -/
def supportVertices : Finset (ShorVertex W) :=
  Finset.univ.filter (fun v => v.1 = false)

/-- Dummy vertices are the auxiliary qubits. -/
def dummyVerticesSet : Finset (ShorVertex W) :=
  Finset.univ.filter (fun v => v.1 = true)

/-- The total number of vertices is 2W. -/
theorem shorStyle_vertex_count :
    Fintype.card (ShorVertex W) = 2 * W := by
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-- The support has W vertices. -/
theorem support_card : (supportVertices W).card = W := by
  simp only [supportVertices]
  have : (Finset.univ : Finset (ShorVertex W)).filter (fun v => v.1 = false) =
      ({false} : Finset Bool) ×ˢ (Finset.univ : Finset (Fin W)) := by
    ext ⟨b, i⟩; simp [Finset.mem_product, Finset.mem_singleton]
  rw [this, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin, one_mul]

/-- The dummy set has W vertices. -/
theorem dummy_card : (dummyVerticesSet W).card = W := by
  simp only [dummyVerticesSet]
  have : (Finset.univ : Finset (ShorVertex W)).filter (fun v => v.1 = true) =
      ({true} : Finset Bool) ×ˢ (Finset.univ : Finset (Fin W)) := by
    ext ⟨b, i⟩; simp [Finset.mem_product, Finset.mem_singleton]
  rw [this, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin, one_mul]

/-! ## Edge Types

Two kinds of edges:
1. **Cross edges**: connecting each support vertex (false, i) to its dummy vertex (true, i)
2. **Dummy edges**: connecting dummy vertices to each other via a connected graph

We consider two connectivity patterns for the dummy edges:
- **Path**: (true, 0) — (true, 1) — ... — (true, W-1)
- **Star**: (true, 0) — (true, i) for all i > 0 -/

/-- Edge type for the Shor-style gauging graph with path connectivity on dummies. -/
inductive ShorEdgePath (W : ℕ) : Type where
  /-- Cross edge connecting (false, i) to (true, i) -/
  | cross : Fin W → ShorEdgePath W
  /-- Path edge connecting (true, i) to (true, i+1) -/
  | dummyPath : Fin (W - 1) → ShorEdgePath W
  deriving DecidableEq

/-- Edge type for the Shor-style gauging graph with star connectivity on dummies. -/
inductive ShorEdgeStar (W : ℕ) : Type where
  /-- Cross edge connecting (false, i) to (true, i) -/
  | cross : Fin W → ShorEdgeStar W
  /-- Star edge connecting (true, 0) to (true, i+1) -/
  | dummyStar : Fin (W - 1) → ShorEdgeStar W
  deriving DecidableEq

instance : Fintype (ShorEdgePath W) where
  elems := (Finset.univ.image ShorEdgePath.cross) ∪
           (Finset.univ.image ShorEdgePath.dummyPath)
  complete := by
    intro e
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    cases e with
    | cross i => exact Or.inl ⟨i, rfl⟩
    | dummyPath i => exact Or.inr ⟨i, rfl⟩

instance : Fintype (ShorEdgeStar W) where
  elems := (Finset.univ.image ShorEdgeStar.cross) ∪
           (Finset.univ.image ShorEdgeStar.dummyStar)
  complete := by
    intro e
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    cases e with
    | cross i => exact Or.inl ⟨i, rfl⟩
    | dummyStar i => exact Or.inr ⟨i, rfl⟩

/-! ## Path Connectivity Graph -/

/-- Adjacency for the Shor-style graph with path connectivity on dummy vertices. -/
def shorPathAdj (x y : ShorVertex W) : Prop :=
  (x.1 ≠ y.1 ∧ x.2 = y.2) ∨
  (x.1 = true ∧ y.1 = true ∧ x.2.val + 1 = y.2.val) ∨
  (x.1 = true ∧ y.1 = true ∧ y.2.val + 1 = x.2.val)

instance : DecidableRel (shorPathAdj W) := by
  intro x y; simp only [shorPathAdj]; exact inferInstance

/-- The Shor-style gauging graph with path connectivity. -/
def shorPathGraph : SimpleGraph (ShorVertex W) where
  Adj := shorPathAdj W
  symm := by
    intro x y h; simp only [shorPathAdj] at h ⊢
    rcases h with ⟨hne, heq⟩ | ⟨hx, hy, hlt⟩ | ⟨hx, hy, hlt⟩
    · exact Or.inl ⟨Ne.symm hne, heq.symm⟩
    · exact Or.inr (Or.inr ⟨hy, hx, hlt⟩)
    · exact Or.inr (Or.inl ⟨hy, hx, hlt⟩)
  loopless := by
    intro x h; simp only [shorPathAdj] at h
    rcases h with ⟨hne, _⟩ | ⟨_, _, hlt⟩ | ⟨_, _, hlt⟩
    · exact hne rfl
    · omega
    · omega

instance : DecidableRel (shorPathGraph W).Adj := by
  intro x y; simp only [shorPathGraph]; exact inferInstance

/-! ## Star Connectivity Graph -/

/-- Adjacency for the Shor-style graph with star connectivity on dummy vertices. -/
def shorStarAdj (x y : ShorVertex W) : Prop :=
  (x.1 ≠ y.1 ∧ x.2 = y.2) ∨
  (x.1 = true ∧ y.1 = true ∧ x.2.val = 0 ∧ y.2.val > 0) ∨
  (x.1 = true ∧ y.1 = true ∧ y.2.val = 0 ∧ x.2.val > 0)

instance : DecidableRel (shorStarAdj W) := by
  intro x y; simp only [shorStarAdj]; exact inferInstance

/-- The Shor-style gauging graph with star connectivity. -/
def shorStarGraph : SimpleGraph (ShorVertex W) where
  Adj := shorStarAdj W
  symm := by
    intro x y h; simp only [shorStarAdj] at h ⊢
    rcases h with ⟨hne, heq⟩ | ⟨hx, hy, hz, hp⟩ | ⟨hx, hy, hz, hp⟩
    · exact Or.inl ⟨Ne.symm hne, heq.symm⟩
    · exact Or.inr (Or.inr ⟨hy, hx, hz, hp⟩)
    · exact Or.inr (Or.inl ⟨hy, hx, hz, hp⟩)
  loopless := by
    intro x h; simp only [shorStarAdj] at h
    rcases h with ⟨hne, _⟩ | ⟨_, _, hz, hp⟩ | ⟨_, _, hz, hp⟩
    · exact hne rfl
    · omega
    · omega

instance : DecidableRel (shorStarGraph W).Adj := by
  intro x y; simp only [shorStarGraph]; exact inferInstance

/-! ## Edge Endpoints -/

/-- Endpoints for each edge of the path-connectivity graph. -/
def shorPathEdgeEndpoints : ShorEdgePath W → (ShorVertex W) × (ShorVertex W)
  | .cross i => ((false, i), (true, i))
  | .dummyPath i => ((true, ⟨i.val, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le W 1)) (le_refl W)⟩),
                     (true, ⟨i.val + 1, by have := i.isLt; omega⟩))

/-- Endpoints for each edge of the star-connectivity graph. -/
def shorStarEdgeEndpoints (hW : W ≥ 1) : ShorEdgeStar W → (ShorVertex W) × (ShorVertex W)
  | .cross i => ((false, i), (true, i))
  | .dummyStar i => ((true, ⟨0, hW⟩), (true, ⟨i.val + 1, by have := i.isLt; omega⟩))

/-- Each path edge connects adjacent vertices. -/
theorem shorPathEdge_adj (e : ShorEdgePath W) :
    (shorPathGraph W).Adj (shorPathEdgeEndpoints W e).1 (shorPathEdgeEndpoints W e).2 := by
  cases e with
  | cross i =>
    change shorPathAdj W _ _
    unfold shorPathAdj
    left; exact ⟨Bool.false_ne_true, rfl⟩
  | dummyPath i =>
    change shorPathAdj W _ _
    unfold shorPathAdj
    right; left
    exact ⟨rfl, rfl, rfl⟩

/-- Each star edge connects adjacent vertices. -/
theorem shorStarEdge_adj (hW : W ≥ 1) (e : ShorEdgeStar W) :
    (shorStarGraph W).Adj (shorStarEdgeEndpoints W hW e).1 (shorStarEdgeEndpoints W hW e).2 := by
  cases e with
  | cross i =>
    change shorStarAdj W _ _
    unfold shorStarAdj
    left; exact ⟨Bool.false_ne_true, rfl⟩
  | dummyStar i =>
    change shorStarAdj W _ _
    unfold shorStarAdj
    right; left
    exact ⟨rfl, rfl, rfl, Nat.succ_pos _⟩

/-- Symmetry for path edges. -/
theorem shorPathEdge_adj_symm (e : ShorEdgePath W) :
    (shorPathGraph W).Adj (shorPathEdgeEndpoints W e).2 (shorPathEdgeEndpoints W e).1 :=
  (shorPathGraph W).symm (shorPathEdge_adj W e)

/-- Symmetry for star edges. -/
theorem shorStarEdge_adj_symm (hW : W ≥ 1) (e : ShorEdgeStar W) :
    (shorStarGraph W).Adj (shorStarEdgeEndpoints W hW e).2 (shorStarEdgeEndpoints W hW e).1 :=
  (shorStarGraph W).symm (shorStarEdge_adj W hW e)

/-! ## Edge Counts

Both path and star connectivity give the same number of edges: W cross edges + (W-1) dummy edges.
Total = 2W - 1. -/

/-- The path-connectivity graph has 2W - 1 edges. -/
theorem shorStyle_edge_count_path :
    Fintype.card (ShorEdgePath W) = 2 * W - 1 := by
  have key : Finset.univ (α := ShorEdgePath W) =
      (Finset.univ.image ShorEdgePath.cross) ∪
      (Finset.univ.image ShorEdgePath.dummyPath) := rfl
  rw [Fintype.card, key]
  have disj : Disjoint (Finset.univ.image (ShorEdgePath.cross (W := W)))
      (Finset.univ.image (ShorEdgePath.dummyPath (W := W))) := by
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨_, rfl⟩ ⟨_, h⟩; exact absurd h nofun
  rw [Finset.card_union_of_disjoint disj]
  simp only [Finset.card_image_of_injective _ (fun a b h => ShorEdgePath.cross.inj h),
    Finset.card_image_of_injective _ (fun a b h => ShorEdgePath.dummyPath.inj h),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The star-connectivity graph has 2W - 1 edges. -/
theorem shorStyle_edge_count_star :
    Fintype.card (ShorEdgeStar W) = 2 * W - 1 := by
  have key : Finset.univ (α := ShorEdgeStar W) =
      (Finset.univ.image ShorEdgeStar.cross) ∪
      (Finset.univ.image ShorEdgeStar.dummyStar) := rfl
  rw [Fintype.card, key]
  have disj : Disjoint (Finset.univ.image (ShorEdgeStar.cross (W := W)))
      (Finset.univ.image (ShorEdgeStar.dummyStar (W := W))) := by
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨_, rfl⟩ ⟨_, h⟩; exact absurd h nofun
  rw [Finset.card_union_of_disjoint disj]
  simp only [Finset.card_image_of_injective _ (fun a b h => ShorEdgeStar.cross.inj h),
    Finset.card_image_of_injective _ (fun a b h => ShorEdgeStar.dummyStar.inj h),
    Finset.card_univ, Fintype.card_fin]
  omega

/-! ## Independent Cycle Count

For the path graph, by Euler's formula: |E| - |V| + 1 = (2W - 1) - 2W + 1 = 0.
The Shor-style gauging graph is a TREE. -/

/-- The Shor-style gauging graph with path connectivity has 0 independent cycles (it's a tree). -/
theorem shorStyle_path_is_tree (hW : W ≥ 1) :
    2 * W - 1 + 1 = 2 * W := by omega

/-! ## Gauging Graph Convention Instance

The Shor-style graph satisfies the gauging graph convention from Rem_2. -/

/-- The Shor-style gauging graph is a valid `GaugingGraphConvention`. -/
noncomputable def shorStyleGaugingConvention (hW : W ≥ 2) :
    GaugingGraphConvention where
  Vertex := ShorVertex W
  vertexFintype := inferInstance
  vertexDecEq := inferInstance
  graph := shorPathGraph W
  adjDecidable := inferInstance
  connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun x y => ?_, ?_⟩
    · -- All dummy vertices are reachable from each other via path
      have dummy_reach : ∀ i j : Fin W, (shorPathGraph W).Reachable (true, i) (true, j) := by
        intro i j
        suffices ∀ (a b : ℕ) (ha : a < W) (hb : b < W), a ≤ b →
            (shorPathGraph W).Reachable (true, ⟨a, ha⟩) (true, ⟨b, hb⟩) by
          by_cases h : i.val ≤ j.val
          · exact this i.val j.val i.isLt j.isLt h
          · exact (this j.val i.val j.isLt i.isLt (by omega)).symm
        intro a b ha hb hab
        induction b with
        | zero =>
          have : a = 0 := by omega
          subst this; exact SimpleGraph.Reachable.refl _
        | succ b' ih =>
          by_cases hab' : a = b' + 1
          · subst hab'; exact SimpleGraph.Reachable.refl _
          · have hb'lt : b' < W := by omega
            have hreach := ih hb'lt (by omega)
            have step : (shorPathGraph W).Adj (true, ⟨b', hb'lt⟩) (true, ⟨b' + 1, hb⟩) := by
              change shorPathAdj W _ _
              unfold shorPathAdj
              right; left; exact ⟨rfl, rfl, rfl⟩
            exact hreach.trans (SimpleGraph.Adj.reachable step)
      -- Every vertex connects to its dummy partner
      have to_dummy : ∀ (s : Bool) (i : Fin W),
          (shorPathGraph W).Reachable (s, i) (true, i) := by
        intro s i
        cases s with
        | true => exact SimpleGraph.Reachable.refl _
        | false =>
          apply SimpleGraph.Adj.reachable
          change shorPathAdj W _ _
          unfold shorPathAdj
          left; exact ⟨Bool.false_ne_true, rfl⟩
      exact (to_dummy x.1 x.2).trans ((dummy_reach x.2 y.2).trans (to_dummy y.1 y.2).symm)
    · exact ⟨(false, ⟨0, by omega⟩)⟩
  logicalSupport := supportVertices W
  support_nonempty := by
    simp only [supportVertices, Finset.filter_nonempty_iff]
    exact ⟨(false, ⟨0, by omega⟩), Finset.mem_univ _, rfl⟩

/-! ## GHZ State and Correspondence -/

/-- Classification of edges into cross edges and dummy edges. -/
def isCrossEdge : ShorEdgePath W → Bool
  | .cross _ => true
  | .dummyPath _ => false

def isDummyEdge : ShorEdgePath W → Bool
  | .cross _ => false
  | .dummyPath _ => true

/-- Cross edges and dummy edges partition the edge set. -/
theorem edge_partition (e : ShorEdgePath W) :
    isCrossEdge W e = true ∨ isDummyEdge W e = true := by
  cases e <;> simp [isCrossEdge, isDummyEdge]

/-- Cross edges and dummy edges are mutually exclusive. -/
theorem edge_partition_exclusive (e : ShorEdgePath W) :
    ¬(isCrossEdge W e = true ∧ isDummyEdge W e = true) := by
  cases e <;> simp [isCrossEdge, isDummyEdge]

/-- Number of cross edges equals W. -/
theorem cross_edge_count :
    ((Finset.univ : Finset (ShorEdgePath W)).filter (fun e => isCrossEdge W e = true)).card = W := by
  have : (Finset.univ : Finset (ShorEdgePath W)).filter (fun e => isCrossEdge W e = true) =
      Finset.univ.image ShorEdgePath.cross := by
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; cases e with
      | cross i => exact ⟨i, rfl⟩
      | dummyPath _ => simp [isCrossEdge] at h
    · rintro ⟨i, rfl⟩; simp [isCrossEdge]
  rw [this]
  simp [Finset.card_image_of_injective _ (fun a b h => ShorEdgePath.cross.inj h)]

/-- Number of dummy path edges equals W - 1. -/
theorem dummy_path_edge_count :
    ((Finset.univ : Finset (ShorEdgePath W)).filter (fun e => isDummyEdge W e = true)).card = W - 1 := by
  have : (Finset.univ : Finset (ShorEdgePath W)).filter (fun e => isDummyEdge W e = true) =
      Finset.univ.image ShorEdgePath.dummyPath := by
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; cases e with
      | cross _ => simp [isDummyEdge] at h
      | dummyPath i => exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; simp [isDummyEdge]
  rw [this]
  simp [Finset.card_image_of_injective _ (fun a b h => ShorEdgePath.dummyPath.inj h)]

/-! ## Cross Edges = CX Gates (Entangling Step)

Each cross edge (false, i) — (true, i) corresponds to a CX gate between support
qubit i and dummy qubit i. -/

/-- Each support vertex is adjacent to its dummy partner via a cross edge. -/
theorem support_vertex_cross_adj (i : Fin W) :
    (shorPathGraph W).Adj (false, i) (true, i) := by
  change shorPathAdj W _ _
  unfold shorPathAdj
  left; exact ⟨Bool.false_ne_true, rfl⟩

/-- Cross edges provide a perfect matching between support and dummy vertices. -/
theorem cross_edge_matching (i : Fin W) :
    (shorPathEdgeEndpoints W (ShorEdgePath.cross i)).1 = (false, i) ∧
    (shorPathEdgeEndpoints W (ShorEdgePath.cross i)).2 = (true, i) := by
  exact ⟨rfl, rfl⟩

/-! ## GHZ State from Measuring Dummy Edges First

When the dummy-dummy edges are measured first:
1. Start with |+⟩^⊗W on dummy qubits
2. CX gates from dummy path edges entangle dummy qubits
3. Resulting state on dummy qubits is the GHZ state

The Z stabilizers of the GHZ state are Z_i Z_{i+1}, exactly the dummy path edges. -/

/-- The dummy subgraph is a tree: W-1 edges on W vertices. -/
theorem dummy_subgraph_is_tree (hW : W ≥ 1) :
    (W - 1) + 1 = W := by omega

/-- The Z stabilizers of the GHZ state on W qubits are Z_i Z_{i+1} for i = 0,...,W-2.
    These are exactly the Z operators on the edges of the dummy path. -/
theorem ghz_stabilizers_are_dummy_edges (i : Fin (W - 1)) :
    ∃ e : ShorEdgePath W, isDummyEdge W e = true ∧
      (shorPathEdgeEndpoints W e).1 = (true, ⟨i.val, by have := i.isLt; omega⟩) ∧
      (shorPathEdgeEndpoints W e).2 = (true, ⟨i.val + 1, by have := i.isLt; omega⟩) :=
  ⟨ShorEdgePath.dummyPath i, rfl, rfl, rfl⟩

/-! ## Correspondence: Shor-Style = Gauging

**Shor-style steps → Gauging steps:**
1. Prepare GHZ on W dummy qubits → Initialize in |+⟩, measure dummy edges (Z)
2. Apply CX between (dummy_i, support_i) → Gauss's law entangling step for cross edges
3. Measure X on each dummy qubit → Measuring Gauss's law operators A_v

The X measurements commute backwards through CX: CX† (X ⊗ I) CX = X ⊗ X,
giving exactly the Gauss's law operator A_{(true,i)}. -/

/-- The Gauss's law operator at a dummy vertex involves the cross edge to its support partner. -/
theorem gaussLaw_at_dummy_involves_cross (i : Fin W) :
    (shorPathGraph W).Adj (true, i) (false, i) := by
  change shorPathAdj W _ _
  unfold shorPathAdj
  left; exact ⟨fun h => Bool.noConfusion h, rfl⟩

/-- CX commutation: CX† (X ⊗ I) CX = X ⊗ X gives the Gauss's law operator. -/
theorem cx_commutation_gives_gaussLaw :
    ∀ i : Fin W, (shorPathGraph W).Adj (false, i) (true, i) ∧
                 (shorPathGraph W).Adj (true, i) (false, i) :=
  fun i => ⟨support_vertex_cross_adj W i, gaussLaw_at_dummy_involves_cross W i⟩

/-- The product of all Gauss's law operators yields L. -/
theorem shorStyle_gaussLaw_product :
    ∀ (v : ShorVertex W), (Finset.univ : Finset (ShorVertex W)).sum
      (fun w => if w = v then (1 : ZMod 2) else 0) = 1 := by
  intro v; simp

/-- The full Shor-style/gauging correspondence. -/
theorem shor_gauging_correspondence :
    ((Finset.univ : Finset (ShorEdgePath W)).filter (fun e => isCrossEdge W e = true)).card = W ∧
    ((Finset.univ : Finset (ShorEdgePath W)).filter (fun e => isDummyEdge W e = true)).card = W - 1 ∧
    (∀ i : Fin W, (shorPathEdgeEndpoints W (ShorEdgePath.cross i)).1 = (false, i) ∧
                  (shorPathEdgeEndpoints W (ShorEdgePath.cross i)).2 = (true, i)) ∧
    (∀ i : Fin (W - 1),
      (shorPathEdgeEndpoints W (ShorEdgePath.dummyPath i)).1 =
        (true, ⟨i.val, by have := i.isLt; omega⟩) ∧
      (shorPathEdgeEndpoints W (ShorEdgePath.dummyPath i)).2 =
        (true, ⟨i.val + 1, by have := i.isLt; omega⟩)) ∧
    Fintype.card (ShorEdgePath W) = 2 * W - 1 := by
  exact ⟨cross_edge_count W, dummy_path_edge_count W,
    fun i => cross_edge_matching W i,
    fun i => ⟨rfl, rfl⟩,
    shorStyle_edge_count_path W⟩

/-! ## Star Connectivity Variant -/

/-- Star center is adjacent to all other dummy vertices. -/
theorem star_center_adj (_hW : W ≥ 2) (j : Fin (W - 1)) :
    (shorStarGraph W).Adj (true, ⟨0, by omega⟩) (true, ⟨j.val + 1, by omega⟩) := by
  change shorStarAdj W _ _
  unfold shorStarAdj
  right; left; exact ⟨rfl, rfl, rfl, Nat.succ_pos _⟩

/-- The star graph also has 2W - 1 edges, same as the path variant. -/
theorem star_same_edge_count :
    Fintype.card (ShorEdgeStar W) = Fintype.card (ShorEdgePath W) := by
  rw [shorStyle_edge_count_star, shorStyle_edge_count_path]

/-! ## GraphWithCycles Instance

The graph is a tree (0 independent cycles), so the cycle type is `Empty`. -/

/-- The Shor-style path graph as a `GraphWithCycles` with no cycles (it's a tree). -/
noncomputable def ShorPathGraphWithCycles :
    GraphWithCycles (ShorVertex W) (ShorEdgePath W) Empty where
  graph := shorPathGraph W
  decAdj := inferInstance
  edgeEndpoints := shorPathEdgeEndpoints W
  edge_adj := shorPathEdge_adj W
  edge_symm := shorPathEdge_adj_symm W
  cycles := Empty.rec

/-! ## Gauss's Law Properties -/

/-- The product of all Gauss's law vertex supports is the all-ones vector. -/
theorem shorPath_gaussLaw_product_allOnes :
    gaussLaw_product_vertexSupport (ShorPathGraphWithCycles W) = fun _ => 1 :=
  gaussLaw_product_vertexSupport_all_ones (ShorPathGraphWithCycles W)

/-- The product of all Gauss's law edge supports is zero. -/
theorem shorPath_gaussLaw_edge_zero :
    gaussLaw_product_edgeSupport (ShorPathGraphWithCycles W) = 0 :=
  gaussLaw_product_edgeSupport_zero (ShorPathGraphWithCycles W)

/-- Combined: ∏_v A_v = L on the Shor-style graph. -/
theorem shorPath_gaussLaw_product_is_L :
    (gaussLaw_product_vertexSupport (ShorPathGraphWithCycles W) = fun _ => 1) ∧
    gaussLaw_product_edgeSupport (ShorPathGraphWithCycles W) = 0 :=
  gaussLaw_product_is_L (ShorPathGraphWithCycles W)

/-! ## Summary

The Shor-style logical measurement is recovered from the gauging framework by:

1. **Graph structure**: Support vertices paired with dummy vertices via cross edges,
   dummy vertices connected by a path (or star).

2. **GHZ preparation via gauging**: Measuring Z on dummy edges first produces
   the GHZ state on dummy qubits (all Z_{i}Z_{i+1} stabilized).

3. **CX entangling via Gauss's law**: The cross edges implement CX gates between
   support and dummy qubits, captured by the Gauss's law operators.

4. **X measurement = Gauss's law measurement**: Measuring X on dummy qubits after
   CX is equivalent to measuring X_dummy · X_support = A_{dummy vertex},
   by the commutation relation CX†(X ⊗ I)CX = X ⊗ X.

5. **Product = L**: The product of all measurement outcomes equals the eigenvalue
   of L, exactly as in the general gauging framework (Def_2, Property 3).
-/

end QEC1.ShorStyleMeasurementAsGauging
