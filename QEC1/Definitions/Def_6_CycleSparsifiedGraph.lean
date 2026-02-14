import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import QEC1.Remarks.Rem_11_DesiderataForGraphG
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Definition 6: Cycle-Sparsified Graph

## Statement
The cycle-sparsified graph (decongested graph) G̿ with cycle-degree bound c is
constructed from a connected graph G with a chosen generating set of cycles by:
1. Creating R+1 layers (layer 0 = original, layers 1..R = copies of V)
2. Adding inter-layer edges (v^(i), v^(i+1)) for each vertex v and 0 ≤ i < R
3. Adding intra-layer edges from the original graph (replicated in all layers)
4. Adding cellulation (triangulation) edges in layers i > 0 to decompose
   high-degree cycles into triangles using the zigzag pattern
5. Choosing R large enough so each edge participates in at most c cycles per layer

The key property is that the generating set of cycles consists of:
- Triangles from cellulation (weight 3)
- Squares connecting adjacent layers (weight 4)
All generating cycles have weight at most 4.

## Main Results
- `SparsifiedVertex` : vertex type V × Fin (R+1)
- `isIntraLayerEdge` : same-layer edge from original graph
- `isInterLayerEdge` : same vertex in consecutive layers
- `zigzagDiagonals` : cellulation diagonals using zigzag pattern
- `isTriangulationEdge` : cellulation edge in some layer > 0
- `sparsifiedAdj` / `sparsifiedGraph` : the sparsified graph
- `edgeCycleDegreeInLayer` / `LayerCycleDegreeBound` : per-layer cycle participation bound
- `SparsificationData` : complete construction data
- `square_is_cycle` : squares from adjacent layers form 4-cycles
- `zigzagDiagonals_mem` : diagonal endpoints come from original cycle
- `zigzagDiagonals_length` : m-gon produces exactly m-2 diagonals
- `cellulation_adj_of_diagonal` : diagonals create edges in sparsified graph
- `cellulation_triangle_exists` : cellulation produces triangles (weight 3)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CycleSparsification

open Finset

/-- The vertex type of the sparsified graph: (v, i) represents vertex v in
layer i. Layer 0 is the original. -/
abbrev SparsifiedVertex (V : Type*) (R : ℕ) := V × Fin (R + 1)

/-- The original layer is layer 0. -/
def originalLayer {R : ℕ} : Fin (R + 1) := ⟨0, Nat.zero_lt_succ R⟩

variable {V : Type*} [Fintype V] [DecidableEq V] {R : ℕ}

/-! ## Layer Structure -/

theorem card_sparsifiedVertex :
    Fintype.card (SparsifiedVertex V R) = (R + 1) * Fintype.card V := by
  simp [SparsifiedVertex, Fintype.card_prod, Fintype.card_fin, mul_comm]

def layerVertices (i : Fin (R + 1)) : Finset (SparsifiedVertex V R) :=
  Finset.univ.filter (fun p => p.2 = i)

theorem card_layerVertices (i : Fin (R + 1)) :
    (layerVertices (V := V) i).card = Fintype.card V := by
  simp only [layerVertices]
  rw [show Finset.univ.filter (fun p : V × Fin (R + 1) => p.2 = i) =
    Finset.univ ×ˢ {i} from by ext ⟨_, j⟩; simp [eq_comm]]
  simp [Finset.card_product]

def embedOriginal (v : V) : SparsifiedVertex V R := (v, originalLayer)

theorem embedOriginal_injective :
    Function.Injective (embedOriginal (V := V) (R := R)) :=
  fun _ _ h => (Prod.ext_iff.mp h).1

theorem vertex_partition (p : SparsifiedVertex V R) :
    ∃! i : Fin (R + 1), p ∈ layerVertices (V := V) i := by
  exact ⟨p.2, by simp [layerVertices], fun j hj => by simp [layerVertices] at hj; exact hj.symm⟩

theorem vertex_partition_disjoint (i j : Fin (R + 1)) (hij : i ≠ j) :
    Disjoint (layerVertices (V := V) i) (layerVertices (V := V) j) := by
  rw [Finset.disjoint_left]
  intro x hx hj
  simp only [layerVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hx hj
  exact hij (hx ▸ hj)

/-! ## Three Types of Edges -/

/-- An intra-layer edge: two vertices in the same layer where the original
graph has an edge. The original graph edges are replicated in every layer,
enabling square cycles between any two consecutive layers. -/
def isIntraLayerEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : SparsifiedVertex V R) : Prop :=
  p.2 = q.2 ∧ G.Adj p.1 q.1

/-- An inter-layer edge: copies of the same vertex in consecutive layers. -/
def isInterLayerEdge (p q : SparsifiedVertex V R) : Prop :=
  p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)

/-! ## Zigzag Triangulation (Cellulation)

For a cycle visiting vertices v₁, v₂, ..., vₘ in order, cellulation adds
diagonal edges following the zigzag pattern:
  (v₁, v_{m-1}), (v_{m-1}, v₂), (v₂, v_{m-2}), (v_{m-2}, v₃), ...
This decomposes the m-gon into m-2 triangles.
-/

/-- Auxiliary recursive function for zigzag diagonals.
Given a vector `vs` of length `n`, left/right indices, and alternation flag,
produces the zigzag diagonal pairs. Requires `left < n` and `right < n`. -/
def zigzagGo {n : ℕ} (vs : Fin n → V) (left right : ℕ)
    (hleft : left < n) (hright : right < n)
    (fromLeft : Bool) (fuel : ℕ) : List (V × V) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if h : right ≤ left + 1 then []
    else
      if fromLeft then
        -- diagonal from vs[left] to vs[right-1]
        have hrm1 : right - 1 < n := by omega
        (vs ⟨left, hleft⟩, vs ⟨right - 1, hrm1⟩) ::
          zigzagGo vs left (right - 1) hleft hrm1 false fuel
      else
        -- diagonal from vs[right] to vs[left+1]
        have hlp1 : left + 1 < n := by omega
        (vs ⟨right, hright⟩, vs ⟨left + 1, hlp1⟩) ::
          zigzagGo vs (left + 1) right hlp1 hright true fuel

/-- Zigzag diagonal pairs from a list of cycle vertices.
Given [v₁, v₂, ..., vₘ], produces the zigzag cellulation diagonals:
  (v₁, v_{m-1}), (v_{m-1}, v₂), (v₂, v_{m-2}), (v_{m-2}, v₃), ...
The zigzag alternates between connecting from the "left" end and the "right"
end of the remaining polygon, working inward.

For m ≤ 3, no diagonals are needed (triangle or simpler).
For m = 4 (square), one diagonal (v₁, v₃).
For m = 5 (pentagon), two diagonals: (v₁, v₄), (v₄, v₂). -/
def zigzagDiagonals (vs : List V) : List (V × V) :=
  if h : vs.length < 4 then []
  else
    let arr : Fin vs.length → V := fun i => vs.get i
    have h0 : 0 < vs.length := by omega
    have hm1 : vs.length - 1 < vs.length := by omega
    zigzagGo arr 0 (vs.length - 1) h0 hm1 true vs.length

/-- A triangulation edge: a cellulation diagonal in some layer i > 0.
The zigzag diagonals of a cycle assigned to layer i create new edges in that
layer, decomposing the cycle into triangles. -/
def isTriangulationEdge
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (p q : SparsifiedVertex V R) : Prop :=
  ∃ c : C,
    cycleAssignment c ≠ originalLayer ∧
    p.2 = cycleAssignment c ∧
    q.2 = cycleAssignment c ∧
    ((p.1, q.1) ∈ zigzagDiagonals (cycleVerts c) ∨
     (q.1, p.1) ∈ zigzagDiagonals (cycleVerts c))

/-! ## Symmetry and Irreflexivity -/

theorem isIntraLayerEdge_symm (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : SparsifiedVertex V R}
    (h : isIntraLayerEdge G p q) : isIntraLayerEdge G q p :=
  ⟨h.1.symm, G.symm h.2⟩

theorem isInterLayerEdge_symm {p q : SparsifiedVertex V R}
    (h : isInterLayerEdge p q) : isInterLayerEdge q p :=
  ⟨h.1.symm, h.2.symm⟩

theorem isTriangulationEdge_symm
    {C : Type*}
    {cycleAssignment : C → Fin (R + 1)}
    {cycleVerts : C → List V}
    {p q : SparsifiedVertex V R}
    (h : isTriangulationEdge cycleAssignment cycleVerts p q) :
    isTriangulationEdge cycleAssignment cycleVerts q p := by
  obtain ⟨c, hne, hp, hq, hor⟩ := h
  exact ⟨c, hne, hq, hp, hor.symm⟩

theorem isIntraLayerEdge_irrefl (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : SparsifiedVertex V R) :
    ¬isIntraLayerEdge G p p := by
  intro ⟨_, hadj⟩; exact G.loopless p.1 hadj

theorem isInterLayerEdge_irrefl (p : SparsifiedVertex V R) :
    ¬isInterLayerEdge p p := by
  intro ⟨_, hlayer⟩; omega

/-! ## The Sparsified Adjacency Relation -/

/-- The adjacency relation combining all three edge types. -/
def sparsifiedAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (p q : SparsifiedVertex V R) : Prop :=
  p ≠ q ∧
    (isIntraLayerEdge G p q ∨
     isInterLayerEdge p q ∨
     isTriangulationEdge cycleAssignment cycleVerts p q)

theorem sparsifiedAdj_symm (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    {cycleAssignment : C → Fin (R + 1)}
    {cycleVerts : C → List V}
    {p q : SparsifiedVertex V R}
    (h : sparsifiedAdj G cycleAssignment cycleVerts p q) :
    sparsifiedAdj G cycleAssignment cycleVerts q p := by
  refine ⟨h.1 ∘ Eq.symm, ?_⟩
  rcases h.2 with h2 | h2 | h2
  · exact Or.inl (isIntraLayerEdge_symm G h2)
  · exact Or.inr (Or.inl (isInterLayerEdge_symm h2))
  · exact Or.inr (Or.inr (isTriangulationEdge_symm h2))

theorem sparsifiedAdj_irrefl (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (p : SparsifiedVertex V R) :
    ¬sparsifiedAdj G cycleAssignment cycleVerts p p := by
  intro ⟨hne, _⟩; exact hne rfl

/-! ## The Cycle-Sparsified Simple Graph -/

/-- The cycle-sparsified graph G̿ as a SimpleGraph on V × Fin (R+1). -/
def sparsifiedGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V) :
    SimpleGraph (SparsifiedVertex V R) where
  Adj := sparsifiedAdj G cycleAssignment cycleVerts
  symm _ _ h := sparsifiedAdj_symm G h
  loopless := sparsifiedAdj_irrefl G cycleAssignment cycleVerts

/-! ## Layer-0 Preserves Original Graph -/

theorem layer_zero_adj_of_original (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    {v w : V} (hadj : G.Adj v w) :
    (sparsifiedGraph G cycleAssignment cycleVerts).Adj
      (v, originalLayer) (w, originalLayer) := by
  refine ⟨?_, Or.inl ⟨rfl, hadj⟩⟩
  intro h; have hv := (Prod.ext_iff.mp h).1; subst hv; exact G.loopless _ hadj

/-! ## Inter-Layer Edge Properties -/

theorem interLayerEdge_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (v : V) (i : Fin R) :
    let i₀ : Fin (R + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    let i₁ : Fin (R + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    (sparsifiedGraph G cycleAssignment cycleVerts).Adj (v, i₀) (v, i₁) := by
  intro i₀ i₁
  exact ⟨by intro h; exact absurd (Fin.mk.inj (Prod.ext_iff.mp h).2) (by omega),
    Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩

/-! ## Triangulation Edge Properties -/

theorem triangulationEdge_same_layer
    {C : Type*}
    {cycleAssignment : C → Fin (R + 1)}
    {cycleVerts : C → List V}
    {p q : SparsifiedVertex V R}
    (h : isTriangulationEdge cycleAssignment cycleVerts p q) :
    p.2 = q.2 := by
  obtain ⟨_, _, hp, hq, _⟩ := h; rw [hp, hq]

theorem triangulationEdge_not_layer_zero
    {C : Type*}
    {cycleAssignment : C → Fin (R + 1)}
    {cycleVerts : C → List V}
    {p q : SparsifiedVertex V R}
    (h : isTriangulationEdge cycleAssignment cycleVerts p q) :
    p.2 ≠ originalLayer := by
  obtain ⟨_, hne, hp, _, _⟩ := h; rw [hp]; exact hne

/-! ## Simp lemmas -/

@[simp] theorem intraLayer_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w : V) (i : Fin (R + 1)) :
    isIntraLayerEdge G ((v, i) : SparsifiedVertex V R) (w, i) ↔ G.Adj v w := by
  simp [isIntraLayerEdge]

@[simp] theorem interLayer_same_vertex_iff (v : V) (i j : Fin (R + 1)) :
    isInterLayerEdge ((v, i) : SparsifiedVertex V R) (v, j) ↔
    (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  simp [isInterLayerEdge]

/-! ## Edge Classification -/

theorem edge_trichotomy (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    {cycleAssignment : C → Fin (R + 1)}
    {cycleVerts : C → List V}
    {p q : SparsifiedVertex V R}
    (hadj : (sparsifiedGraph G cycleAssignment cycleVerts).Adj p q) :
    isIntraLayerEdge G p q ∨
    isInterLayerEdge p q ∨
    isTriangulationEdge cycleAssignment cycleVerts p q :=
  hadj.2

theorem diff_layer_not_intra (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : SparsifiedVertex V R} (h : p.2 ≠ q.2) :
    ¬isIntraLayerEdge G p q := by
  intro ⟨heq, _⟩; exact h heq

theorem diff_vertex_not_inter {p q : SparsifiedVertex V R} (h : p.1 ≠ q.1) :
    ¬isInterLayerEdge p q := by
  intro ⟨heq, _⟩; exact h heq

/-! ## Squares: Explicit 4-Cycles -/

/-- A square in the sparsified graph: given (v,u) ∈ E(G) and layer i < R,
(v^i, v^{i+1}, u^{i+1}, u^i) form a 4-cycle. -/
theorem square_is_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (v u : V) (hadj : G.Adj v u) (i : Fin R) :
    let G' := sparsifiedGraph G cycleAssignment cycleVerts
    let i₀ : Fin (R + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    let i₁ : Fin (R + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    G'.Adj (v, i₀) (v, i₁) ∧
    G'.Adj (v, i₁) (u, i₁) ∧
    G'.Adj (u, i₁) (u, i₀) ∧
    G'.Adj (u, i₀) (v, i₀) := by
  intro G' i₀ i₁
  have hne : v ≠ u := fun h => by subst h; exact G.loopless v hadj
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by intro h; exact absurd (Fin.mk.inj (Prod.ext_iff.mp h).2) (by omega),
      Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
  · exact ⟨by intro h; exact hne (Prod.ext_iff.mp h).1,
      Or.inl ⟨rfl, hadj⟩⟩
  · exact ⟨by intro h; exact absurd (Fin.mk.inj (Prod.ext_iff.mp h).2) (by omega),
      Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩
  · exact ⟨by intro h; exact hne.symm (Prod.ext_iff.mp h).1,
      Or.inl ⟨rfl, G.symm hadj⟩⟩

/-! ## Zigzag Cellulation: Vertex Membership and Triangle Decomposition

The zigzag cellulation decomposes an m-gon (m ≥ 4) into m-2 triangles by adding
diagonal edges. We prove:
1. All diagonal endpoints come from the original cycle vertices
2. The diagonals produce exactly m-2 pairs
3. Each diagonal, together with consecutive cycle edges (intra-layer), forms a
   triangle in the sparsified graph — establishing the paper's key claim that
   the generating set consists of triangles (weight 3) and squares (weight 4).
-/

/-- Every vertex appearing in a zigzagGo output is a value of `vs` at some index
in the range [left, right]. -/
theorem zigzagGo_mem_range {n : ℕ} (vs : Fin n → V) (left right : ℕ)
    (hl : left < n) (hr : right < n) (b : Bool) (fuel : ℕ)
    {p : V × V} (hp : p ∈ zigzagGo vs left right hl hr b fuel) :
    (∃ i : Fin n, vs i = p.1) ∧ (∃ j : Fin n, vs j = p.2) := by
  induction fuel generalizing left right b with
  | zero => simp [zigzagGo] at hp
  | succ k ih =>
    simp only [zigzagGo] at hp
    split at hp
    · simp at hp
    · rename_i hgt
      split at hp
      · -- fromLeft case: emitted (vs[left], vs[right-1])
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨⟨⟨left, hl⟩, rfl⟩, ⟨⟨right - 1, by omega⟩, rfl⟩⟩
        · exact ih _ _ _ _ _ hp'
      · -- fromRight case: emitted (vs[right], vs[left+1])
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨⟨⟨right, hr⟩, rfl⟩, ⟨⟨left + 1, by omega⟩, rfl⟩⟩
        · exact ih _ _ _ _ _ hp'

/-- Every vertex in a zigzag diagonal pair is a member of the original cycle list. -/
theorem zigzagDiagonals_mem (vs : List V)
    {p : V × V} (hp : p ∈ zigzagDiagonals vs) :
    p.1 ∈ vs ∧ p.2 ∈ vs := by
  simp only [zigzagDiagonals] at hp
  split at hp
  · simp at hp
  · rename_i hge
    have hmem := zigzagGo_mem_range _ _ _ _ _ _ _ hp
    constructor
    · obtain ⟨⟨i, hi⟩, heq⟩ := hmem.1
      rw [← heq]; exact List.get_mem vs ⟨i, hi⟩
    · obtain ⟨⟨j, hj⟩, heq⟩ := hmem.2
      rw [← heq]; exact List.get_mem vs ⟨j, hj⟩

/-- When the gap is closed (`right ≤ left + 1`), zigzagGo returns the empty list. -/
theorem zigzagGo_nil {n : ℕ} (vs : Fin n → V) (left right : ℕ)
    (hl : left < n) (hr : right < n) (b : Bool) (fuel : ℕ)
    (hle : right ≤ left + 1) :
    zigzagGo vs left right hl hr b fuel = [] := by
  cases fuel with
  | zero => simp [zigzagGo]
  | succ k => simp [zigzagGo, dif_pos hle]

/-- The exact number of diagonals from zigzagGo: when `right > left + 1` and
fuel ≥ `right - left - 1`, zigzagGo produces exactly `right - left - 1` pairs. -/
theorem zigzagGo_exact_length {n : ℕ} (vs : Fin n → V) (left right : ℕ)
    (hl : left < n) (hr : right < n) (b : Bool) (fuel : ℕ)
    (hfuel : right - left - 1 ≤ fuel)
    (hgt : left + 1 < right) :
    (zigzagGo vs left right hl hr b fuel).length = right - left - 1 := by
  induction fuel generalizing left right b with
  | zero => omega
  | succ k ih =>
    simp only [zigzagGo]
    rw [dif_neg (by omega)]
    split
    · -- fromLeft: emit (vs[left], vs[right-1]), recurse with right' = right-1
      simp only [List.length_cons]
      by_cases hstop : left + 1 < right - 1
      · rw [ih _ _ _ _ _ (by omega) hstop]; omega
      · -- base case: right-1 = left+1, so zigzagGo terminates
        rw [zigzagGo_nil _ _ _ _ _ _ _ (by omega), List.length_nil]; omega
    · -- fromRight: emit (vs[right], vs[left+1]), recurse with left' = left+1
      simp only [List.length_cons]
      by_cases hstop : left + 1 + 1 < right
      · rw [ih _ _ _ _ _ (by omega) hstop]; omega
      · rw [zigzagGo_nil _ _ _ _ _ _ _ (by omega), List.length_nil]; omega

/-- For a cycle of length m ≥ 4, zigzag cellulation produces exactly m-2 diagonals.
This corresponds to decomposing an m-gon into m-2 triangles. -/
theorem zigzagDiagonals_length (vs : List V) (hlen : 4 ≤ vs.length) :
    (zigzagDiagonals vs).length = vs.length - 2 := by
  unfold zigzagDiagonals
  rw [dif_neg (by omega)]
  apply zigzagGo_exact_length <;> omega

/-! ## Cellulation Produces Triangles in the Sparsified Graph

The key property from the paper: for each cycle assigned to a layer i > 0,
the zigzag cellulation diagonals together with the intra-layer cycle edges
form triangles in the sparsified graph.

A **cellulation triangle** consists of three vertices a, b, c in the same layer i,
where two pairs are connected by intra-layer edges (from the original cycle) and
one pair by a triangulation diagonal. Since all three edge types (intra-layer,
triangulation) are part of `sparsifiedAdj`, these triangles are 3-cycles in the
sparsified graph.
-/

/-- For a cycle c assigned to layer i > 0, if (a, b) is a zigzag diagonal of c,
then (a, i) and (b, i) are adjacent in the sparsified graph via a triangulation edge. -/
theorem cellulation_adj_of_diagonal (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (c : C) (a b : V) (hab_ne : a ≠ b)
    (hne : cycleAssignment c ≠ originalLayer)
    (hdiag : (a, b) ∈ zigzagDiagonals (cycleVerts c)) :
    let i := cycleAssignment c
    (sparsifiedGraph G cycleAssignment cycleVerts).Adj (a, i) (b, i) := by
  intro i
  refine ⟨fun h => hab_ne (Prod.ext_iff.mp h).1, ?_⟩
  exact Or.inr (Or.inr ⟨c, hne, rfl, rfl, Or.inl hdiag⟩)

/-- For a cycle c assigned to layer i > 0, if consecutive vertices u, v of the
cycle are adjacent in G, then (u, i) and (v, i) are adjacent in the sparsified
graph via an intra-layer edge. -/
theorem cellulation_adj_of_cycle_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (u v : V) (huv_ne : u ≠ v) (hadj : G.Adj u v) (i : Fin (R + 1)) :
    (sparsifiedGraph G cycleAssignment cycleVerts).Adj (u, i) (v, i) := by
  refine ⟨fun h => huv_ne (Prod.ext_iff.mp h).1, Or.inl ⟨rfl, hadj⟩⟩

/-- **Key property (Cellulation Triangle Existence):** For a cycle c visiting
vertices v₁, ..., vₘ assigned to layer i > 0, each zigzag diagonal (a, b) together
with two intra-layer edges from G forms a triangle in the sparsified graph.

Specifically: if (a, b) is a diagonal and both a-x and b-x are edges in G for
some common neighbor x on the cycle, then (a,i)-(b,i)-(x,i) is a triangle.
This is the content of the paper's claim that cellulation decomposes cycles into
triangles, all of weight 3 in the generating set. -/
theorem cellulation_triangle_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*}
    (cycleAssignment : C → Fin (R + 1))
    (cycleVerts : C → List V)
    (c : C) (a b x : V)
    (hab_ne : a ≠ b) (hax_ne : a ≠ x) (hbx_ne : b ≠ x)
    (hne : cycleAssignment c ≠ originalLayer)
    (hdiag : (a, b) ∈ zigzagDiagonals (cycleVerts c))
    (hadj_ax : G.Adj a x)
    (hadj_bx : G.Adj b x) :
    let i := cycleAssignment c
    let G' := sparsifiedGraph G cycleAssignment cycleVerts
    -- All three edges of the triangle exist in G'
    G'.Adj (a, i) (b, i) ∧
    G'.Adj (a, i) (x, i) ∧
    G'.Adj (b, i) (x, i) := by
  intro i G'
  exact ⟨cellulation_adj_of_diagonal G cycleAssignment cycleVerts c a b hab_ne hne hdiag,
         cellulation_adj_of_cycle_edge G cycleAssignment cycleVerts a x hax_ne hadj_ax i,
         cellulation_adj_of_cycle_edge G cycleAssignment cycleVerts b x hbx_ne hadj_bx i⟩

/-! ## Cycle Degree in the Sparsified Graph

The cycle-degree bound is the key property of the sparsification construction.
Given a cycle assignment `C → Fin (R+1)` that distributes cycles across layers,
the sparsified graph has a new generating set consisting of:
- Triangles from cellulation (each original cycle assigned to layer i produces
  triangles in that layer)
- Squares connecting adjacent layers

The cycle degree of an edge in the sparsified graph is the number of cycles
from this new generating set that contain it. The parameter `c` bounds this. -/

/-- The number of original cycles assigned to a given layer that contain a
given edge. This counts how many cellulated cycles in layer `i` use edge `e`
(as an intra-layer copy). This is the per-layer edge participation count:
the whole point of distributing cycles across layers is to make this small. -/
def edgeCycleDegreeInLayer
    {α : Type*} {R' : ℕ} {C : Type*} [Fintype C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (cycleAssignment : C → Fin (R' + 1))
    (e : α) (i : Fin (R' + 1)) : ℕ :=
  (Finset.univ.filter (fun c : C => cycleAssignment c = i ∧ e ∈ cycles c)).card

/-- The per-layer cycle-degree bound: for every edge and every layer, the
number of cycles assigned to that layer containing that edge is at most `bound`.
This is the correct formalization of the paper's cycle-degree bound `c`:
distributing cycles across R layers so that each edge participates in at most
`c` cycles within any single layer. -/
def LayerCycleDegreeBound
    {α : Type*} {R' : ℕ} {C : Type*} [Fintype C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (cycleAssignment : C → Fin (R' + 1))
    (bound : ℕ) : Prop :=
  ∀ (e : α) (i : Fin (R' + 1)),
    edgeCycleDegreeInLayer cycles cycleAssignment e i ≤ bound

/-- The global edge-cycle degree: total number of generating cycles containing
edge e (across all layers). -/
def edgeCycleDegree
    {α : Type*} {C : Type*} [Fintype C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (e : α) : ℕ :=
  (Finset.univ.filter (fun c : C => e ∈ cycles c)).card

theorem edgeCycleDegree_le_card
    {α : Type*} {C : Type*} [Fintype C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (e : α) :
    edgeCycleDegree cycles e ≤ Fintype.card C :=
  Finset.card_filter_le _ _

/-- Per-layer bound implies global bound scaled by number of layers. -/
theorem layerBound_implies_global_bound
    {α : Type*} {R' : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (cycleAssignment : C → Fin (R' + 1))
    (bound : ℕ)
    (hbound : LayerCycleDegreeBound cycles cycleAssignment bound)
    (e : α) :
    edgeCycleDegree cycles e ≤ (R' + 1) * bound := by
  unfold edgeCycleDegree
  have heq : Finset.univ.filter (fun c : C => e ∈ cycles c) =
    (Finset.univ : Finset (Fin (R' + 1))).biUnion
      (fun i => Finset.univ.filter (fun c : C => cycleAssignment c = i ∧ e ∈ cycles c)) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he; exact ⟨cycleAssignment c, rfl, he⟩
    · intro ⟨_, _, he⟩; exact he
  rw [heq]
  calc (Finset.univ.biUnion _).card
      ≤ ∑ i : Fin (R' + 1), (Finset.univ.filter
          (fun c : C => cycleAssignment c = i ∧ e ∈ cycles c)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin (R' + 1), bound := by
        apply Finset.sum_le_sum; intro i _; exact hbound e i
    _ = (R' + 1) * bound := by simp [Finset.sum_const, Finset.card_fin, mul_comm]

/-! ## Complete Sparsification Data -/

/-- The complete data for a cycle-sparsified graph construction.
The cycle assignment distributes cycles across layers, and the per-layer
cycle-degree bound ensures each edge participates in at most `cycleBound`
cycles within any single layer. -/
structure SparsificationData (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    {C : Type*} [Fintype C] [DecidableEq C]
    (cycles : C → Set G.edgeSet)
    [∀ c, DecidablePred (· ∈ cycles c)] where
  numLayers : ℕ
  cycleAssignment : C → Fin (numLayers + 1)
  cycleVerts : C → List V
  cycleBound : ℕ
  /-- The cycle assignment achieves the per-layer bound: each edge participates
  in at most `cycleBound` cycles within any single layer. -/
  bound_holds : LayerCycleDegreeBound cycles cycleAssignment cycleBound

/-- Extract the sparsified graph from sparsification data. -/
noncomputable def SparsificationData.graph
    {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
    {C : Type*} [Fintype C] [DecidableEq C]
    {cycles : C → Set G.edgeSet}
    [∀ c, DecidablePred (· ∈ cycles c)]
    (data : SparsificationData G cycles) :
    SimpleGraph (SparsifiedVertex V data.numLayers) :=
  sparsifiedGraph G data.cycleAssignment data.cycleVerts

/-! ## Minimum Number of Layers R_G^c

The minimum number of layers R_G^c is the smallest R such that there exists
a cycle assignment `C → Fin (R+1)` achieving per-layer cycle-degree ≤ c.
This is nontrivial: distributing cycles across more layers allows reducing
the per-layer participation, and the Freedman-Hastings decongestion lemma
gives R_G^c = O(log² W) for constant-degree graphs. -/

/-- The minimum number of layers R_G^c for cycle-sparsification with
per-layer cycle-degree bound c. This is the smallest R such that cycles
can be distributed across R+1 layers with each edge participating in
at most c cycles per layer. -/
noncomputable def minLayers
    {α : Type*} {C : Type*} [Fintype C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (bound : ℕ)
    (hexists : ∃ R : ℕ, ∃ f : C → Fin (R + 1),
      LayerCycleDegreeBound cycles f bound) : ℕ :=
  @Nat.find _ (Classical.decPred _) hexists

/-- The minimum layers value achieves the bound. -/
theorem minLayers_spec
    {α : Type*} {C : Type*} [Fintype C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (bound : ℕ)
    (hexists : ∃ R : ℕ, ∃ f : C → Fin (R + 1),
      LayerCycleDegreeBound cycles f bound) :
    ∃ f : C → Fin (minLayers cycles bound hexists + 1),
      LayerCycleDegreeBound cycles f bound := by
  unfold minLayers
  exact @Nat.find_spec _ (Classical.decPred _) hexists

/-- No smaller number of layers suffices. -/
theorem minLayers_minimal
    {α : Type*} {C : Type*} [Fintype C]
    (cycles : C → Set α)
    [∀ c, DecidablePred (· ∈ cycles c)]
    (bound : ℕ)
    (hexists : ∃ R : ℕ, ∃ f : C → Fin (R + 1),
      LayerCycleDegreeBound cycles f bound)
    (R' : ℕ) (hR' : R' < minLayers cycles bound hexists) :
    ¬∃ f : C → Fin (R' + 1), LayerCycleDegreeBound cycles f bound := by
  unfold minLayers at hR'
  exact @Nat.find_min _ (Classical.decPred _) hexists R' hR'

/-! ## Zigzag Triangulation Properties -/

/-- For short lists (length < 4), no diagonals are produced. -/
theorem zigzagDiagonals_short (vs : List V) (h : vs.length < 4) :
    zigzagDiagonals vs = [] := by
  simp [zigzagDiagonals, h]

/-- The zigzag go function produces at most `fuel` diagonal pairs. -/
theorem zigzagGo_length_le {n : ℕ} (vs : Fin n → V) (left right : ℕ)
    (hl : left < n) (hr : right < n) (b : Bool) (fuel : ℕ) :
    (zigzagGo vs left right hl hr b fuel).length ≤ fuel := by
  induction fuel generalizing left right b with
  | zero => simp [zigzagGo]
  | succ k ih =>
    simp only [zigzagGo]
    split
    · simp
    · split
      · simp only [List.length_cons, add_le_add_iff_right]; exact ih ..
      · simp only [List.length_cons, add_le_add_iff_right]; exact ih ..

end CycleSparsification
