import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_3_FluxOperators

/-!
# Rem_7: Exactness of Boundary and Coboundary Maps

## Statement
When a generating set of cycles for graph G is chosen, the maps ∂₂ (boundary from cycles to
edges) and ∂ (boundary from edges to vertices) form an exact sequence in the sense that
im(∂₂) = ker(∂). That is, the image of ∂₂ equals the kernel of ∂: an edge-set is the boundary
of some cycle-set if and only if it has zero boundary (i.e., every vertex has even degree in
the edge-set).

Similarly, the coboundary maps δ and δ₂ form an exact sequence: ker(δ₂) = im(δ).

Note that δ has a nontrivial kernel: ker(δ) = {𝟬, 𝟙} where 𝟙 is the all-ones vector
(corresponding to the full vertex set), since every edge has exactly two endpoints.

## Main Results
- `boundary_comp_boundary2_eq_zero` : ∂ ∘ ∂₂ = 0 (chain complex property)
- `coboundary2_comp_coboundary_eq_zero` : δ₂ ∘ δ = 0 (cochain complex property)
- `allOnes_in_ker_coboundary` : 𝟙 ∈ ker(δ) - follows from "every edge has two endpoints"
- `zero_in_ker_coboundary` : 0 ∈ ker(δ)
- `ker_coboundary_nontrivial` : ker(δ) contains both 0 and 𝟙 (nontrivial)
- `ker_coboundary_classification` : ker(δ) = {0, 𝟙} for connected graphs
- `im_coboundary_subset_ker_coboundary2` : im(δ) ⊆ ker(δ₂) (cochain complex property)
- `exactness_coboundary_iff` : Exactness for coboundary (under cut generation assumption)
- `exactness_boundary_iff` : Exactness for boundary (under cycle generation assumption)
- `boundary_zero_iff_even_degree` : Zero boundary ↔ even degree at all vertices

## File Structure
1. Definitions and Basic Properties
2. All-Ones Vector and Nontrivial Kernel (key: "every edge has exactly two endpoints")
3. Chain Complex Property: ∂ ∘ ∂₂ = 0
4. Cochain Complex Property: δ₂ ∘ δ = 0
5. Zero Boundary Characterization
6. Connected Graph Kernel Classification
7. Exactness Properties
-/

open Finset GraphWithCycles

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GraphWithCycles

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]
variable (G : GraphWithCycles V E C)

/-! ## Section 1: Definitions and Basic Properties -/

/-- A cycle property: a set of edges is a valid cycle if every vertex has even degree in it.
    This is the defining property that makes ∂(cycle) = 0. -/
def IsValidCycleEdgeSet (edgeSet : Finset E) : Prop :=
  ∀ v : V, (edgeSet.filter (fun e => G.isIncident e v)).card % 2 = 0

/-- Extended graph with valid cycles. -/
structure GraphWithValidCycles extends GraphWithCycles V E C where
  cycles_valid : ∀ c : C, IsValidCycleEdgeSet toGraphWithCycles (cycles c)

/-- The all-ones vector: 1 at every vertex -/
def allOnesV : VectorV' V := fun _ => 1

/-- The zero vector: 0 at every vertex -/
def zeroV : VectorV' V := fun _ => 0

/-- The degree of vertex v in an edge-vector f: counts edges incident to v (mod 2). -/
def vertexDegreeMod2 (f : VectorE' E) (v : V) : ZMod 2 :=
  ∑ e ∈ G.incidentEdges v, f e

/-- Two vertices are adjacent if they share an edge. -/
def AreAdjacent (v w : V) : Prop :=
  ∃ e : E, ((G.edgeEndpoints e).1 = v ∧ (G.edgeEndpoints e).2 = w) ∨
           ((G.edgeEndpoints e).1 = w ∧ (G.edgeEndpoints e).2 = v)

/-- The graph is connected if any two vertices can be connected by a path. -/
def IsConnected : Prop :=
  ∀ v w : V, Relation.ReflTransGen (G.AreAdjacent) v w

/-! ## Section 2: All-Ones Vector and Nontrivial Kernel

The coboundary map δ has a nontrivial kernel: ker(δ) = {0, 𝟙} where 𝟙 is the all-ones vector.
This is because every edge has exactly two endpoints, so δ(𝟙)(e) = 1 + 1 = 0.
-/

/-- Every edge has exactly two endpoints, which in ZMod 2 means 1 + 1 = 0. -/
theorem two_endpoints_sum_eq_zero : (1 : ZMod 2) + 1 = 0 := by decide

/-- The all-ones vector is in ker(δ): δ(𝟙) = 0.
    This is because every edge has exactly two endpoints. -/
theorem allOnes_in_ker_coboundary : G.coboundaryMap (allOnesV (V := V)) = 0 := by
  ext e
  simp only [coboundaryMap_apply_edge, Pi.zero_apply, allOnesV]
  -- edgeVertices e has exactly 2 elements (the two endpoints)
  -- Sum of 1 over 2 elements in ZMod 2 is 0
  have h_ne : (G.edgeEndpoints e).1 ≠ (G.edgeEndpoints e).2 := G.edge_endpoints_ne e
  have h_mem : G.edgeVertices e = {(G.edgeEndpoints e).1, (G.edgeEndpoints e).2} := rfl
  rw [h_mem]
  rw [Finset.sum_pair h_ne]
  decide

/-- The zero vector is trivially in ker(δ). -/
theorem zero_in_ker_coboundary : G.coboundaryMap (zeroV (V := V)) = 0 := by
  have h : zeroV (V := V) = 0 := rfl
  rw [h]
  exact G.coboundaryMap.map_zero

/-- The kernel of δ is nontrivial: it contains both 0 and 𝟙.
    This formalizes the remark that "δ has a nontrivial kernel".
    Note: This holds for ANY graph - no connectedness required!
    The key insight is that every edge has exactly two endpoints, so 1 + 1 = 0 in ZMod 2. -/
theorem ker_coboundary_nontrivial :
    G.coboundaryMap (zeroV (V := V)) = 0 ∧ G.coboundaryMap (allOnesV (V := V)) = 0 :=
  ⟨zero_in_ker_coboundary G, allOnes_in_ker_coboundary G⟩

/-- The inclusion {0, 𝟙} ⊆ ker(δ) holds for ANY graph.
    The original statement "ker(δ) = {0, 1} since every edge has exactly two endpoints"
    asserts this inclusion - the "two endpoints" argument shows 𝟙 ∈ ker(δ).
    For connected graphs, this is an equality; for disconnected graphs, ker(δ) may be larger. -/
theorem ker_coboundary_contains_zero_and_allOnes (f : VectorV' V) :
    f = 0 ∨ f = allOnesV → G.coboundaryMap f = 0 := by
  intro h
  rcases h with rfl | rfl
  · exact zero_in_ker_coboundary G
  · exact allOnes_in_ker_coboundary G

/-- The all-ones vector is nonzero if there is at least one vertex. -/
theorem allOnesV_ne_zero [Nonempty V] : allOnesV (V := V) ≠ 0 := by
  intro h
  have := congr_fun h (Classical.arbitrary V)
  simp only [allOnesV, Pi.zero_apply, one_ne_zero] at this

/-- For a nonempty graph, ker(δ) contains a nonzero element. -/
theorem ker_coboundary_has_nonzero_element [Nonempty V] :
    ∃ f : VectorV' V, f ≠ 0 ∧ G.coboundaryMap f = 0 :=
  ⟨allOnesV, allOnesV_ne_zero, allOnes_in_ker_coboundary G⟩

/-! ## Section 3: Coboundary Characterization

The coboundary δ(α)(e) = α(v) + α(v') for e = {v, v'}.
This is zero iff both endpoints have the same value.
-/

/-- Coboundary at an edge: δ(f)(e) = f(v) + f(v') where e = {v, v'}. -/
theorem coboundaryMap_at_edge (f : VectorV' V) (e : E) :
    G.coboundaryMap f e = f (G.edgeEndpoints e).1 + f (G.edgeEndpoints e).2 := by
  rw [coboundaryMap_apply_edge]
  have h_ne : (G.edgeEndpoints e).1 ≠ (G.edgeEndpoints e).2 := G.edge_endpoints_ne e
  have h_mem : G.edgeVertices e = {(G.edgeEndpoints e).1, (G.edgeEndpoints e).2} := rfl
  rw [h_mem, Finset.sum_pair h_ne]

/-- In ZMod 2, a + b = 0 iff a = b. -/
theorem ZMod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have : a + b + b = 0 + b := by rw [h]
    simp only [zero_add] at this
    have hbb : b + b = 0 := by fin_cases b <;> decide
    rw [add_assoc, hbb, add_zero] at this
    exact this
  · intro h
    rw [h]
    fin_cases b <;> decide

/-- Coboundary is zero at edge iff both endpoints have same value. -/
theorem coboundaryMap_zero_at_edge_iff (f : VectorV' V) (e : E) :
    G.coboundaryMap f e = 0 ↔ f (G.edgeEndpoints e).1 = f (G.edgeEndpoints e).2 := by
  rw [coboundaryMap_at_edge]
  exact ZMod2_add_eq_zero_iff _ _

/-- For the all-ones vector, coboundary is zero at every edge. -/
theorem coboundaryMap_allOnes_at_edge (e : E) :
    G.coboundaryMap (allOnesV (V := V)) e = 0 := by
  rw [coboundaryMap_at_edge]
  simp only [allOnesV]
  decide

variable {G}

/-! ## Section 4: Chain Complex Property

The key chain complex property: ∂ ∘ ∂₂ = 0.
This means im(∂₂) ⊆ ker(∂): the boundary of any cycle-chain is zero.
-/

/-- If a set of edges forms a valid cycle, then its boundary is zero. -/
theorem boundary_of_valid_cycle_eq_zero (edgeSet : Finset E) (hvalid : IsValidCycleEdgeSet G edgeSet) :
    G.boundaryMap (fun e => if e ∈ edgeSet then 1 else 0) = 0 := by
  ext v
  simp only [boundaryMap_apply_vertex, Pi.zero_apply]
  have h := hvalid v
  -- The sum is the cardinality of edges incident to v in edgeSet (mod 2)
  have h_sum : ∑ e ∈ G.incidentEdges v, (if e ∈ edgeSet then (1 : ZMod 2) else 0) =
      (edgeSet.filter (fun e => G.isIncident e v)).card := by
    -- Sum over incident edges of indicator = card of intersection
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
    congr 1
    -- Show: card of {e ∈ incidentEdges v | e ∈ edgeSet} = card of {e ∈ edgeSet | isIncident e v}
    have h_eq : (G.incidentEdges v).filter (fun e => e ∈ edgeSet) =
        edgeSet.filter (fun e => G.isIncident e v) := by
      ext e
      simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [h_eq]
  rw [h_sum]
  have h_even : Even (edgeSet.filter (fun e => G.isIncident e v)).card := by
    rw [Nat.even_iff]
    exact h
  exact h_even.natCast_zmod_two

variable (G)

/-- The chain complex property: ∂ ∘ ∂₂ = 0.
    This is equivalent to im(∂₂) ⊆ ker(∂). -/
theorem boundary_comp_boundary2_eq_zero
    (hvalid : ∀ c : C, IsValidCycleEdgeSet G (G.cycles c)) :
    G.boundaryMap ∘ₗ G.boundary2Map = 0 := by
  -- Show (∂ ∘ ∂₂)(cycleVec) = 0 for all cycleVec : VectorC' C
  apply LinearMap.ext
  intro cycleVec
  apply funext
  intro w
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  rw [boundaryMap_apply_vertex, boundary2Map_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- ∑ e ∈ incidentEdges w, ∑ c : C, cycleVec c * (if e ∈ cycles c then 1 else 0)
  -- = ∑ c : C, cycleVec c * |{e ∈ cycles c | e incident to w}|
  -- Each cycle has even degree at w, so each term is 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  have hc_valid := hvalid c
  -- Count edges in cycle c incident to w
  have h_sum : ∑ e ∈ G.incidentEdges w, cycleVec c * G.boundary2OfCycle c e =
      cycleVec c * ((G.cycles c).filter (fun e => G.isIncident e w)).card := by
    rw [← Finset.mul_sum]
    congr 1
    have h_eq : (G.incidentEdges w).filter (fun e => e ∈ G.cycles c) =
        (G.cycles c).filter (fun e => G.isIncident e w) := by
      ext e
      simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    -- Sum of indicator function over edges
    have h_card : ∑ e ∈ G.incidentEdges w, G.boundary2OfCycle c e =
        ((G.incidentEdges w).filter (fun e => e ∈ G.cycles c)).card := by
      -- First, expand boundary2OfCycle
      simp only [boundary2OfCycle_apply]
      -- Now have: ∑ e ∈ incidentEdges w, if e ∈ cycles c then 1 else 0
      -- Use sum_filter backwards
      have h_filter_sum : (∑ e ∈ (G.incidentEdges w).filter (fun e => e ∈ G.cycles c), (1 : ZMod 2)) =
          ∑ e ∈ G.incidentEdges w, if e ∈ G.cycles c then (1 : ZMod 2) else 0 := by
        exact Finset.sum_filter (fun e => e ∈ G.cycles c) (fun _ => 1)
      rw [← h_filter_sum]
      rw [Finset.sum_const, Nat.smul_one_eq_cast]
    rw [h_card, h_eq]
  rw [h_sum]
  have h_even : ((G.cycles c).filter (fun e => G.isIncident e w)).card % 2 = 0 := hc_valid w
  have h_even' : Even ((G.cycles c).filter (fun e => G.isIncident e w)).card := by
    rw [Nat.even_iff]; exact h_even
  rw [h_even'.natCast_zmod_two, mul_zero]

/-- The image of ∂₂ is contained in the kernel of ∂. -/
theorem im_boundary2_subset_ker_boundary
    (hvalid : ∀ c : C, IsValidCycleEdgeSet G (G.cycles c))
    (cycleVec : VectorC' C) :
    G.boundaryMap (G.boundary2Map cycleVec) = 0 := by
  have h := boundary_comp_boundary2_eq_zero G hvalid
  have h' : (G.boundaryMap ∘ₗ G.boundary2Map) cycleVec = 0 := by
    simp only [h, LinearMap.zero_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'

/-! ## Section 5: Cochain Complex Property

The cochain complex property: δ₂ ∘ δ = 0.
This means im(δ) ⊆ ker(δ₂).
-/

/-- For a valid cycle, the sum over edges in the cycle of (endpoints match v) has even parity.
    This is because every valid cycle visits each internal vertex an even number of times. -/
theorem cycle_visits_vertex_even {G : GraphWithCycles V E C}
    (c : C) (v : V) (cycles_valid : IsValidCycleEdgeSet G (G.cycles c)) :
    ((G.cycles c).filter (fun e => G.isIncident e v)).card % 2 = 0 :=
  cycles_valid v

/-- The cochain complex property: δ₂ ∘ δ = 0.
    This is equivalent to im(δ) ⊆ ker(δ₂). -/
theorem coboundary2_comp_coboundary_eq_zero
    (hvalid : ∀ c : C, IsValidCycleEdgeSet G (G.cycles c)) :
    G.coboundary2Map ∘ₗ G.coboundaryMap = 0 := by
  apply LinearMap.ext
  intro vertexVec
  apply funext
  intro cycleIdx
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  rw [coboundary2Map_apply_cycle]
  -- We need to show: ∑ e ∈ G.cycles cycleIdx, (coboundaryMap vertexVec)(e) = 0
  -- coboundaryMap vertexVec e = vertexVec(v₁) + vertexVec(v₂) where e = {v₁, v₂}
  -- The sum counts each vertex v with multiplicity = # of edges in cycle incident to v
  -- For a valid cycle, each vertex has even degree, so sum is 0
  have h : ∑ e ∈ G.cycles cycleIdx, G.coboundaryMap vertexVec e =
      ∑ e ∈ G.cycles cycleIdx, (vertexVec (G.edgeEndpoints e).1 + vertexVec (G.edgeEndpoints e).2) := by
    apply Finset.sum_congr rfl
    intro e _
    exact G.coboundaryMap_at_edge vertexVec e
  rw [h]
  rw [Finset.sum_add_distrib]
  -- Use Finset.sum_fiberwise to group edges by endpoint
  -- ∑ e, vertexVec (ep e).1 = ∑ v, (card of edges with first endpoint v) * vertexVec v
  have hrewrite1 : ∑ e ∈ G.cycles cycleIdx, vertexVec (G.edgeEndpoints e).1 =
      ∑ v : V, (((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).1 = v)).card : ZMod 2) * vertexVec v := by
    rw [← Finset.sum_fiberwise (G.cycles cycleIdx) (fun e => (G.edgeEndpoints e).1) (fun e => vertexVec (G.edgeEndpoints e).1)]
    apply Finset.sum_congr rfl
    intro v _
    -- Sum of vertexVec v over all edges with first endpoint v = card * vertexVec v
    have : ∑ e ∈ (G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).1 = v), vertexVec (G.edgeEndpoints e).1 =
           ∑ e ∈ (G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).1 = v), vertexVec v := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Finset.mem_filter] at he
      rw [he.2]
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hrewrite2 : ∑ e ∈ G.cycles cycleIdx, vertexVec (G.edgeEndpoints e).2 =
      ∑ v : V, (((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).2 = v)).card : ZMod 2) * vertexVec v := by
    rw [← Finset.sum_fiberwise (G.cycles cycleIdx) (fun e => (G.edgeEndpoints e).2) (fun e => vertexVec (G.edgeEndpoints e).2)]
    apply Finset.sum_congr rfl
    intro v _
    have : ∑ e ∈ (G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).2 = v), vertexVec (G.edgeEndpoints e).2 =
           ∑ e ∈ (G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).2 = v), vertexVec v := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Finset.mem_filter] at he
      rw [he.2]
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- The sum over first endpoints + sum over second endpoints
  -- counts each vertex v once for each incident edge in the cycle
  have htotal : ∀ v : V,
      ((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).1 = v)).card +
      ((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).2 = v)).card =
      ((G.cycles cycleIdx).filter (fun e => G.isIncident e v)).card := by
    intro v
    have h_disjoint : Disjoint
        ((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).1 = v))
        ((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).2 = v)) := by
      rw [Finset.disjoint_filter]
      intro e _ h1 h2
      have hne := G.edge_endpoints_ne e
      rw [h1] at hne
      exact hne h2.symm
    have h_union : ((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).1 = v)) ∪
        ((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).2 = v)) =
        (G.cycles cycleIdx).filter (fun e => G.isIncident e v) := by
      ext e
      simp only [Finset.mem_union, Finset.mem_filter, isIncident]
      tauto
    rw [← h_union, Finset.card_union_of_disjoint h_disjoint]
  -- For valid cycle, total incident count is even
  have heven : ∀ v : V, Even (((G.cycles cycleIdx).filter (fun e => G.isIncident e v)).card) := by
    intro v
    rw [Nat.even_iff]
    exact hvalid cycleIdx v
  -- Now combine
  rw [hrewrite1, hrewrite2, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro v _
  have heq := htotal v
  have hv_even := heven v
  rw [← heq] at hv_even
  have h_cast : ((((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).1 = v)).card +
      ((G.cycles cycleIdx).filter (fun e => (G.edgeEndpoints e).2 = v)).card : ℕ) : ZMod 2) = 0 :=
    hv_even.natCast_zmod_two
  simp only [Nat.cast_add] at h_cast
  -- Need: card1 * vertexVec v + card2 * vertexVec v = 0
  -- Using h_cast: card1 + card2 = 0
  rw [← add_mul, h_cast, zero_mul]

/-- The image of δ is contained in the kernel of δ₂. -/
theorem im_coboundary_subset_ker_coboundary2
    (hvalid : ∀ c : C, IsValidCycleEdgeSet G (G.cycles c))
    (vertexVec : VectorV' V) :
    G.coboundary2Map (G.coboundaryMap vertexVec) = 0 := by
  have h := coboundary2_comp_coboundary_eq_zero G hvalid
  have h' : (G.coboundary2Map ∘ₗ G.coboundaryMap) vertexVec = 0 := by
    simp only [h, LinearMap.zero_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'

variable {G}

/-! ## Section 6: Zero Boundary Characterization

An edge-set has zero boundary iff every vertex has even degree in the edge-set.
-/

/-- Boundary at vertex equals vertex degree (mod 2). -/
theorem boundaryMap_eq_vertexDegreeMod2 (f : VectorE' E) (v : V) :
    G.boundaryMap f v = G.vertexDegreeMod2 f v := by
  unfold vertexDegreeMod2
  exact G.boundaryMap_apply_vertex f v

/-- Zero boundary is equivalent to all vertex degrees being zero (mod 2). -/
theorem boundary_zero_iff_all_degrees_zero (f : VectorE' E) :
    G.boundaryMap f = 0 ↔ ∀ v : V, G.vertexDegreeMod2 f v = 0 := by
  constructor
  · intro h v
    have := congr_fun h v
    simp only [Pi.zero_apply] at this
    rw [← boundaryMap_eq_vertexDegreeMod2]
    exact this
  · intro h
    ext v
    simp only [Pi.zero_apply]
    rw [boundaryMap_eq_vertexDegreeMod2]
    exact h v

/-- Zero boundary ↔ every vertex has even degree in the edge-set.
    This is the characterization mentioned in the remark. -/
theorem boundary_zero_iff_even_degree (f : VectorE' E) :
    G.boundaryMap f = 0 ↔ ∀ v : V, G.vertexDegreeMod2 f v = 0 :=
  boundary_zero_iff_all_degrees_zero f

/-! ## Section 7: Connected Graph Kernel Classification

For a connected graph, ker(δ) = {0, 𝟙}.
Connectedness means any two vertices can be joined by a path of edges.
-/

/-- If f ∈ ker(δ) and v, w are adjacent, then f(v) = f(w). -/
theorem ker_coboundary_constant_on_adjacent (f : VectorV' V)
    (hf : G.coboundaryMap f = 0) (v w : V) (hadj : G.AreAdjacent v w) :
    f v = f w := by
  obtain ⟨e, h⟩ := hadj
  have he := congr_fun hf e
  simp only [Pi.zero_apply] at he
  rw [G.coboundaryMap_zero_at_edge_iff] at he
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact he
  · rw [← h1, ← h2]; exact he.symm

/-- For a connected graph, if f ∈ ker(δ), then f is constant on all vertices. -/
theorem ker_coboundary_constant_of_connected (f : VectorV' V)
    (hf : G.coboundaryMap f = 0) (hconn : G.IsConnected) :
    ∀ v w : V, f v = f w := by
  intro v w
  have h := hconn v w
  induction h with
  | refl => rfl
  | tail _ hadj ih =>
    have hstep := ker_coboundary_constant_on_adjacent f hf _ _ hadj
    exact ih.trans hstep

/-- In ZMod 2, every element is 0 or 1. -/
theorem ZMod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- For a connected graph, ker(δ) = {0, 𝟙}.
    Every element of ker(δ) is either 0 or the all-ones vector. -/
theorem ker_coboundary_classification (f : VectorV' V)
    (hf : G.coboundaryMap f = 0) (hconn : G.IsConnected) :
    f = 0 ∨ f = allOnesV := by
  by_cases hV : Nonempty V
  · obtain ⟨v₀⟩ := hV
    have hconst := ker_coboundary_constant_of_connected f hf hconn
    have hall : ∀ v, f v = f v₀ := fun v => hconst v v₀
    rcases ZMod2_cases (f v₀) with h0 | h1
    · left
      ext v
      simp [hall v, h0]
    · right
      ext v
      simp [allOnesV, hall v, h1]
  · left
    ext v
    exact absurd ⟨v⟩ hV

/-- Connected graph version: ker(δ) has exactly two elements {0, 𝟙}. -/
theorem ker_coboundary_eq_zero_or_allOnes (f : VectorV' V)
    (hf : G.coboundaryMap f = 0) (hconn : G.IsConnected) :
    f = 0 ∨ f = allOnesV :=
  ker_coboundary_classification f hf hconn

/-- Classification as an iff statement for connected graphs. -/
theorem ker_coboundary_iff (hconn : G.IsConnected) (f : VectorV' V) :
    G.coboundaryMap f = 0 ↔ f = 0 ∨ f = allOnesV := by
  constructor
  · intro hf
    exact ker_coboundary_classification f hf hconn
  · intro h
    rcases h with rfl | rfl
    · exact zero_in_ker_coboundary G
    · exact allOnes_in_ker_coboundary G

/-! ## Section 8: Exactness Properties

Exactness at C₁ means im(∂₂) = ker(∂):
- One direction (im(∂₂) ⊆ ker(∂)) follows from ∂ ∘ ∂₂ = 0 for valid cycles
- The other direction requires that the cycles generate all cycles
-/

variable (G)

/-- The cycles generate all cycles if every edge-chain with zero boundary
    can be written as a sum of cycle boundaries. -/
def CyclesGenerate : Prop :=
  ∀ f : VectorE' E, G.boundaryMap f = 0 →
    ∃ g : VectorC' C, G.boundary2Map g = f

/-- Exactness at C₁: an edge-chain is in im(∂₂) iff it has zero boundary.
    This requires that the cycles generate all cycles AND cycles are valid. -/
theorem exactness_boundary_iff
    (hvalid : ∀ c : C, IsValidCycleEdgeSet G (G.cycles c))
    (hgen : CyclesGenerate G) (f : VectorE' E) :
    (∃ g : VectorC' C, G.boundary2Map g = f) ↔ G.boundaryMap f = 0 := by
  constructor
  · -- im(∂₂) ⊆ ker(∂): follows from valid cycles
    intro ⟨g, hg⟩
    rw [← hg]
    exact im_boundary2_subset_ker_boundary G hvalid g
  · -- ker(∂) ⊆ im(∂₂): this is the generation property
    exact hgen f

/-- The cuts generate all cocycles if every edge-chain in ker(δ₂) is in im(δ).
    This is the dual of CyclesGenerate. -/
def CutsGenerate : Prop :=
  ∀ f : VectorE' E, G.coboundary2Map f = 0 →
    ∃ g : VectorV' V, G.coboundaryMap g = f

/-- Exactness for coboundary maps: an edge-chain is in im(δ) iff it's in ker(δ₂).
    This requires valid cycles (for im(δ) ⊆ ker(δ₂)) and cut generation (for the converse). -/
theorem exactness_coboundary_iff
    (hvalid : ∀ c : C, IsValidCycleEdgeSet G (G.cycles c))
    (hcuts : CutsGenerate G) (f : VectorE' E) :
    (∃ g : VectorV' V, G.coboundaryMap g = f) ↔ G.coboundary2Map f = 0 := by
  constructor
  · -- im(δ) ⊆ ker(δ₂): follows from cochain complex property
    intro ⟨g, hg⟩
    rw [← hg]
    exact im_coboundary_subset_ker_coboundary2 G hvalid g
  · -- ker(δ₂) ⊆ im(δ): this is the cut generation property
    exact hcuts f

/-! ## Section 9: Summary and Simp Lemmas -/

variable {G}

@[simp]
theorem coboundaryMap_allOnesV : G.coboundaryMap (allOnesV (V := V)) = 0 :=
  allOnes_in_ker_coboundary G

@[simp]
theorem coboundaryMap_zeroV : G.coboundaryMap (zeroV (V := V)) = 0 :=
  zero_in_ker_coboundary G

/-- The remark's key assertion: ker(δ) = {0, 𝟙} for connected graphs. -/
theorem ker_coboundary_is_zero_and_allOnes (hconn : G.IsConnected) (f : VectorV' V) :
    G.coboundaryMap f = 0 ↔ (f = 0 ∨ f = allOnesV) :=
  ker_coboundary_iff hconn f

end GraphWithCycles
