import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

import QEC1.Remarks.Rem_3_BinaryVectorNotation

/-!
# Def_1: Boundary and Coboundary Maps

## Statement
Let $G = (V, E)$ be a graph with a chosen collection $\mathcal{C}$ of cycles. We define the
following $\mathbb{Z}_2$-linear maps using binary vector representations:

**Boundary map $\partial: \mathbb{Z}_2^{|E|} \to \mathbb{Z}_2^{|V|}$**: For a single edge
$e = \{v, v'\}$, define $\partial e = v + v'$ (the binary vector with 1s at positions $v$ and $v'$).
Extend linearly to edge-sets: $\partial(\sum_i e_i) = \sum_i \partial e_i$.
Equivalently, $\partial$ is the incidence matrix of $G$ over $\mathbb{Z}_2$.

**Coboundary map $\delta: \mathbb{Z}_2^{|V|} \to \mathbb{Z}_2^{|E|}$**: Define $\delta = \partial^T$
(transpose of $\partial$). For a single vertex $v$, we have $\delta v = \sum_{e \ni v} e$
(the binary vector of all edges incident to $v$).

**Second boundary map $\partial_2: \mathbb{Z}_2^{|\mathcal{C}|} \to \mathbb{Z}_2^{|E|}$**:
For a single cycle $c$, define $\partial_2 c = \sum_{e \in c} e$ (the binary vector of edges in $c$).
Extend linearly.

**Second coboundary map $\delta_2: \mathbb{Z}_2^{|E|} \to \mathbb{Z}_2^{|\mathcal{C}|}$**:
Define $\delta_2 = \partial_2^T$. For a single edge $e$, we have $\delta_2 e = \sum_{c \ni e} c$
(the binary vector of cycles containing $e$).

## Main Definitions
- `GraphWithCycles` : A simple graph with a chosen collection of cycles
- `boundaryMap` : The boundary map ∂ : Z₂^E → Z₂^V
- `coboundaryMap` : The coboundary map δ : Z₂^V → Z₂^E (transpose of boundary)
- `boundary2Map` : The second boundary map ∂₂ : Z₂^C → Z₂^E
- `coboundary2Map` : The second coboundary map δ₂ : Z₂^E → Z₂^C (transpose of ∂₂)

## Key Properties
- `coboundaryMap_eq_transpose` : δ = ∂ᵀ
- `coboundary2Map_eq_transpose` : δ₂ = ∂₂ᵀ
- `boundaryMap_single_edge` : ∂(e) = v + v' for edge e = {v, v'}
- `coboundaryMap_single_vertex` : δ(v) = sum of incident edges
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ## Graph with Chosen Cycles -/

/-- A simple graph together with a chosen collection of cycles (represented as sets of edges).
    The cycles are indexed by a finite type C. -/
structure GraphWithCycles (V : Type*) (E : Type*) (C : Type*)
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    [Fintype V] [Fintype E] [Fintype C] where
  /-- The underlying simple graph -/
  graph : SimpleGraph V
  /-- Decidable adjacency -/
  decAdj : DecidableRel graph.Adj
  /-- Edges are represented by a type E with a way to get endpoints -/
  edgeEndpoints : E → V × V
  /-- For each edge, the two endpoints are adjacent -/
  edge_adj : ∀ e : E, graph.Adj (edgeEndpoints e).1 (edgeEndpoints e).2
  /-- Edges are symmetric: we don't distinguish (v, v') from (v', v) -/
  edge_symm : ∀ e : E, graph.Adj (edgeEndpoints e).2 (edgeEndpoints e).1
  /-- The cycles, each represented as a set of edges -/
  cycles : C → Finset E

attribute [instance] GraphWithCycles.decAdj

namespace GraphWithCycles

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]
variable (G : GraphWithCycles V E C)

/-! ## Incidence Relation -/

/-- An edge e is incident to vertex v if v is one of its endpoints -/
def isIncident (e : E) (v : V) : Prop :=
  (G.edgeEndpoints e).1 = v ∨ (G.edgeEndpoints e).2 = v

instance decIsIncident : DecidableRel G.isIncident := fun e v =>
  inferInstanceAs (Decidable ((G.edgeEndpoints e).1 = v ∨ (G.edgeEndpoints e).2 = v))

/-- The set of edges incident to a vertex v -/
def incidentEdges (v : V) : Finset E :=
  Finset.univ.filter (fun e => G.isIncident e v)

/-- The set of vertices incident to an edge e (its two endpoints) -/
def edgeVertices (e : E) : Finset V :=
  {(G.edgeEndpoints e).1, (G.edgeEndpoints e).2}

@[simp]
lemma mem_edgeVertices (e : E) (v : V) :
    v ∈ G.edgeVertices e ↔ G.isIncident e v := by
  simp only [edgeVertices, mem_insert, mem_singleton, isIncident]
  tauto

/-- A cycle contains an edge if the edge is in the cycle's edge set -/
def cycleContainsEdge (c : C) (e : E) : Prop := e ∈ G.cycles c

instance decCycleContainsEdge : DecidableRel G.cycleContainsEdge := fun c e =>
  inferInstanceAs (Decidable (e ∈ G.cycles c))

/-- The set of cycles containing a given edge -/
def cyclesContaining (e : E) : Finset C :=
  Finset.univ.filter (fun c => G.cycleContainsEdge c e)

/-! ## Binary Vector Spaces -/

/-- Binary vectors over vertices: Z₂^V -/
abbrev VectorV' (V : Type*) := V → ZMod 2

/-- Binary vectors over edges: Z₂^E -/
abbrev VectorE' (E : Type*) := E → ZMod 2

/-- Binary vectors over cycles: Z₂^C -/
abbrev VectorC' (C : Type*) := C → ZMod 2

instance : Module (ZMod 2) (VectorV' V) := Pi.module V (fun _ => ZMod 2) (ZMod 2)
instance : Module (ZMod 2) (VectorE' E) := Pi.module E (fun _ => ZMod 2) (ZMod 2)
instance : Module (ZMod 2) (VectorC' C) := Pi.module C (fun _ => ZMod 2) (ZMod 2)

/-! ## Standard Basis Vectors -/

/-- Standard basis vector for vertices: 1 at position v, 0 elsewhere -/
def basisV (v : V) : VectorV' V := Pi.single v 1

/-- Standard basis vector for edges: 1 at position e, 0 elsewhere -/
def basisE (e : E) : VectorE' E := Pi.single e 1

/-- Standard basis vector for cycles: 1 at position c, 0 elsewhere -/
def basisC (c : C) : VectorC' C := Pi.single c 1

@[simp]
lemma basisV_apply_same (v : V) : basisV v v = 1 := Pi.single_eq_same v 1

@[simp]
lemma basisV_apply_ne (v w : V) (h : v ≠ w) : basisV v w = 0 := Pi.single_eq_of_ne h.symm 1

@[simp]
lemma basisE_apply_same (e : E) : basisE e e = 1 := Pi.single_eq_same e 1

@[simp]
lemma basisE_apply_ne (e f : E) (h : e ≠ f) : basisE e f = 0 := Pi.single_eq_of_ne h.symm 1

@[simp]
lemma basisC_apply_same (c : C) : basisC c c = 1 := Pi.single_eq_same c 1

@[simp]
lemma basisC_apply_ne (c d : C) (h : c ≠ d) : basisC c d = 0 := Pi.single_eq_of_ne h.symm 1

/-! ## The Boundary Map ∂ : Z₂^E → Z₂^V -/

/-- The boundary of a single edge e = {v, v'} is v + v' (the characteristic vector of {v, v'}) -/
def boundaryOfEdge (e : E) : VectorV' V :=
  let (v, v') := G.edgeEndpoints e
  basisV v + basisV v'

/-- The boundary map ∂ : Z₂^E → Z₂^V
    For edge e = {v, v'}, ∂(e) = v + v'.
    Extended linearly to all edge vectors. -/
def boundaryMap : VectorE' E →ₗ[ZMod 2] VectorV' V where
  toFun f := ∑ e : E, f e • G.boundaryOfEdge e
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    congr 1
    funext e
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Notation for boundary map -/
scoped notation "∂" => boundaryMap

@[simp]
lemma boundaryMap_apply (f : VectorE' E) :
    G.boundaryMap f = ∑ e : E, f e • G.boundaryOfEdge e := rfl

/-- Boundary of basis vector is the boundary of that edge -/
@[simp]
lemma boundaryMap_basisE (e : E) :
    G.boundaryMap (basisE e) = G.boundaryOfEdge e := by
  simp only [boundaryMap_apply]
  rw [Finset.sum_eq_single e]
  · simp only [basisE, Pi.single_eq_same, one_smul]
  · intro f _ hne
    simp only [basisE]
    rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- Endpoints of an edge are distinct (since SimpleGraph has no self-loops) -/
lemma edge_endpoints_ne (e : E) : (G.edgeEndpoints e).1 ≠ (G.edgeEndpoints e).2 :=
  G.graph.ne_of_adj (G.edge_adj e)

/-- The boundary of an edge has 1s exactly at its endpoints -/
lemma boundaryOfEdge_apply (e : E) (v : V) :
    G.boundaryOfEdge e v = if G.isIncident e v then 1 else 0 := by
  simp only [boundaryOfEdge, basisV, Pi.add_apply]
  by_cases h1 : (G.edgeEndpoints e).1 = v
  · subst h1
    simp only [Pi.single_eq_same, isIncident, true_or, ↓reduceIte]
    rw [Pi.single_eq_of_ne (G.edge_endpoints_ne e) 1, add_zero]
  · by_cases h2 : (G.edgeEndpoints e).2 = v
    · subst h2
      rw [Pi.single_eq_of_ne (Ne.symm h1) 1, zero_add, Pi.single_eq_same]
      simp only [isIncident, h1, false_or, ↓reduceIte]
    · rw [Pi.single_eq_of_ne (Ne.symm h1) 1, Pi.single_eq_of_ne (Ne.symm h2) 1, add_zero]
      simp only [isIncident, h1, h2, or_self, ↓reduceIte]

/-- Alternative characterization: boundary counts (mod 2) how many times v appears as endpoint -/
lemma boundaryMap_apply_vertex (f : VectorE' E) (v : V) :
    G.boundaryMap f v = ∑ e ∈ G.incidentEdges v, f e := by
  simp only [boundaryMap_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => G.isIncident e v)]
  have h_incident : Finset.univ.filter (fun e => G.isIncident e v) = G.incidentEdges v := by
    ext e
    simp [incidentEdges]
  rw [h_incident]
  have h_not_incident : ∀ e ∈ Finset.univ.filter (fun e => ¬G.isIncident e v),
      f e * G.boundaryOfEdge e v = 0 := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [boundaryOfEdge_apply, if_neg he, mul_zero]
  rw [Finset.sum_eq_zero h_not_incident, add_zero]
  apply Finset.sum_congr rfl
  intro e he
  simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [boundaryOfEdge_apply, if_pos he, mul_one]

/-! ## The Coboundary Map δ : Z₂^V → Z₂^E -/

/-- The coboundary of a single vertex v is the sum of all incident edges -/
def coboundaryOfVertex (v : V) : VectorE' E :=
  fun e => if G.isIncident e v then 1 else 0

/-- The coboundary map δ : Z₂^V → Z₂^E
    For vertex v, δ(v) = sum of all edges incident to v.
    This is the transpose of the boundary map. -/
def coboundaryMap : VectorV' V →ₗ[ZMod 2] VectorE' E where
  toFun f := ∑ v : V, f v • G.coboundaryOfVertex v
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    congr 1
    funext v
    funext e
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Notation for coboundary map -/
scoped notation "δ" => coboundaryMap

@[simp]
lemma coboundaryMap_apply (f : VectorV' V) :
    G.coboundaryMap f = ∑ v : V, f v • G.coboundaryOfVertex v := rfl

/-- Coboundary of basis vector is the coboundary of that vertex -/
@[simp]
lemma coboundaryMap_basisV (v : V) :
    G.coboundaryMap (basisV v) = G.coboundaryOfVertex v := by
  simp only [coboundaryMap_apply]
  rw [Finset.sum_eq_single v]
  · simp only [basisV, Pi.single_eq_same, one_smul]
  · intro w _ hne
    simp only [basisV]
    rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- The coboundary map on a vertex gives the characteristic vector of incident edges -/
lemma coboundaryOfVertex_apply (v : V) (e : E) :
    G.coboundaryOfVertex v e = if G.isIncident e v then 1 else 0 := rfl

/-- Coboundary map applied to a vertex vector at an edge e -/
lemma coboundaryMap_apply_edge (f : VectorV' V) (e : E) :
    G.coboundaryMap f e = ∑ v ∈ G.edgeVertices e, f v := by
  simp only [coboundaryMap_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => G.isIncident e v)]
  have h_incident : Finset.univ.filter (fun v => G.isIncident e v) = G.edgeVertices e := by
    ext v
    simp only [edgeVertices, isIncident, mem_insert, mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  rw [h_incident]
  have h_not_incident : ∀ v ∈ Finset.univ.filter (fun v => ¬G.isIncident e v),
      f v * G.coboundaryOfVertex v e = 0 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [coboundaryOfVertex_apply, if_neg hv, mul_zero]
  rw [Finset.sum_eq_zero h_not_incident, add_zero]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' : G.isIncident e v := by rwa [mem_edgeVertices] at hv
  rw [coboundaryOfVertex_apply, if_pos hv', mul_one]

/-! ## Transpose Relationship: δ = ∂ᵀ -/

/-- Key property: The coboundary is the transpose of the boundary.
    This means ⟨∂f, g⟩ = ⟨f, δg⟩ for the natural pairing. -/
theorem coboundary_eq_boundary_transpose (f : VectorE' E) (g : VectorV' V) :
    ∑ v : V, G.boundaryMap f v * g v = ∑ e : E, f e * G.coboundaryMap g e := by
  calc ∑ v : V, G.boundaryMap f v * g v
      = ∑ v : V, (∑ e ∈ G.incidentEdges v, f e) * g v := by
        congr 1; ext v; rw [boundaryMap_apply_vertex]
    _ = ∑ v : V, ∑ e ∈ G.incidentEdges v, f e * g v := by
        congr 1; ext v; rw [Finset.sum_mul]
    _ = ∑ e : E, ∑ v ∈ G.edgeVertices e, f e * g v := by
        rw [Finset.sum_comm']
        intro e v
        simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and, mem_edgeVertices]
        exact Iff.intro (fun h => ⟨h, trivial⟩) (fun h => h.1)
    _ = ∑ e : E, f e * ∑ v ∈ G.edgeVertices e, g v := by
        congr 1; ext e; rw [Finset.mul_sum]
    _ = ∑ e : E, f e * G.coboundaryMap g e := by
        congr 1; ext e; rw [coboundaryMap_apply_edge]

/-! ## The Second Boundary Map ∂₂ : Z₂^C → Z₂^E -/

/-- The boundary of a single cycle c is the sum of its edges -/
def boundary2OfCycle (c : C) : VectorE' E :=
  fun e => if e ∈ G.cycles c then 1 else 0

/-- The second boundary map ∂₂ : Z₂^C → Z₂^E
    For cycle c, ∂₂(c) = sum of all edges in c. -/
def boundary2Map : VectorC' C →ₗ[ZMod 2] VectorE' E where
  toFun f := ∑ c : C, f c • G.boundary2OfCycle c
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    congr 1
    funext c
    funext e
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Notation for second boundary map -/
scoped notation "∂₂" => boundary2Map

@[simp]
lemma boundary2Map_apply (f : VectorC' C) :
    G.boundary2Map f = ∑ c : C, f c • G.boundary2OfCycle c := rfl

/-- Second boundary of basis vector is the boundary of that cycle -/
@[simp]
lemma boundary2Map_basisC (c : C) :
    G.boundary2Map (basisC c) = G.boundary2OfCycle c := by
  simp only [boundary2Map_apply]
  rw [Finset.sum_eq_single c]
  · simp only [basisC, Pi.single_eq_same, one_smul]
  · intro d _ hne
    simp only [basisC]
    rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The boundary of a cycle has 1s exactly at edges in the cycle -/
lemma boundary2OfCycle_apply (c : C) (e : E) :
    G.boundary2OfCycle c e = if e ∈ G.cycles c then 1 else 0 := rfl

/-- Second boundary map applied to edge e -/
lemma boundary2Map_apply_edge (f : VectorC' C) (e : E) :
    G.boundary2Map f e = ∑ c ∈ G.cyclesContaining e, f c := by
  simp only [boundary2Map_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => G.cycleContainsEdge c e)]
  have h_containing : Finset.univ.filter (fun c => G.cycleContainsEdge c e) = G.cyclesContaining e := by
    ext c
    simp [cyclesContaining, cycleContainsEdge]
  rw [h_containing]
  have h_not_containing : ∀ c ∈ Finset.univ.filter (fun c => ¬G.cycleContainsEdge c e),
      f c * G.boundary2OfCycle c e = 0 := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cycleContainsEdge] at hc
    rw [boundary2OfCycle_apply, if_neg hc, mul_zero]
  rw [Finset.sum_eq_zero h_not_containing, add_zero]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [cyclesContaining, Finset.mem_filter, Finset.mem_univ, true_and, cycleContainsEdge] at hc
  rw [boundary2OfCycle_apply, if_pos hc, mul_one]

/-! ## The Second Coboundary Map δ₂ : Z₂^E → Z₂^C -/

/-- The coboundary of a single edge e is the sum of all cycles containing e -/
def coboundary2OfEdge (e : E) : VectorC' C :=
  fun c => if e ∈ G.cycles c then 1 else 0

/-- The second coboundary map δ₂ : Z₂^E → Z₂^C
    For edge e, δ₂(e) = sum of all cycles containing e.
    This is the transpose of the second boundary map. -/
def coboundary2Map : VectorE' E →ₗ[ZMod 2] VectorC' C where
  toFun f := ∑ e : E, f e • G.coboundary2OfEdge e
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    congr 1
    funext e
    funext c
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Notation for second coboundary map -/
scoped notation "δ₂" => coboundary2Map

@[simp]
lemma coboundary2Map_apply (f : VectorE' E) :
    G.coboundary2Map f = ∑ e : E, f e • G.coboundary2OfEdge e := rfl

/-- Second coboundary of basis vector is the coboundary of that edge -/
@[simp]
lemma coboundary2Map_basisE (e : E) :
    G.coboundary2Map (basisE e) = G.coboundary2OfEdge e := by
  simp only [coboundary2Map_apply]
  rw [Finset.sum_eq_single e]
  · simp only [basisE, Pi.single_eq_same, one_smul]
  · intro f _ hne
    simp only [basisE]
    rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- The coboundary of an edge has 1s exactly at cycles containing it -/
lemma coboundary2OfEdge_apply (e : E) (c : C) :
    G.coboundary2OfEdge e c = if e ∈ G.cycles c then 1 else 0 := rfl

/-- Second coboundary map applied to cycle c -/
lemma coboundary2Map_apply_cycle (f : VectorE' E) (c : C) :
    G.coboundary2Map f c = ∑ e ∈ G.cycles c, f e := by
  simp only [coboundary2Map_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => e ∈ G.cycles c)]
  have h_in_cycle : Finset.univ.filter (fun e => e ∈ G.cycles c) = G.cycles c := by
    ext e
    simp
  rw [h_in_cycle]
  have h_not_in_cycle : ∀ e ∈ Finset.univ.filter (fun e => e ∉ G.cycles c),
      f e * G.coboundary2OfEdge e c = 0 := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [coboundary2OfEdge_apply, if_neg he, mul_zero]
  rw [Finset.sum_eq_zero h_not_in_cycle, add_zero]
  apply Finset.sum_congr rfl
  intro e he
  rw [coboundary2OfEdge_apply, if_pos he, mul_one]

/-! ## Transpose Relationship: δ₂ = ∂₂ᵀ -/

/-- Key property: The second coboundary is the transpose of the second boundary.
    This means ⟨∂₂f, g⟩ = ⟨f, δ₂g⟩ for the natural pairing. -/
theorem coboundary2_eq_boundary2_transpose (f : VectorC' C) (g : VectorE' E) :
    ∑ e : E, G.boundary2Map f e * g e = ∑ c : C, f c * G.coboundary2Map g c := by
  calc ∑ e : E, G.boundary2Map f e * g e
      = ∑ e : E, (∑ c ∈ G.cyclesContaining e, f c) * g e := by
        congr 1; ext e; rw [boundary2Map_apply_edge]
    _ = ∑ e : E, ∑ c ∈ G.cyclesContaining e, f c * g e := by
        congr 1; ext e; rw [Finset.sum_mul]
    _ = ∑ c : C, ∑ e ∈ G.cycles c, f c * g e := by
        rw [Finset.sum_comm']
        intro c e
        simp only [cyclesContaining, Finset.mem_filter, Finset.mem_univ, true_and, cycleContainsEdge]
        tauto
    _ = ∑ c : C, f c * ∑ e ∈ G.cycles c, g e := by
        congr 1; ext c; rw [Finset.mul_sum]
    _ = ∑ c : C, f c * G.coboundary2Map g c := by
        congr 1; ext c; rw [coboundary2Map_apply_cycle]

end GraphWithCycles

/-! ## Special Case Properties -/

namespace GraphWithCycles

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]
variable (G : GraphWithCycles V E C)

/-! ### Zero and Linearity Properties -/

@[simp]
lemma boundaryMap_zero : G.boundaryMap 0 = 0 := G.boundaryMap.map_zero

@[simp]
lemma coboundaryMap_zero : G.coboundaryMap 0 = 0 := G.coboundaryMap.map_zero

@[simp]
lemma boundary2Map_zero : G.boundary2Map 0 = 0 := G.boundary2Map.map_zero

@[simp]
lemma coboundary2Map_zero : G.coboundary2Map 0 = 0 := G.coboundary2Map.map_zero

lemma boundaryMap_add (f g : VectorE' E) :
    G.boundaryMap (f + g) = G.boundaryMap f + G.boundaryMap g := G.boundaryMap.map_add f g

lemma coboundaryMap_add (f g : VectorV' V) :
    G.coboundaryMap (f + g) = G.coboundaryMap f + G.coboundaryMap g := G.coboundaryMap.map_add f g

lemma boundary2Map_add (f g : VectorC' C) :
    G.boundary2Map (f + g) = G.boundary2Map f + G.boundary2Map g := G.boundary2Map.map_add f g

lemma coboundary2Map_add (f g : VectorE' E) :
    G.coboundary2Map (f + g) = G.coboundary2Map f + G.coboundary2Map g := G.coboundary2Map.map_add f g

/-! ### Incidence Matrix Interpretation -/

/-- The boundary map can be viewed as multiplication by the incidence matrix.
    The (v, e) entry is 1 if v is incident to e, 0 otherwise. -/
def incidenceMatrix : V → E → ZMod 2 :=
  fun v e => if G.isIncident e v then 1 else 0

/-- The incidence matrix entry equals the boundary of edge evaluated at vertex -/
lemma incidenceMatrix_eq_boundaryOfEdge (v : V) (e : E) :
    G.incidenceMatrix v e = G.boundaryOfEdge e v := by
  simp only [incidenceMatrix, boundaryOfEdge_apply]

/-- Boundary map is multiplication by incidence matrix -/
theorem boundaryMap_eq_incidenceMatrix_mul (f : VectorE' E) (v : V) :
    G.boundaryMap f v = ∑ e : E, G.incidenceMatrix v e * f e := by
  rw [boundaryMap_apply_vertex]
  simp only [incidentEdges, incidenceMatrix, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => G.isIncident e v)]
  have h1 : ∑ e ∈ Finset.univ.filter (fun e => G.isIncident e v), (if G.isIncident e v then 1 else 0) * f e
         = ∑ e ∈ Finset.univ.filter (fun e => G.isIncident e v), f e := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp [he]
  have h2 : ∑ e ∈ Finset.univ.filter (fun e => ¬G.isIncident e v), (if G.isIncident e v then 1 else 0) * f e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp [he]
  rw [h1, h2, add_zero]

/-- Coboundary map is multiplication by transpose of incidence matrix -/
theorem coboundaryMap_eq_incidenceMatrixT_mul (f : VectorV' V) (e : E) :
    G.coboundaryMap f e = ∑ v : V, G.incidenceMatrix v e * f v := by
  rw [coboundaryMap_apply_edge]
  simp only [incidenceMatrix]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => G.isIncident e v)]
  have h_filter : Finset.univ.filter (fun v => G.isIncident e v) = G.edgeVertices e := by
    ext v
    simp only [edgeVertices, isIncident, mem_insert, mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  rw [h_filter]
  have h1 : ∑ v ∈ G.edgeVertices e, (if G.isIncident e v then 1 else 0) * f v
          = ∑ v ∈ G.edgeVertices e, f v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [mem_edgeVertices] at hv
    simp [hv]
  have h2 : ∑ v ∈ Finset.univ.filter (fun v => ¬G.isIncident e v), (if G.isIncident e v then 1 else 0) * f v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp [hv]
  rw [h1, h2, add_zero]

/-! ### Cycle Matrix Interpretation -/

/-- The cycle-edge incidence matrix: (c, e) entry is 1 if edge e is in cycle c -/
def cycleEdgeMatrix : C → E → ZMod 2 :=
  fun c e => if e ∈ G.cycles c then 1 else 0

/-- Second boundary map is multiplication by cycle-edge matrix -/
theorem boundary2Map_eq_cycleMatrix_mul (f : VectorC' C) (e : E) :
    G.boundary2Map f e = ∑ c : C, G.cycleEdgeMatrix c e * f c := by
  rw [boundary2Map_apply_edge]
  simp only [cycleEdgeMatrix, cyclesContaining, Finset.mem_filter, Finset.mem_univ, true_and, cycleContainsEdge]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => e ∈ G.cycles c)]
  have h1 : ∑ c ∈ Finset.univ.filter (fun c => e ∈ G.cycles c), (if e ∈ G.cycles c then 1 else 0) * f c
          = ∑ c ∈ Finset.univ.filter (fun c => e ∈ G.cycles c), f c := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp [hc]
  have h2 : ∑ c ∈ Finset.univ.filter (fun c => e ∉ G.cycles c), (if e ∈ G.cycles c then 1 else 0) * f c = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp [hc]
  rw [h1, h2, add_zero]

/-- Second coboundary map is multiplication by transpose of cycle-edge matrix -/
theorem coboundary2Map_eq_cycleMatrixT_mul (f : VectorE' E) (c : C) :
    G.coboundary2Map f c = ∑ e : E, G.cycleEdgeMatrix c e * f e := by
  rw [coboundary2Map_apply_cycle]
  simp only [cycleEdgeMatrix]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => e ∈ G.cycles c)]
  have h_filter : Finset.univ.filter (fun e => e ∈ G.cycles c) = G.cycles c := by
    ext e; simp
  rw [h_filter]
  have h1 : ∑ e ∈ G.cycles c, (if e ∈ G.cycles c then 1 else 0) * f e
          = ∑ e ∈ G.cycles c, f e := by
    apply Finset.sum_congr rfl
    intro e he
    simp [he]
  have h2 : ∑ e ∈ Finset.univ.filter (fun e => e ∉ G.cycles c), (if e ∈ G.cycles c then 1 else 0) * f e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp [he]
  rw [h1, h2, add_zero]

end GraphWithCycles

/-! ## Summary

This formalization defines the boundary and coboundary maps for a graph with chosen cycles:

1. **Boundary map ∂ : Z₂^E → Z₂^V**
   - For edge e = {v, v'}: ∂(e) = v + v' (sum in Z₂)
   - Equivalently: the v-th component of ∂(f) counts (mod 2) edges in f incident to v

2. **Coboundary map δ : Z₂^V → Z₂^E**
   - For vertex v: δ(v) = sum of all edges incident to v
   - This is the transpose of ∂ : ⟨∂f, g⟩ = ⟨f, δg⟩

3. **Second boundary map ∂₂ : Z₂^C → Z₂^E**
   - For cycle c: ∂₂(c) = sum of all edges in c
   - Equivalently: the e-th component counts (mod 2) cycles in f containing e

4. **Second coboundary map δ₂ : Z₂^E → Z₂^C**
   - For edge e: δ₂(e) = sum of all cycles containing e
   - This is the transpose of ∂₂ : ⟨∂₂f, g⟩ = ⟨f, δ₂g⟩

Key properties proven:
- All maps are Z₂-linear
- Transpose relationships verified via bilinear pairing identity
- Maps can be expressed as matrix multiplication by incidence/cycle matrices
-/
