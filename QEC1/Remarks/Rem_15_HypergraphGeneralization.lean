import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawOperators

/-!
# Rem_15: Hypergraph Generalization of Gauging Measurement

## Statement
The gauging measurement procedure can be generalized by replacing the graph G with a
**hypergraph** to measure multiple operators simultaneously.

**Setup**: Consider an abelian group of operators describable as the X-type operators that
commute with an auxiliary set of k-local Z-type checks. Using the stabilizer formalism, this
group can be equivalently formulated as the kernel of a sparse linear map over F_2.

**Procedure**: For qubits, this is equivalent to replacing the graph G with a hypergraph.
The generalized gauging procedure performs a code deformation by:
1. Introducing a qubit for each hyperedge
2. Measuring into new Gauss's law checks A_v given by the product of X on a vertex and
   the adjacent hyperedges: A_v = X_v ∏_{e ∋ v, e ∈ hyperedges} X_e

**Application**: This allows measuring any abelian group of commuting logical operators that
can be characterized as the kernel of a sparse parity-check matrix.

## Main Definitions
- `Hypergraph` : A hypergraph with vertices V and hyperedges H
- `Hypergraph.incidenceMatrix` : The incidence matrix over ZMod 2
- `Hypergraph.parityCheckMap` : The parity-check map H_Z : Z₂^V → Z₂^H
- `Hypergraph.gaussLawSupport` : The support of a generalized Gauss law operator A_v
- `Hypergraph.toGraphWithCycles` : A graph is a special case of a hypergraph (with edge size 2)

## Key Properties
- `gaussLaw_commute_hypergraph` : All generalized A_v commute (symplectic inner product = 0)
- `gaussLaw_vertex_support_sum_allOnes` : ∑_v A_v support = all-ones on V (represents L)
- `kernel_is_abelian_group` : The abelian group of operators equals ker(H_Z)
- `ofGraphWithCycles_isGraphLike` : Ordinary graphs embed into hypergraphs
- `kLocal_means_sparse_row` : k-local Z-checks ↔ sparse parity-check matrix
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace QEC1.HypergraphGeneralization

/-! ## Hypergraph Definition

A hypergraph generalizes a graph: each hyperedge connects a set of vertices
(not necessarily just two). -/

/-- A hypergraph on vertices V with hyperedges indexed by H.
    Each hyperedge is a subset of vertices (represented as a Finset V). -/
structure Hypergraph (V : Type*) (H : Type*) [DecidableEq V] [Fintype V] [Fintype H] where
  /-- Each hyperedge maps to its set of incident vertices -/
  incidence : H → Finset V

variable {V H : Type*} [DecidableEq V] [DecidableEq H] [Fintype V] [Fintype H]

namespace Hypergraph

/-! ## Binary Vector Types -/

/-- Binary vectors over vertices: Z₂^V -/
abbrev VectorV (V : Type*) := V → ZMod 2

/-- Binary vectors over hyperedges: Z₂^H -/
abbrev VectorH (H : Type*) := H → ZMod 2

instance : Module (ZMod 2) (VectorV V) := Pi.module V (fun _ => ZMod 2) (ZMod 2)
instance : Module (ZMod 2) (VectorH H) := Pi.module H (fun _ => ZMod 2) (ZMod 2)

/-! ## Incidence Matrix and Parity-Check Map

The incidence matrix M over F_2 has M_{h,v} = 1 iff vertex v ∈ hyperedge h.
The parity-check map is the corresponding linear map Z₂^V → Z₂^H. -/

/-- The incidence matrix entry: 1 if vertex v is in hyperedge h, 0 otherwise -/
def incidenceEntry (HG : Hypergraph V H) (h : H) (v : V) : ZMod 2 :=
  if v ∈ HG.incidence h then 1 else 0

/-- The parity-check map H_Z : Z₂^V → Z₂^H.
    For each hyperedge h, (H_Z(x))_h = ∑_{v ∈ h} x_v (mod 2).
    This is the linear map whose kernel characterizes the abelian group. -/
def parityCheckMap (HG : Hypergraph V H) : VectorV V →ₗ[ZMod 2] VectorH H where
  toFun x h := ∑ v ∈ HG.incidence h, x v
  map_add' x y := by
    ext h
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' c x := by
    ext h
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp]
lemma parityCheckMap_apply (HG : Hypergraph V H) (x : VectorV V) (h : H) :
    HG.parityCheckMap x h = ∑ v ∈ HG.incidence h, x v := rfl

/-! ## Kernel Characterization

The abelian group of X-type operators that commute with all k-local Z-type checks
is exactly the kernel of the parity-check map. -/

/-- The kernel of the parity-check map: vectors x ∈ Z₂^V such that H_Z(x) = 0.
    This characterizes the abelian group of commuting X-type operators. -/
def operatorKernel (HG : Hypergraph V H) : Submodule (ZMod 2) (VectorV V) :=
  LinearMap.ker HG.parityCheckMap

/-- Membership in the kernel: x ∈ ker(H_Z) iff ∑_{v ∈ h} x_v = 0 for all hyperedges h -/
@[simp]
theorem mem_operatorKernel_iff (HG : Hypergraph V H) (x : VectorV V) :
    x ∈ HG.operatorKernel ↔ ∀ h : H, ∑ v ∈ HG.incidence h, x v = 0 := by
  simp only [operatorKernel, LinearMap.mem_ker]
  constructor
  · intro h_eq h
    have := congr_fun h_eq h
    simpa using this
  · intro h_all
    ext h
    simp [h_all h]

/-! ## k-Locality

A Z-type check is k-local if the corresponding hyperedge has at most k vertices. -/

/-- A hyperedge h is k-local if it contains at most k vertices -/
def isKLocal (HG : Hypergraph V H) (k : ℕ) (h : H) : Prop :=
  (HG.incidence h).card ≤ k

/-- The hypergraph is k-local if all hyperedges are k-local -/
def isKLocalHypergraph (HG : Hypergraph V H) (k : ℕ) : Prop :=
  ∀ h : H, HG.isKLocal k h

/-- k-locality means the parity-check map is sparse: each row has at most k nonzero entries -/
theorem kLocal_means_sparse_row (HG : Hypergraph V H) (k : ℕ) (h : H)
    (hk : HG.isKLocal k h) :
    (Finset.univ.filter (fun v => HG.incidenceEntry h v ≠ 0)).card ≤ k := by
  have : Finset.univ.filter (fun v => HG.incidenceEntry h v ≠ 0) =
      Finset.univ.filter (fun v => v ∈ HG.incidence h) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, incidenceEntry]
    constructor
    · intro hne
      by_contra h_not
      simp [h_not] at hne
    · intro hv
      simp [hv]
  rw [this]
  calc (Finset.univ.filter (fun v => v ∈ HG.incidence h)).card
      ≤ (HG.incidence h).card := by
        apply Finset.card_le_card
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hv
    _ ≤ k := hk

/-! ## Generalized Gauss Law Operators

In the hypergraph setting, the Gauss law operator A_v is:
  A_v = X_v ∏_{e ∋ v, e ∈ hyperedges} X_e

The support on vertex qubits: 1 at v, 0 elsewhere
The support on hyperedge qubits: 1 at each hyperedge containing v -/

/-- The set of hyperedges incident to vertex v -/
def incidentHyperedges (HG : Hypergraph V H) (v : V) : Finset H :=
  Finset.univ.filter (fun h => v ∈ HG.incidence h)

/-- The vertex support of the generalized Gauss law operator A_v:
    a binary vector on V with 1 at v, 0 elsewhere (represents X_v) -/
def gaussLawVertexSupport (_HG : Hypergraph V H) (v : V) : VectorV V :=
  Pi.single v 1

/-- The hyperedge support of A_v: 1 at each hyperedge containing v, 0 elsewhere -/
def gaussLawHyperedgeSupport (HG : Hypergraph V H) (v : V) : VectorH H :=
  fun h => if v ∈ HG.incidence h then 1 else 0

@[simp]
lemma gaussLawVertexSupport_same (HG : Hypergraph V H) (v : V) :
    HG.gaussLawVertexSupport v v = 1 := by
  simp [gaussLawVertexSupport]

@[simp]
lemma gaussLawVertexSupport_ne (HG : Hypergraph V H) (v w : V) (h : v ≠ w) :
    HG.gaussLawVertexSupport v w = 0 := by
  simp [gaussLawVertexSupport, h]

@[simp]
lemma gaussLawHyperedgeSupport_mem (HG : Hypergraph V H) (v : V) (h : H)
    (hv : v ∈ HG.incidence h) :
    HG.gaussLawHyperedgeSupport v h = 1 := by
  simp [gaussLawHyperedgeSupport, hv]

@[simp]
lemma gaussLawHyperedgeSupport_not_mem (HG : Hypergraph V H) (v : V) (h : H)
    (hv : v ∉ HG.incidence h) :
    HG.gaussLawHyperedgeSupport v h = 0 := by
  simp [gaussLawHyperedgeSupport, hv]

/-! ## Properties of Generalized Gauss Law Operators -/

/-- All generalized Gauss law operators commute.
    Two Pauli operators P₁, P₂ commute iff the symplectic inner product of their supports
    is 0 (mod 2). Since A_v are purely X-type operators (no Z component), the Z-type
    support of each A_v is empty. Therefore the symplectic overlap is always 0.

    We model this as: the Z-type support of each A_v is the zero vector (trivial),
    so the symplectic inner product ∑_i (X-support₁(i) * Z-support₂(i) + Z-support₁(i) * X-support₂(i))
    is 0 for any pair of A_v operators. -/
def gaussLawZTypeSupport (_HG : Hypergraph V H) (_v : V) : VectorV V := 0

def gaussLawZTypeHyperedgeSupport (_HG : Hypergraph V H) (_v : V) : VectorH H := 0

/-- The symplectic inner product of two Pauli operators on the vertex qubits.
    For X-type support vectors xS₁, xS₂ and Z-type support vectors zS₁, zS₂,
    the symplectic product is ∑_i (xS₁(i) * zS₂(i) + zS₁(i) * xS₂(i)). -/
def symplecticInnerProductV (xS₁ zS₁ xS₂ zS₂ : VectorV V) : ZMod 2 :=
  ∑ i : V, (xS₁ i * zS₂ i + zS₁ i * xS₂ i)

/-- The symplectic inner product on hyperedge qubits. -/
def symplecticInnerProductH (xS₁ zS₁ xS₂ zS₂ : VectorH H) : ZMod 2 :=
  ∑ i : H, (xS₁ i * zS₂ i + zS₁ i * xS₂ i)

/-- All generalized Gauss law operators A_v commute: the symplectic inner product
    of A_v₁ and A_v₂ is 0 on both vertex and hyperedge qubits.
    This is because A_v has trivial (zero) Z-type support. -/
theorem gaussLaw_commute_hypergraph (HG : Hypergraph V H) (v₁ v₂ : V) :
    symplecticInnerProductV (HG.gaussLawVertexSupport v₁) (HG.gaussLawZTypeSupport v₁)
      (HG.gaussLawVertexSupport v₂) (HG.gaussLawZTypeSupport v₂) = 0 ∧
    symplecticInnerProductH (HG.gaussLawHyperedgeSupport v₁) (HG.gaussLawZTypeHyperedgeSupport v₁)
      (HG.gaussLawHyperedgeSupport v₂) (HG.gaussLawZTypeHyperedgeSupport v₂) = 0 := by
  constructor
  · simp [symplecticInnerProductV, gaussLawZTypeSupport]
  · simp [symplecticInnerProductH, gaussLawZTypeHyperedgeSupport]

/-- The sum of all vertex supports is the all-ones vector on V.
    This corresponds to ∏_v A_v having L = ∏_v X_v as its vertex component. -/
theorem gaussLaw_vertex_support_sum_allOnes (HG : Hypergraph V H) :
    ∑ v : V, HG.gaussLawVertexSupport v = fun _ => 1 := by
  ext w
  simp only [Finset.sum_apply, gaussLawVertexSupport]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ w) h

/-- The sum of all hyperedge supports gives the cardinality (mod 2) at each hyperedge,
    because each hyperedge h has |incidence h| vertices contributing.
    In the graph case (each hyperedge has exactly 2 vertices), this is 0 mod 2. -/
theorem gaussLaw_hyperedge_support_sum (HG : Hypergraph V H) (h : H) :
    ∑ v : V, HG.gaussLawHyperedgeSupport v h = (HG.incidence h).card := by
  simp only [gaussLawHyperedgeSupport]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => v ∈ HG.incidence h)]
  have h_in : ∀ v ∈ Finset.univ.filter (fun v => v ∈ HG.incidence h),
      (if v ∈ HG.incidence h then (1 : ZMod 2) else 0) = 1 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp [hv]
  have h_not : ∀ v ∈ Finset.univ.filter (fun v => ¬(v ∈ HG.incidence h)),
      (if v ∈ HG.incidence h then (1 : ZMod 2) else 0) = 0 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp [hv]
  rw [Finset.sum_congr rfl h_in, Finset.sum_congr rfl h_not]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_const_zero, add_zero,
    mul_zero]
  congr 1
  have : Finset.univ.filter (fun v => v ∈ HG.incidence h) = HG.incidence h := by
    ext v; simp
  rw [this]

/-- For the graph case: when every hyperedge has exactly 2 vertices,
    the sum of all hyperedge supports is 0 (mod 2). -/
theorem gaussLaw_product_edge_zero (HG : Hypergraph V H)
    (h_graphlike : ∀ h : H, (HG.incidence h).card = 2) (h : H) :
    ∑ v : V, HG.gaussLawHyperedgeSupport v h = 0 := by
  rw [gaussLaw_hyperedge_support_sum]
  rw [h_graphlike h]
  decide

/-! ## Graphs as Special Case of Hypergraphs

An ordinary graph (where every edge connects exactly 2 vertices) is a hypergraph
where every hyperedge has exactly 2 vertices. -/

/-- A hypergraph is graph-like if every hyperedge has exactly 2 vertices -/
def isGraphLike (HG : Hypergraph V H) : Prop :=
  ∀ h : H, (HG.incidence h).card = 2

/-- Construct a hypergraph from a GraphWithCycles -/
def ofGraphWithCycles {E C : Type*} [DecidableEq E] [DecidableEq C]
    [Fintype E] [Fintype C] (G : _root_.GraphWithCycles V E C) :
    Hypergraph V E where
  incidence := fun e => G.edgeVertices e

/-- A hypergraph derived from a graph is graph-like -/
theorem ofGraphWithCycles_isGraphLike {E C : Type*} [DecidableEq E] [DecidableEq C]
    [Fintype E] [Fintype C] (G : _root_.GraphWithCycles V E C) :
    isGraphLike (ofGraphWithCycles G) := by
  intro e
  simp only [ofGraphWithCycles, isGraphLike, _root_.GraphWithCycles.edgeVertices]
  rw [Finset.card_pair (G.edge_endpoints_ne e)]

/-! ## Parity Check Matrix Sparsity

The parity-check matrix is sparse when the hypergraph is k-local. -/

/-- For a k-local hypergraph, the parity-check matrix has at most k entries per row -/
theorem parityCheck_sparse_rows (HG : Hypergraph V H) (k : ℕ)
    (hk : HG.isKLocalHypergraph k) (h : H) :
    (HG.incidence h).card ≤ k :=
  hk h

/-- The total number of nonzero entries in the incidence matrix is bounded by k * |H| -/
theorem parityCheck_total_entries_bound (HG : Hypergraph V H) (k : ℕ)
    (hk : HG.isKLocalHypergraph k) :
    ∑ h : H, (HG.incidence h).card ≤ k * Fintype.card H := by
  calc ∑ h : H, (HG.incidence h).card
      ≤ ∑ _h : H, k := Finset.sum_le_sum (fun h _ => hk h)
    _ = k * Fintype.card H := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-! ## Application: Measuring Abelian Groups via Kernel

Any abelian group of commuting X-type logical operators that can be characterized as
the kernel of a sparse parity-check matrix can be measured via hypergraph gauging. -/

/-- The kernel of the parity-check map is a submodule (abelian group over F_2) -/
theorem kernel_is_abelian_group (HG : Hypergraph V H) :
    ∃ (S : Submodule (ZMod 2) (VectorV V)),
      (∀ x : VectorV V, x ∈ S ↔ HG.parityCheckMap x = 0) := by
  exact ⟨HG.operatorKernel, fun x => LinearMap.mem_ker⟩

/-- Zero vector is always in the kernel -/
@[simp]
theorem zero_mem_kernel (HG : Hypergraph V H) :
    (0 : VectorV V) ∈ HG.operatorKernel := by
  simp [operatorKernel, LinearMap.mem_ker, map_zero]

/-- The kernel is closed under addition (symmetric difference of supports) -/
theorem kernel_add_closed (HG : Hypergraph V H) (x y : VectorV V)
    (hx : x ∈ HG.operatorKernel) (hy : y ∈ HG.operatorKernel) :
    x + y ∈ HG.operatorKernel := by
  exact (HG.operatorKernel).add_mem hx hy

/-! ## Generalized Gauging Procedure

The generalized gauging procedure introduces one qubit per hyperedge and
measures generalized Gauss law operators A_v = X_v ∏_{e ∋ v} X_e. -/

/-- The number of new qubits introduced = number of hyperedges -/
def newQubitCount (_HG : Hypergraph V H) : ℕ := Fintype.card H

/-- The number of new checks = number of vertices (one A_v per vertex) -/
def newCheckCount (_HG : Hypergraph V H) : ℕ := Fintype.card V

/-- The generalized coboundary map δ : Z₂^V → Z₂^H for the hypergraph.
    For vertex v, δ(v) = indicator vector of hyperedges containing v.
    This is the transpose of the incidence matrix. -/
def hypergraphCoboundary (HG : Hypergraph V H) : VectorV V →ₗ[ZMod 2] VectorH H where
  toFun x h := ∑ v ∈ HG.incidence h, x v
  map_add' x y := by
    ext h
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    ext h
    simp [Finset.mul_sum]

/-- The hypergraph coboundary equals the parity-check map -/
theorem hypergraphCoboundary_eq_parityCheck (HG : Hypergraph V H) :
    HG.hypergraphCoboundary = HG.parityCheckMap := by
  ext x h
  simp [hypergraphCoboundary, parityCheckMap]

/-- The all-ones vector on V represents the logical operator L = ∏_v X_v -/
def allOnesV : VectorV V := fun _ => 1

/-- The logical operator L is in the kernel iff every hyperedge has even cardinality -/
theorem logical_in_kernel_iff (HG : Hypergraph V H) :
    allOnesV ∈ HG.operatorKernel ↔ ∀ h : H, (HG.incidence h).card % 2 = 0 := by
  simp only [mem_operatorKernel_iff, allOnesV]
  constructor
  · intro h_all h
    have := h_all h
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    have hval := congrArg ZMod.val this
    simp only [ZMod.val_natCast, ZMod.val_zero] at hval
    exact hval
  · intro h_all h
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_mod := h_all h
    exact Even.natCast_zmod_two (Nat.even_iff.mpr h_mod)

/-- In the graph case, the logical is always in the kernel (each edge has 2 vertices) -/
theorem graphLike_logical_in_kernel (HG : Hypergraph V H) (h_gl : HG.isGraphLike) :
    allOnesV ∈ HG.operatorKernel := by
  rw [logical_in_kernel_iff]
  intro h
  rw [h_gl h]

end Hypergraph

/-! ## Summary

This formalization captures Remark 15 about the hypergraph generalization of gauging:

**Definitions:**
- `Hypergraph`: A hypergraph with vertices V and hyperedges H, each hyperedge is a set of vertices
- `parityCheckMap`: The sparse linear map H_Z : Z₂^V → Z₂^H whose kernel characterizes
  the abelian group of operators
- `operatorKernel`: The kernel of H_Z, representing the abelian group of commuting operators
- `gaussLawVertexSupport`/`gaussLawHyperedgeSupport`: X-type support vectors for A_v operators
- `gaussLawZTypeSupport`/`gaussLawZTypeHyperedgeSupport`: Z-type support (trivially zero for A_v)
- `symplecticInnerProductV`/`symplecticInnerProductH`: Symplectic inner product for commutativity

**Key Results:**
- `gaussLaw_commute_hypergraph`: A_v operators commute (symplectic inner product = 0)
- `mem_operatorKernel_iff`: x ∈ ker(H_Z) iff ∑_{v ∈ h} x_v = 0 for all hyperedges h
- `kernel_is_abelian_group`: The kernel characterizes commuting operators (x ∈ S ↔ H_Z(x) = 0)
- `gaussLaw_vertex_support_sum_allOnes`: Product of all A_v vertex parts gives L
- `ofGraphWithCycles_isGraphLike`: Ordinary graphs embed as graph-like hypergraphs
- `kLocal_means_sparse_row`: k-local checks correspond to sparse parity-check matrix
- `logical_in_kernel_iff`: L ∈ ker(H_Z) iff all hyperedges have even cardinality
-/

end QEC1.HypergraphGeneralization
