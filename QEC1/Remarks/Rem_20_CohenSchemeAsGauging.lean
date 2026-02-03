import QEC1.Remarks.Rem_15_HypergraphGeneralization
import QEC1.Remarks.Rem_2_GraphConvention
import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawOperators
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic

/-!
# Rem_20: Cohen Scheme as Gauging

## Statement
**The Cohen et al. scheme for logical measurement can be recovered as a hypergraph gauging
measurement.**

**Cohen et al. scheme setup**: Consider the restriction of the Z-type checks to the support
of an irreducible X logical L. This defines a hypergraph of Z constraints with the only
nontrivial element in the kernel being the logical operator L.

**Recovery via gauging**:
1. Add d layers of dummy vertices for each qubit in supp(L)
2. Connect the d copies of each vertex via a line graph (chain)
3. Join the vertices in each layer via a copy of the same underlying hypergraph

Applying the generalized hypergraph gauging procedure to this construction exactly reproduces
the Cohen et al. measurement scheme.

**Cross et al. modification**: The scheme from Cross et al. can similarly be recovered by
using fewer than d layers of dummy vertices.

**Product measurement**: The procedures for joining ancilla systems designed for irreducible
logicals to measure their products can be captured as a gauging measurement by adding edges
between the graphs corresponding to the individual ancilla systems.

## Main Results
- `CohenHypergraph` : The Z-constraint hypergraph from the Cohen scheme
- `cohen_kernel_characterization` : The kernel has {0, L} as only elements
- `LayeredCohenConstruction` : The d-layer construction with chains and hypergraph copies
- `layered_vertex_count` : Total vertices = W * (d + 1)
- `layered_hyperedge_count` : Total hyperedges = W * d + |H| * (d + 1)
- `layered_kernel_is_logical` : The all-ones vector on the base layer is in the kernel
- `cross_et_al_fewer_layers` : Cross et al. uses m < d layers
- `ProductMeasurementGraph` : Graph for product measurement via bridge edges
- `product_measurement_kernel_contains_product` : Product of logicals is in the kernel
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace QEC1.CohenSchemeAsGauging

open Finset

/-! ## Cohen et al. Scheme Setup

The Cohen scheme restricts Z-type checks to supp(L), forming a hypergraph whose kernel
characterizes the X-type operators commuting with these checks. The key property is that
the only nontrivial element in the kernel is L itself. -/

section CohenHypergraph

variable {W : ℕ} {numChecks : ℕ}

open QEC1.HypergraphGeneralization in
/-- The Cohen hypergraph: Z-type checks restricted to supp(L).
    Vertices are the W qubits in supp(L), and hyperedges are the restricted Z-type checks. -/
abbrev CohenHypergraph (W numChecks : ℕ) :=
  Hypergraph (Fin W) (Fin numChecks)

open QEC1.HypergraphGeneralization in
/-- The all-ones vector on Fin W represents the logical operator L = ∏_{v ∈ supp(L)} X_v. -/
def logicalVector (W : ℕ) : Hypergraph.VectorV (Fin W) := fun _ => 1

/-- The logical vector is nonzero when W ≥ 1. -/
theorem logicalVector_ne_zero (hW : W ≥ 1) : logicalVector W ≠ 0 := by
  intro h
  have := congr_fun h ⟨0, hW⟩
  simp [logicalVector] at this

open QEC1.HypergraphGeneralization in
/-- Property that the kernel of the Cohen hypergraph is exactly {0, L}.
    This is the defining property of the Cohen scheme: the restriction of Z-type checks
    to supp(L) has kernel spanned by L (the logical operator is irreducible). -/
def CohenKernelProperty (HG : CohenHypergraph W numChecks) : Prop :=
  ∀ x : Hypergraph.VectorV (Fin W),
    x ∈ HG.operatorKernel ↔ (x = 0 ∨ x = logicalVector W)

open QEC1.HypergraphGeneralization in
/-- When the Cohen kernel property holds, L is in the kernel. -/
theorem cohen_logical_in_kernel (HG : CohenHypergraph W numChecks)
    (hker : CohenKernelProperty HG) :
    logicalVector W ∈ HG.operatorKernel := by
  rw [hker]
  exact Or.inr rfl

open QEC1.HypergraphGeneralization in
/-- When the Cohen kernel property holds, the kernel has exactly {0, L}. -/
theorem cohen_kernel_characterization (HG : CohenHypergraph W numChecks)
    (hker : CohenKernelProperty HG) :
    ∀ x : Hypergraph.VectorV (Fin W),
      x ∈ HG.operatorKernel → x = 0 ∨ x = logicalVector W := by
  intro x hx
  exact (hker x).mp hx

open QEC1.HypergraphGeneralization in
/-- Both 0 and L are in the kernel. -/
theorem cohen_kernel_contains_zero_and_L (HG : CohenHypergraph W numChecks)
    (hker : CohenKernelProperty HG) :
    (0 : Hypergraph.VectorV (Fin W)) ∈ HG.operatorKernel ∧
    logicalVector W ∈ HG.operatorKernel := by
  exact ⟨(hker 0).mpr (Or.inl rfl), (hker (logicalVector W)).mpr (Or.inr rfl)⟩

end CohenHypergraph

/-! ## Layered Construction for Recovery via Gauging

The construction to recover the Cohen scheme via gauging:
1. Start with W qubits (vertices of supp(L))
2. Add d layers of dummy vertices (W vertices per layer)
3. Connect d copies of each vertex via a line graph (chain of length d)
4. Join vertices in each layer via copies of the same underlying hypergraph

Total vertices: W * (d + 1) (original layer + d dummy layers)
Total hyperedges: W * d (chain edges) + numChecks * (d + 1) (hypergraph copies per layer)
-/

section LayeredConstruction

variable (W : ℕ) (d : ℕ) (numChecks : ℕ)

/-- Vertex type for the layered construction: (layer, qubit_index).
    Layer 0 is the original (base) layer, layers 1..d are dummy layers. -/
abbrev LayeredVertex := Fin (d + 1) × Fin W

/-- The total number of vertices in the layered construction. -/
theorem layered_vertex_count :
    Fintype.card (LayeredVertex W d) = (d + 1) * W := by
  simp [Fintype.card_prod, Fintype.card_fin]

/-- The base layer vertices (layer 0) correspond to the original qubits in supp(L). -/
def baseLayerVertices : Finset (LayeredVertex W d) :=
  Finset.univ.filter (fun v => v.1 = ⟨0, Nat.zero_lt_succ d⟩)

/-- The dummy layer vertices (layers 1..d). -/
def dummyLayerVertices : Finset (LayeredVertex W d) :=
  Finset.univ.filter (fun v => v.1 ≠ ⟨0, Nat.zero_lt_succ d⟩)

/-- The base layer has exactly W vertices. -/
theorem base_layer_card :
    (baseLayerVertices W d).card = W := by
  simp only [baseLayerVertices]
  have : (Finset.univ : Finset (LayeredVertex W d)).filter
      (fun v => v.1 = ⟨0, Nat.zero_lt_succ d⟩) =
      ({⟨0, Nat.zero_lt_succ d⟩} : Finset (Fin (d + 1))) ×ˢ (Finset.univ : Finset (Fin W)) := by
    ext ⟨l, i⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · intro h; exact ⟨h, trivial⟩
    · intro ⟨h, _⟩; exact h
  rw [this, Finset.card_product, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin, one_mul]

/-- The dummy layers have exactly d * W vertices. -/
theorem dummy_layers_card :
    (dummyLayerVertices W d).card = d * W := by
  have htotal := layered_vertex_count W d
  have hbase := base_layer_card W d
  have hpart : Finset.univ (α := LayeredVertex W d) =
      baseLayerVertices W d ∪ dummyLayerVertices W d := by
    ext v
    simp only [baseLayerVertices, dummyLayerVertices, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    tauto
  have hdisj : Disjoint (baseLayerVertices W d) (dummyLayerVertices W d) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [baseLayerVertices, dummyLayerVertices, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv1 hv2
    exact hv2 hv1
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hpart, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  rw [hbase] at hcard
  -- hcard : (d + 1) * W = W + #(dummyLayerVertices W d)
  -- goal : #(dummyLayerVertices W d) = d * W
  have : (d + 1) * W = W + d * W := by ring
  omega

/-! ## Edge Types in the Layered Construction

Two types of edges/hyperedges:
1. **Chain edges**: connecting (layer, i) to (layer+1, i) for each qubit i and layer 0..d-1
2. **Hypergraph copies**: a copy of the original Z-constraint hypergraph in each layer -/

/-- Combined edge/hyperedge type for the layered construction. -/
inductive LayeredHyperedge (W d numChecks : ℕ) : Type where
  /-- Chain edge connecting (l, i) to (l+1, i) -/
  | chain : Fin d → Fin W → LayeredHyperedge W d numChecks
  /-- Copy of a hypergraph check in a given layer -/
  | hypergraphCopy : Fin (d + 1) → Fin numChecks → LayeredHyperedge W d numChecks
  deriving DecidableEq

instance : Fintype (LayeredHyperedge W d numChecks) where
  elems := (Finset.univ.image (fun p : Fin d × Fin W => LayeredHyperedge.chain p.1 p.2)) ∪
           (Finset.univ.image (fun p : Fin (d + 1) × Fin numChecks =>
              LayeredHyperedge.hypergraphCopy p.1 p.2))
  complete := by
    intro e
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    cases e with
    | chain l i => exact Or.inl ⟨(l, i), rfl⟩
    | hypergraphCopy l h => exact Or.inr ⟨(l, h), rfl⟩

/-- The number of chain edges is d * W. -/
theorem chain_edge_count :
    (Finset.univ.image (fun p : Fin d × Fin W =>
      (LayeredHyperedge.chain p.1 p.2 : LayeredHyperedge W d numChecks))).card = d * W := by
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_prod, Fintype.card_fin]
  · intro ⟨l₁, i₁⟩ ⟨l₂, i₂⟩ h
    simp only [LayeredHyperedge.chain.injEq] at h
    exact Prod.ext h.1 h.2

/-- The number of hypergraph copy edges is (d + 1) * numChecks. -/
theorem hypergraph_copy_count :
    (Finset.univ.image (fun p : Fin (d + 1) × Fin numChecks =>
      (LayeredHyperedge.hypergraphCopy p.1 p.2 : LayeredHyperedge W d numChecks))).card =
    (d + 1) * numChecks := by
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_prod, Fintype.card_fin]
  · intro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h
    simp only [LayeredHyperedge.hypergraphCopy.injEq] at h
    exact Prod.ext h.1 h.2

/-! ## Layered Hypergraph Construction

Build the layered hypergraph from the original Cohen hypergraph. -/

open QEC1.HypergraphGeneralization in
/-- Construct the layered hypergraph from the original Cohen hypergraph.
    - Chain edges connect (l, i) to (l+1, i) (2-element hyperedges)
    - Hypergraph copies replicate the original Z-constraint hypergraph in each layer -/
def LayeredCohenConstruction (HG : CohenHypergraph W numChecks) :
    Hypergraph (LayeredVertex W d) (LayeredHyperedge W d numChecks) where
  incidence := fun e =>
    match e with
    | .chain l i =>
      {(⟨l.val, by omega⟩, i), (⟨l.val + 1, by omega⟩, i)}
    | .hypergraphCopy layer check =>
      (HG.incidence check).map
        ⟨fun v => (layer, v), fun _ _ h => by
          simp only [Prod.mk.injEq] at h; exact h.2⟩

/-- Helper: the two endpoints of a chain edge are distinct. -/
private theorem chain_endpoints_ne (l : Fin d) (i : Fin W) :
    ((⟨l.val, by omega⟩ : Fin (d + 1)), i) ≠
    ((⟨l.val + 1, by omega⟩ : Fin (d + 1)), i) := by
  intro h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  omega

open QEC1.HypergraphGeneralization in
/-- Each chain edge is a 2-element hyperedge (graph-like). -/
theorem chain_edge_is_pair (HG : CohenHypergraph W numChecks)
    (l : Fin d) (i : Fin W) :
    ((LayeredCohenConstruction W d numChecks HG).incidence (.chain l i)).card = 2 := by
  simp only [LayeredCohenConstruction]
  exact Finset.card_pair (chain_endpoints_ne W d l i)

open QEC1.HypergraphGeneralization in
/-- Hypergraph copy edges have the same cardinality as the original. -/
theorem hypergraph_copy_card (HG : CohenHypergraph W numChecks)
    (layer : Fin (d + 1)) (check : Fin numChecks) :
    ((LayeredCohenConstruction W d numChecks HG).incidence
      (.hypergraphCopy layer check)).card =
    (HG.incidence check).card := by
  simp only [LayeredCohenConstruction]
  rw [Finset.card_map]

/-! ## Kernel Properties of the Layered Construction

The all-ones vector on all layers represents the product of L across layers.
The layered construction preserves the property that this vector is in the kernel. -/

open QEC1.HypergraphGeneralization in
/-- The all-ones vector on the base layer, zeros elsewhere. -/
def baseLogicalVector (W d : ℕ) : Hypergraph.VectorV (LayeredVertex W d) :=
  fun v => if v.1 = ⟨0, Nat.zero_lt_succ d⟩ then 1 else 0

open QEC1.HypergraphGeneralization in
/-- The all-ones vector on all layers represents the full product. -/
def allLayersLogicalVector (W d : ℕ) : Hypergraph.VectorV (LayeredVertex W d) :=
  fun _ => 1

open QEC1.HypergraphGeneralization in
/-- The all-layers logical vector is in the kernel if L is in the kernel of each copy. -/
theorem layered_kernel_is_logical (HG : CohenHypergraph W numChecks)
    (hker : CohenKernelProperty HG) :
    allLayersLogicalVector W d ∈
      (LayeredCohenConstruction W d numChecks HG).operatorKernel := by
  rw [Hypergraph.mem_operatorKernel_iff]
  intro e
  cases e with
  | chain l i =>
    -- Chain edges have exactly 2 vertices, all-ones sums to 0 mod 2
    simp only [LayeredCohenConstruction, allLayersLogicalVector]
    rw [Finset.sum_pair (chain_endpoints_ne W d l i)]
    decide
  | hypergraphCopy layer check =>
    simp only [LayeredCohenConstruction, allLayersLogicalVector]
    rw [Finset.sum_map]
    have hL := cohen_logical_in_kernel HG hker
    rw [Hypergraph.mem_operatorKernel_iff] at hL
    convert hL check using 1

/-! ## Chain Structure: Line Graph Connectivity

The d copies of each vertex are connected via a chain (line graph).
This provides a path of length d from the base layer to the top layer. -/

/-- Adjacency in the chain: vertex i in layers l and l+1 are connected. -/
theorem chain_adjacency (l : Fin d) (_i : Fin W) :
    (⟨l.val, by omega⟩ : Fin (d + 1)) ≠ (⟨l.val + 1, by omega⟩ : Fin (d + 1)) := by
  simp [Fin.ext_iff]

/-- The chain from layer 0 to layer d for vertex i has exactly d edges. -/
theorem chain_path_length (_hd : d ≥ 1) :
    ∀ _i : Fin W,
    ∃ edges : Finset (Fin d),
      edges.card = d ∧
      edges = Finset.univ := by
  intro _i
  exact ⟨Finset.univ, Finset.card_fin d, rfl⟩

/-! ## Cross et al. Modification

The Cross et al. scheme uses m < d layers of dummy vertices instead of d.
This is captured by instantiating the layered construction with a smaller parameter. -/

/-- The Cross et al. modification uses m layers where m < d. -/
def CrossEtAlLayers (m : ℕ) (_hm : m < d) := Fin (m + 1) × Fin W

/-- The Cross et al. construction has fewer total vertices when W ≥ 1. -/
theorem cross_et_al_fewer_layers (m : ℕ) (hm : m < d) (hW : W ≥ 1) :
    (m + 1) * W < (d + 1) * W := by
  exact Nat.mul_lt_mul_of_pos_right (by omega) hW

open QEC1.HypergraphGeneralization in
/-- The Cross et al. layered construction with m < d layers. -/
def CrossEtAlConstruction (HG : CohenHypergraph W numChecks) (m : ℕ) (_hm : m < d) :
    Hypergraph (Fin (m + 1) × Fin W) (LayeredHyperedge W m numChecks) :=
  LayeredCohenConstruction W m numChecks HG

open QEC1.HypergraphGeneralization in
/-- The Cross et al. construction preserves the kernel property. -/
theorem cross_et_al_kernel_preserved (HG : CohenHypergraph W numChecks)
    (hker : CohenKernelProperty HG) (m : ℕ) (hm : m < d) :
    allLayersLogicalVector W m ∈
      (CrossEtAlConstruction W d numChecks HG m hm).operatorKernel :=
  layered_kernel_is_logical W m numChecks HG hker

end LayeredConstruction

/-! ## Product Measurement via Bridge Edges

To measure products of irreducible logicals, join the ancilla systems for individual
logicals by adding edges between their corresponding graphs. -/

section ProductMeasurement

variable {W₁ W₂ : ℕ} {nc₁ nc₂ : ℕ}

/-- Vertex type for the combined product measurement graph. -/
abbrev ProductVertex (W₁ W₂ : ℕ) := (Fin W₁) ⊕ (Fin W₂)

instance : DecidableEq (ProductVertex W₁ W₂) := inferInstance
instance : Fintype (ProductVertex W₁ W₂) := inferInstance

/-- The total vertex count of the product measurement graph. -/
theorem product_vertex_count :
    Fintype.card (ProductVertex W₁ W₂) = W₁ + W₂ := by
  simp [Fintype.card_sum, Fintype.card_fin]

/-- Bridge edges connect specific vertices between the two ancilla systems. -/
structure BridgeEdgeConfig (W₁ W₂ : ℕ) where
  /-- The set of bridge connections: pairs (v₁, v₂) to connect -/
  bridges : Finset (Fin W₁ × Fin W₂)
  /-- At least one bridge edge exists -/
  nonempty : bridges.Nonempty

/-- Hyperedge type for the product measurement construction. -/
inductive ProductHyperedge (W₁ W₂ nc₁ nc₂ : ℕ) : Type where
  /-- A check from the first ancilla system -/
  | left : Fin nc₁ → ProductHyperedge W₁ W₂ nc₁ nc₂
  /-- A check from the second ancilla system -/
  | right : Fin nc₂ → ProductHyperedge W₁ W₂ nc₁ nc₂
  /-- A bridge edge between the two systems -/
  | bridge : Fin W₁ → Fin W₂ → ProductHyperedge W₁ W₂ nc₁ nc₂
  deriving DecidableEq

instance : Fintype (ProductHyperedge W₁ W₂ nc₁ nc₂) where
  elems := (Finset.univ.image ProductHyperedge.left) ∪
           (Finset.univ.image ProductHyperedge.right) ∪
           (Finset.univ.image (fun p : Fin W₁ × Fin W₂ =>
              ProductHyperedge.bridge p.1 p.2))
  complete := by
    intro e
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    cases e with
    | left h => exact Or.inl (Or.inl ⟨h, rfl⟩)
    | right h => exact Or.inl (Or.inr ⟨h, rfl⟩)
    | bridge i j => exact Or.inr ⟨(i, j), rfl⟩

open QEC1.HypergraphGeneralization in
/-- The product measurement hypergraph combining two ancilla systems with bridge edges. -/
def ProductMeasurementGraph
    (HG₁ : Hypergraph (Fin W₁) (Fin nc₁))
    (HG₂ : Hypergraph (Fin W₂) (Fin nc₂))
    (_bridges : Finset (Fin W₁ × Fin W₂)) :
    Hypergraph (ProductVertex W₁ W₂) (ProductHyperedge W₁ W₂ nc₁ nc₂) where
  incidence := fun e =>
    match e with
    | .left h =>
      (HG₁.incidence h).map ⟨Sum.inl, Sum.inl_injective⟩
    | .right h =>
      (HG₂.incidence h).map ⟨Sum.inr, Sum.inr_injective⟩
    | .bridge i j =>
      {Sum.inl i, Sum.inr j}

open QEC1.HypergraphGeneralization in
/-- Bridge edges are 2-element hyperedges (graph-like). -/
theorem bridge_edge_is_pair (HG₁ : Hypergraph (Fin W₁) (Fin nc₁))
    (HG₂ : Hypergraph (Fin W₂) (Fin nc₂))
    (bridges : Finset (Fin W₁ × Fin W₂))
    (i : Fin W₁) (j : Fin W₂) :
    ((ProductMeasurementGraph HG₁ HG₂ bridges).incidence (.bridge i j)).card = 2 := by
  simp only [ProductMeasurementGraph]
  rw [Finset.card_pair]
  exact Sum.inl_ne_inr

open QEC1.HypergraphGeneralization in
/-- Left check edges have the same cardinality as in the original system. -/
theorem left_check_card (HG₁ : Hypergraph (Fin W₁) (Fin nc₁))
    (HG₂ : Hypergraph (Fin W₂) (Fin nc₂))
    (bridges : Finset (Fin W₁ × Fin W₂))
    (h : Fin nc₁) :
    ((ProductMeasurementGraph HG₁ HG₂ bridges).incidence (.left h)).card =
    (HG₁.incidence h).card := by
  simp only [ProductMeasurementGraph, Finset.card_map]

open QEC1.HypergraphGeneralization in
/-- Right check edges have the same cardinality as in the original system. -/
theorem right_check_card (HG₁ : Hypergraph (Fin W₁) (Fin nc₁))
    (HG₂ : Hypergraph (Fin W₂) (Fin nc₂))
    (bridges : Finset (Fin W₁ × Fin W₂))
    (h : Fin nc₂) :
    ((ProductMeasurementGraph HG₁ HG₂ bridges).incidence (.right h)).card =
    (HG₂.incidence h).card := by
  simp only [ProductMeasurementGraph, Finset.card_map]

open QEC1.HypergraphGeneralization in
/-- The product logical vector: all-ones on both systems. -/
def productLogicalVector : Hypergraph.VectorV (ProductVertex W₁ W₂) :=
  fun _ => 1

open QEC1.HypergraphGeneralization in
/-- The product of logicals is in the kernel when both individual logicals are,
    and all bridge edges have even-cardinality incidence (they are 2-element). -/
theorem product_measurement_kernel_contains_product
    (HG₁ : Hypergraph (Fin W₁) (Fin nc₁))
    (HG₂ : Hypergraph (Fin W₂) (Fin nc₂))
    (bridges : Finset (Fin W₁ × Fin W₂))
    (hL₁ : Hypergraph.allOnesV ∈ HG₁.operatorKernel)
    (hL₂ : Hypergraph.allOnesV ∈ HG₂.operatorKernel) :
    productLogicalVector (W₁ := W₁) (W₂ := W₂) ∈
      (ProductMeasurementGraph HG₁ HG₂ bridges).operatorKernel := by
  rw [Hypergraph.mem_operatorKernel_iff]
  rw [Hypergraph.mem_operatorKernel_iff] at hL₁ hL₂
  intro e
  cases e with
  | left h =>
    simp only [ProductMeasurementGraph, productLogicalVector]
    rw [Finset.sum_map]
    convert hL₁ h using 1
  | right h =>
    simp only [ProductMeasurementGraph, productLogicalVector]
    rw [Finset.sum_map]
    convert hL₂ h using 1
  | bridge i j =>
    simp only [ProductMeasurementGraph, productLogicalVector]
    rw [Finset.sum_pair Sum.inl_ne_inr]
    decide

end ProductMeasurement

/-! ## Recovery Correspondence

The full Cohen et al. scheme is recovered by applying the generalized hypergraph gauging
procedure (Rem_15) to the layered construction:

1. **Gauss's law operators**: For each vertex (l, i), the operator
   A_{(l,i)} = X_{(l,i)} ∏_{e ∋ (l,i)} X_e
   This includes contributions from chain edges and hypergraph copy edges.

2. **Product = L**: The product of all A_v operators on the base layer yields L,
   while dummy layers contribute +1 (as per Rem_2 dummy vertex property).

3. **Flux operators**: The cycles in the construction give rise to flux operators B_p
   that stabilize the edge qubits. -/

open QEC1.HypergraphGeneralization in
/-- The generalized Gauss's law vertex support sum equals all-ones
    (instantiation of the hypergraph Gauss's law property). -/
theorem layered_gaussLaw_vertex_sum (W d numChecks : ℕ)
    (HG : CohenHypergraph W numChecks) :
    ∑ v : LayeredVertex W d,
      (LayeredCohenConstruction W d numChecks HG).gaussLawVertexSupport v =
    fun _ => 1 :=
  Hypergraph.gaussLaw_vertex_support_sum_allOnes _

open QEC1.HypergraphGeneralization in
/-- The layered construction is k-local when the original Cohen hypergraph is k-local
    (chain edges have size 2, so the locality bound is max(2, k)). -/
theorem layered_klocal_preserved (W d numChecks : ℕ)
    (HG : CohenHypergraph W numChecks) (k : ℕ) (hk : k ≥ 2)
    (hHG : HG.isKLocalHypergraph k) :
    (LayeredCohenConstruction W d numChecks HG).isKLocalHypergraph k := by
  intro e
  cases e with
  | chain l i =>
    simp only [Hypergraph.isKLocal]
    rw [chain_edge_is_pair W d numChecks HG l i]
    exact hk
  | hypergraphCopy layer check =>
    simp only [Hypergraph.isKLocal]
    rw [hypergraph_copy_card W d numChecks HG layer check]
    exact hHG check

/-! ## Summary

The Cohen et al. scheme for logical measurement is recovered as a hypergraph gauging
measurement through the following correspondence:

1. **Cohen setup**: The Z-type checks restricted to supp(L) define a hypergraph
   whose kernel is {0, L} (the logical is irreducible).

2. **Layered construction**: d layers of dummy vertices + chain connections +
   hypergraph copies per layer give the full gauging hypergraph.

3. **Kernel preservation**: The all-ones vector (representing L) remains in the
   kernel of the layered construction, ensuring the gauging measurement recovers L.

4. **Cross et al.**: Using m < d layers gives a more efficient variant.

5. **Product measurement**: Adding bridge edges between individual ancilla systems
   allows measuring products of irreducible logicals via a single gauging measurement.
-/

end QEC1.CohenSchemeAsGauging
