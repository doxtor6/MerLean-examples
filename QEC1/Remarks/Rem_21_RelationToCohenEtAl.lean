import QEC1.Remarks.Rem_20_RelationToShorMeasurement
import QEC1.Remarks.Rem_14_HypergraphGeneralization

/-!
# Relation to Cohen et al. Scheme (Remark 21)

## Statement
The generalized (hypergraph) gauging measurement recovers the Cohen et al. scheme:

**Cohen et al. construction** (from reference [cohen2022low]):
- Restrict Z-type checks to support of an irreducible X logical
- Add $d$ layers of dummy vertices for each qubit in $\mathrm{supp}(L)$
- Connect copies of each vertex via line graphs
- Join vertices in each layer via a copy of the hypergraph

**Gauging interpretation**: This is exactly the generalized gauging measurement applied to the
hypergraph defined by the restricted Z checks, with the specified layering structure.

**Cross et al. modification**: Use fewer than $d$ layers, exploiting expansion in the logical's
Tanner subgraph.

**Product measurement**: The procedures in both references for measuring products of irreducible
logicals are captured by adding edges between the corresponding ancilla graphs.

## Formalization Approach

This is a conceptual remark explaining how the general hypergraph gauging framework (Remark 14)
specializes to recover prior constructions by Cohen et al. and Cross et al.

We formalize the structural parameters and counting formulas:
1. **Cohen construction**: Layered structure with d layers of dummy vertices
2. **Cross et al. optimization**: Reduced layers when expansion is sufficient
3. **Product measurement**: Connection structure for measuring logical products

The conceptual correspondence (that Cohen's construction equals hypergraph gauging with
specific parameters) is documented but not formally proven, as it requires external
definitions from the referenced papers.

## Main Results
- `CohenConstruction`: Structural parameters for Cohen et al. construction
- `vertex_decomposition`: Total vertices = code + dummy vertices
- `reduced_fewer_vertices`: Cross et al. uses fewer vertices
- `reduced_fewer_edges`: Cross et al. uses fewer edges
- `connecting_bounds`: Product measurement connection bounds

## File Structure
1. Cohen Construction Parameters: Layer structure and vertex counts
2. Edge Structure: Line graph and hypergraph edges
3. Cross et al. Optimization: Reduced layers
4. Product Measurement: Multi-logical measurement structure
5. Structural Correspondence: Conceptual connection to hypergraph framework
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Cohen Construction Parameters

The Cohen et al. construction builds a layered structure for fault-tolerant measurement:
- Layer 0: Code qubits in supp(L)
- Layers 1 to d: Dummy qubits for error correction
-/

/-- Structural parameters for the Cohen et al. fault-tolerant measurement construction.
    This captures the layering with d dummy layers for distance-d fault tolerance.

    **Correspondence to Remark 14**: The Cohen construction can be viewed as hypergraph
    gauging where the hypergraph is the restricted Z-checks, replicated across d+1 layers
    and connected by line graphs. -/
structure CohenConstruction where
  /-- Size of the logical support |L| -/
  supportSize : ℕ
  /-- Number of dummy layers (d from the paper, provides distance-d fault tolerance) -/
  numLayers : ℕ
  /-- Number of restricted Z-checks (hyperedges in the restricted hypergraph) -/
  numChecks : ℕ
  /-- Support is non-empty -/
  support_pos : 0 < supportSize
  /-- At least one layer for fault tolerance -/
  layers_pos : 0 < numLayers

namespace CohenConstruction

variable (C : CohenConstruction)

/-! ### Vertex Organization -/

/-- Total number of vertices: |L| × (d + 1)
    This includes the code layer and d dummy layers. -/
def totalVertices : ℕ := C.supportSize * (C.numLayers + 1)

/-- Number of code vertices (layer 0 only) -/
def codeVertices : ℕ := C.supportSize

/-- Number of dummy vertices (layers 1 through d) -/
def dummyVertices : ℕ := C.supportSize * C.numLayers

/-- Total vertices decompose into code + dummy vertices -/
theorem vertex_decomposition :
    C.totalVertices = C.codeVertices + C.dummyVertices := by
  unfold totalVertices codeVertices dummyVertices
  ring

/-- Each layer has exactly |L| vertices -/
def verticesPerLayer : ℕ := C.supportSize

/-- Total number of layers (including code layer) -/
def totalLayerCount : ℕ := C.numLayers + 1

/-- Layer count times vertices per layer gives total -/
theorem layer_vertex_count :
    C.totalLayerCount * C.verticesPerLayer = C.totalVertices := by
  unfold totalLayerCount verticesPerLayer totalVertices
  ring

/-! ### Edge Structure -/

/-- Line graph edges: vertical connections between layers.
    Each qubit in supp(L) has d edges connecting its copies across layers.
    Total = |L| × d -/
def lineGraphEdges : ℕ := C.supportSize * C.numLayers

/-- Hypergraph copy edges: horizontal connections within each layer.
    Each layer contains a copy of the restricted hypergraph.
    Total = (d + 1) × |checks| -/
def hypergraphCopyEdges : ℕ := (C.numLayers + 1) * C.numChecks

/-- Total edges in the construction -/
def totalEdges : ℕ := C.lineGraphEdges + C.hypergraphCopyEdges

/-- Line graph edges equal dummy vertex count -/
theorem lineEdges_eq_dummy : C.lineGraphEdges = C.dummyVertices := rfl

/-- Total vertices is positive -/
theorem totalVertices_pos : 0 < C.totalVertices := by
  unfold totalVertices
  exact Nat.mul_pos C.support_pos (Nat.succ_pos C.numLayers)

/-- Total layers is positive -/
theorem totalLayerCount_pos : 0 < C.totalLayerCount := Nat.succ_pos C.numLayers

/-- Dummy vertices equals line edges (natural correspondence) -/
theorem dummy_eq_lineEdges : C.dummyVertices = C.lineGraphEdges := rfl

/-! ### Fault Tolerance -/

/-- The construction provides distance-d fault tolerance (d = numLayers) -/
def faultDistance : ℕ := C.numLayers

/-- Fault distance is positive -/
theorem faultDistance_pos : 0 < C.faultDistance := C.layers_pos

end CohenConstruction

/-! ## Section 2: Cross et al. Optimization

Cross et al. show that fewer than d layers suffice when the logical's Tanner subgraph
has sufficient expansion. The reduced construction uses the same structure but with
fewer dummy layers. -/

/-- Parameters for the Cross et al. reduced-layer construction.
    Uses expansion properties to achieve fault tolerance with fewer layers. -/
structure CrossConstruction extends CohenConstruction where
  /-- Reduced number of layers (achieves fault tolerance via expansion) -/
  reducedLayers : ℕ
  /-- Reduced layers is strictly less than original d -/
  layer_reduction : reducedLayers < numLayers
  /-- Reduced layers is still positive (provides some fault tolerance) -/
  reduced_pos : 0 < reducedLayers

namespace CrossConstruction

variable (X : CrossConstruction)

/-- Reduced total vertices -/
def reducedVertices : ℕ := X.supportSize * (X.reducedLayers + 1)

/-- Reduced line graph edges -/
def reducedLineEdges : ℕ := X.supportSize * X.reducedLayers

/-- Reduced hypergraph copy edges -/
def reducedHyperedges : ℕ := (X.reducedLayers + 1) * X.numChecks

/-- Reduced total edges -/
def reducedTotalEdges : ℕ := X.reducedLineEdges + X.reducedHyperedges

/-- Vertex savings from the reduction -/
def vertexSavings : ℕ := X.totalVertices - X.reducedVertices

/-- Edge savings from the reduction -/
def edgeSavings : ℕ := X.totalEdges - X.reducedTotalEdges

/-- The reduced construction has strictly fewer vertices -/
theorem reduced_fewer_vertices : X.reducedVertices < X.totalVertices := by
  unfold reducedVertices CohenConstruction.totalVertices
  apply Nat.mul_lt_mul_of_pos_left _ X.support_pos
  exact Nat.succ_lt_succ X.layer_reduction

/-- The reduced construction has strictly fewer edges -/
theorem reduced_fewer_edges : X.reducedTotalEdges < X.totalEdges := by
  unfold reducedTotalEdges CohenConstruction.totalEdges
  unfold reducedLineEdges reducedHyperedges
  unfold CohenConstruction.lineGraphEdges CohenConstruction.hypergraphCopyEdges
  have h1 : X.supportSize * X.reducedLayers < X.supportSize * X.numLayers :=
    Nat.mul_lt_mul_of_pos_left X.layer_reduction X.support_pos
  have h2 : (X.reducedLayers + 1) * X.numChecks ≤ (X.numLayers + 1) * X.numChecks := by
    apply Nat.mul_le_mul_right
    exact Nat.succ_le_succ (Nat.le_of_lt X.layer_reduction)
  omega

/-- Vertex savings formula -/
theorem vertexSavings_formula :
    X.vertexSavings = X.supportSize * (X.numLayers - X.reducedLayers) := by
  unfold vertexSavings reducedVertices CohenConstruction.totalVertices
  have h := Nat.le_of_lt X.layer_reduction
  rw [← Nat.mul_sub]
  congr 1
  omega

/-- The reduced fault distance -/
def reducedFaultDistance : ℕ := X.reducedLayers

/-- Reduced fault distance is less than original -/
theorem reducedFaultDistance_lt : X.reducedFaultDistance < X.faultDistance := X.layer_reduction

/-- Reduced fault distance is still positive -/
theorem reducedFaultDistance_pos : 0 < X.reducedFaultDistance := X.reduced_pos

end CrossConstruction

/-! ## Section 3: Product Measurement

For measuring products of irreducible logicals, connect the corresponding ancilla graphs
with additional edges. This allows simultaneous measurement of multiple logicals. -/

/-- Parameters for measuring a product of multiple logical operators.
    Each logical has its own ancilla graph; they are connected to measure the product. -/
structure ProductMeasurement where
  /-- Number of logicals in the product -/
  numLogicals : ℕ
  /-- Construction parameters for each logical's ancilla graph -/
  constructions : Fin numLogicals → CohenConstruction
  /-- At least 2 logicals for a non-trivial product -/
  product_nontrivial : 2 ≤ numLogicals

namespace ProductMeasurement

variable (P : ProductMeasurement)

/-- Total vertices across all ancilla graphs -/
def totalVertices : ℕ :=
  Finset.sum Finset.univ (fun i => (P.constructions i).totalVertices)

/-- Total edges within individual ancilla graphs (before connection) -/
def internalEdges : ℕ :=
  Finset.sum Finset.univ (fun i => (P.constructions i).totalEdges)

/-- Minimum connecting edges: a spanning tree among the ancilla graphs.
    This is the minimum needed to enable product measurement. -/
def minConnectingEdges : ℕ := P.numLogicals - 1

/-- Maximum connecting edges: complete graph among ancilla graphs -/
def maxConnectingEdges : ℕ := P.numLogicals * (P.numLogicals - 1) / 2

/-- Connecting edges bounds: spanning tree ≤ complete graph -/
theorem connecting_bounds : P.minConnectingEdges ≤ P.maxConnectingEdges := by
  unfold minConnectingEdges maxConnectingEdges
  have h := P.product_nontrivial
  -- For n ≥ 2: n - 1 ≤ n(n-1)/2
  have h2 : 2 * (P.numLogicals - 1) ≤ P.numLogicals * (P.numLogicals - 1) := by
    apply Nat.mul_le_mul_right
    exact h
  omega

/-- Minimum connecting edges is positive (at least 1 edge needed) -/
theorem min_edges_pos : 0 < P.minConnectingEdges := by
  unfold minConnectingEdges
  have h := P.product_nontrivial
  omega

/-- Total edges with minimal connection -/
def totalEdgesMinimal : ℕ := P.internalEdges + P.minConnectingEdges

/-- Total edges with maximal connection -/
def totalEdgesMaximal : ℕ := P.internalEdges + P.maxConnectingEdges

/-- Minimal connection uses fewer edges than maximal -/
theorem minimal_le_maximal : P.totalEdgesMinimal ≤ P.totalEdgesMaximal := by
  unfold totalEdgesMinimal totalEdgesMaximal
  exact Nat.add_le_add_left P.connecting_bounds P.internalEdges

end ProductMeasurement

/-! ## Section 4: Structural Correspondence

The Cohen et al. construction corresponds to the hypergraph gauging framework (Remark 14):
- Cohen's restricted hypergraph = hypergraph H with Z-checks restricted to supp(L)
- Cohen's layering = d + 1 copies of H with line graph connections
- Gauging measurement on this layered hypergraph recovers the Cohen et al. scheme

This correspondence is conceptual: the same measurement outcome can be achieved
by viewing Cohen's construction as an instance of hypergraph gauging.

The Cross et al. modification uses expansion to achieve fault tolerance with fewer layers,
demonstrating that the general framework can capture optimization techniques from the
literature.
-/

/-- Number of hypergraph copies in the Cohen construction equals total layers -/
def hypergraphCopies (C : CohenConstruction) : ℕ := C.totalLayerCount

/-- Line graph connections per qubit equals number of dummy layers -/
def lineConnectionsPerQubit (C : CohenConstruction) : ℕ := C.numLayers

/-- The layered structure has correct copy count -/
theorem hypergraphCopies_eq_layers (C : CohenConstruction) :
    hypergraphCopies C = C.numLayers + 1 := rfl

/-- Each qubit connects through d line edges -/
theorem lineConnections_eq_layers (C : CohenConstruction) :
    lineConnectionsPerQubit C = C.numLayers := rfl

/-! ## Section 5: Summary Properties -/

/-- Vertex count formula -/
theorem cohen_vertex_formula (C : CohenConstruction) :
    C.totalVertices = C.supportSize * (C.numLayers + 1) := rfl

/-- Edge count formula -/
theorem cohen_edge_formula (C : CohenConstruction) :
    C.totalEdges = C.supportSize * C.numLayers + (C.numLayers + 1) * C.numChecks := rfl

/-- Cross reduction saves vertices -/
theorem cross_vertex_savings (X : CrossConstruction) :
    X.reducedVertices < X.totalVertices := X.reduced_fewer_vertices

/-- Cross reduction saves edges -/
theorem cross_edge_savings (X : CrossConstruction) :
    X.reducedTotalEdges < X.totalEdges := X.reduced_fewer_edges

/-- Product measurement needs connections -/
theorem product_needs_connections (P : ProductMeasurement) :
    0 < P.minConnectingEdges := P.min_edges_pos

end QEC
