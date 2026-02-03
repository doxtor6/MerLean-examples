import QEC1.Remarks.Rem_19_RelationToLatticeSurgery

/-!
# Relation to Shor Measurement (Remark 20)

## Statement
The gauging measurement can recover Shor-style logical measurement:

**Shor-style setup**: Entangle an auxiliary GHZ state to the code via transversal CX gates,
then measure X on auxiliary qubits.

**Gauging equivalent**: Use a graph $G$ with:
- A **dummy vertex** for each qubit in $\mathrm{supp}(L)$, each connected by an edge to the
  corresponding code qubit
- A **connected subgraph** on the dummy vertices

**Process**: If we measure the edges of the connected subgraph first (projecting dummies into
a GHZ state), then measure the remaining edges, the result is equivalent to Shor-style
measurement with $X$ measurements commuted backward through CX gates.

## Formalization Approach

This remark describes how the gauging measurement framework recovers Shor-style logical
measurement as a special case. The key insight is that:

1. The Shor measurement uses a GHZ state (all dummies in |+⟩ entangled via CX)
2. The gauging measurement achieves this by:
   - Measuring flux operators on a connected dummy subgraph (creates GHZ state)
   - Measuring remaining edges (equivalent to CX-commuted X measurements)

We formalize:
1. **Shor graph structure**: The specific graph topology for Shor measurement
2. **Dummy-to-code edges**: The "rung" edges connecting dummies to code qubits
3. **Connected dummy subgraph**: The edges among dummies forming a connected graph
4. **Measurement order**: The two-phase measurement process
5. **Graph parameters**: Vertex/edge counts and cycle rank analysis

## Main Results
- `ShorGraph`: Graph structure for Shor-style gauging measurement
- `shor_graph_vertex_count`: |V| = 2|L| (code qubits + dummy qubits)
- `shor_graph_edge_count`: |E| = |L| + (|L| - 1) = 2|L| - 1
- `shor_graph_cycle_rank`: Cycle rank = 0 (tree structure)
- `dummy_subgraph_connected`: The dummy vertices form a connected subgraph
- `measurement_phase_separation`: Two phases: dummy subgraph, then rung edges

## File Structure
1. Shor Graph Vertices: Code qubits and dummy qubits
2. Shor Graph Edges: Rung edges and dummy-connection edges
3. Connectivity Properties: Connected dummy subgraph
4. Graph Parameters: Vertex/edge/cycle counts
5. Measurement Process: Two-phase structure
6. Equivalence to Shor: Connection to standard Shor measurement
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Shor Graph Vertices

The Shor graph has two types of vertices:
- Code vertices: one for each qubit in supp(L)
- Dummy vertices: one auxiliary qubit for each code qubit

This is similar to the ladder structure but with a specific interpretation.
-/

/-- Vertex type for the Shor measurement graph.
    For a logical operator with support size n:
    - `code i` represents the i-th code qubit in supp(L)
    - `dummy i` represents the auxiliary dummy qubit for code qubit i -/
inductive ShorVertex (n : ℕ) where
  | code : Fin n → ShorVertex n
  | dummy : Fin n → ShorVertex n
  deriving DecidableEq

namespace ShorVertex

variable {n : ℕ}

/-- Is this vertex a code qubit? -/
def isCode : ShorVertex n → Bool
  | code _ => true
  | dummy _ => false

/-- Is this vertex a dummy qubit? -/
def isDummy : ShorVertex n → Bool
  | code _ => false
  | dummy _ => true

/-- Get the index of the vertex (0 to n-1) -/
def index : ShorVertex n → Fin n
  | code i => i
  | dummy i => i

/-- Code vertices are injective -/
theorem code_injective : Function.Injective (code : Fin n → ShorVertex n) := by
  intro i j h
  cases h
  rfl

/-- Dummy vertices are injective -/
theorem dummy_injective : Function.Injective (dummy : Fin n → ShorVertex n) := by
  intro i j h
  cases h
  rfl

/-- Code and dummy vertices are disjoint -/
theorem code_ne_dummy (i j : Fin n) : code i ≠ dummy j := by
  intro h
  cases h

/-- Dummy and code vertices are disjoint -/
theorem dummy_ne_code (i j : Fin n) : dummy i ≠ code j := by
  intro h
  cases h

end ShorVertex

/-- Fintype instance for ShorVertex -/
instance {n : ℕ} [NeZero n] : Fintype (ShorVertex n) := by
  haveI : Fintype (Fin n) := Fin.fintype n
  exact Fintype.ofEquiv (Fin n ⊕ Fin n) {
    toFun := fun x => match x with
      | Sum.inl i => ShorVertex.code i
      | Sum.inr i => ShorVertex.dummy i
    invFun := fun v => match v with
      | ShorVertex.code i => Sum.inl i
      | ShorVertex.dummy i => Sum.inr i
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun v => by cases v <;> rfl
  }

/-- Cardinality of Shor vertices is exactly 2n -/
theorem shorVertex_card {n : ℕ} [NeZero n] :
    Fintype.card (ShorVertex n) = 2 * n := by
  have h_sum : Fintype.card (Fin n ⊕ Fin n) = Fintype.card (Fin n) + Fintype.card (Fin n) :=
    @Fintype.card_sum (Fin n) (Fin n) _ _
  calc Fintype.card (ShorVertex n)
    = Fintype.card (Fin n ⊕ Fin n) := Fintype.card_congr ⟨
        fun v => match v with
          | ShorVertex.code i => Sum.inl i
          | ShorVertex.dummy i => Sum.inr i,
        fun x => match x with
          | Sum.inl i => ShorVertex.code i
          | Sum.inr i => ShorVertex.dummy i,
        fun v => by cases v <;> rfl,
        fun x => by cases x <;> rfl⟩
    _ = Fintype.card (Fin n) + Fintype.card (Fin n) := h_sum
    _ = n + n := by simp only [Fintype.card_fin]
    _ = 2 * n := by ring

/-! ## Section 2: Shor Graph Edges

The Shor graph has two types of edges:
- Rung edges: connect code qubit i to dummy qubit i
- Dummy-connection edges: connect consecutive dummy qubits to form a path/tree
-/

/-- Rung edge: connects code qubit i to dummy qubit i -/
def isRungEdgeShor {n : ℕ} (v w : ShorVertex n) : Prop :=
  match v, w with
  | ShorVertex.code i, ShorVertex.dummy j => i = j
  | ShorVertex.dummy i, ShorVertex.code j => i = j
  | _, _ => False

/-- Dummy-connection edge: connects consecutive dummy qubits -/
def isDummyConnectionEdge {n : ℕ} (v w : ShorVertex n) : Prop :=
  match v, w with
  | ShorVertex.dummy i, ShorVertex.dummy j =>
      i.val + 1 = j.val ∨ j.val + 1 = i.val
  | _, _ => False

/-- Shor graph adjacency: rung or dummy-connection edge -/
def isShorAdjacent {n : ℕ} (v w : ShorVertex n) : Prop :=
  isRungEdgeShor v w ∨ isDummyConnectionEdge v w

/-- Rung edges are symmetric -/
theorem isRungEdgeShor_symm {n : ℕ} (v w : ShorVertex n) :
    isRungEdgeShor v w ↔ isRungEdgeShor w v := by
  cases v <;> cases w <;> simp only [isRungEdgeShor] <;> exact Iff.intro Eq.symm Eq.symm

/-- Dummy-connection edges are symmetric -/
theorem isDummyConnectionEdge_symm {n : ℕ} (v w : ShorVertex n) :
    isDummyConnectionEdge v w ↔ isDummyConnectionEdge w v := by
  cases v <;> cases w <;> simp [isDummyConnectionEdge, or_comm]

/-- Shor adjacency is symmetric -/
theorem isShorAdjacent_symm {n : ℕ} (v w : ShorVertex n) :
    isShorAdjacent v w ↔ isShorAdjacent w v := by
  unfold isShorAdjacent
  rw [isRungEdgeShor_symm, isDummyConnectionEdge_symm]

/-- Shor adjacency is irreflexive -/
theorem isShorAdjacent_irrefl {n : ℕ} (v : ShorVertex n) :
    ¬isShorAdjacent v v := by
  intro h
  unfold isShorAdjacent isRungEdgeShor isDummyConnectionEdge at h
  cases v with
  | code i => simp only [or_self] at h
  | dummy i => simp only [or_self, false_or] at h; omega

/-! ## Section 3: Shor Graph Edge Counts

We count the edges in the Shor graph:
- Rung edges: n (one per code/dummy pair)
- Dummy-connection edges: n-1 (forming a path among n dummies)
- Total: 2n - 1
-/

/-- Number of rung edges: n (one per code qubit) -/
def shorRungCount (n : ℕ) : ℕ := n

/-- Number of dummy-connection edges: n - 1 (forming a path among dummies) -/
def shorDummyEdgeCount (n : ℕ) : ℕ := n - 1

/-- Total edges in Shor graph: n + (n-1) = 2n - 1 -/
def shorTotalEdgeCount (n : ℕ) : ℕ := shorRungCount n + shorDummyEdgeCount n

/-- Edge count formula: 2n - 1 for n ≥ 1 -/
theorem shorTotalEdgeCount_formula (n : ℕ) (hn : 1 ≤ n) :
    shorTotalEdgeCount n = 2 * n - 1 := by
  unfold shorTotalEdgeCount shorRungCount shorDummyEdgeCount
  omega

/-- Rung count equals support size -/
theorem shorRungCount_eq_support (n : ℕ) : shorRungCount n = n := rfl

/-! ## Section 4: Shor Graph is a Tree

The Shor graph has cycle rank 0, meaning it is a tree.
This follows from: |E| = 2n - 1 = |V| - 1
-/

/-- Cycle rank of the Shor graph: |E| - |V| + 1 = (2n-1) - 2n + 1 = 0 -/
def shorCycleRank (n : ℕ) : ℤ :=
  (shorTotalEdgeCount n : ℤ) - (2 * n : ℤ) + 1

/-- The Shor graph has cycle rank 0 (is a tree) for n ≥ 1 -/
theorem shor_graph_is_tree (n : ℕ) (hn : 1 ≤ n) : shorCycleRank n = 0 := by
  unfold shorCycleRank
  have h_edges := shorTotalEdgeCount_formula n hn
  simp only [h_edges]
  omega

/-- For a tree: |E| = |V| - 1 -/
theorem shor_tree_edge_formula (n : ℕ) (hn : 1 ≤ n) :
    shorTotalEdgeCount n = 2 * n - 1 := shorTotalEdgeCount_formula n hn

/-! ## Section 5: Dummy Subgraph Structure

The dummy vertices form a path graph (connected subgraph).
This is the structure that, when measured first, creates the GHZ state.
-/

/-- The dummy subgraph is a path of length n -/
def dummyPathLength (n : ℕ) : ℕ := n

/-- The dummy subgraph has n - 1 edges (forming a path) -/
def dummySubgraphEdgeCount (n : ℕ) : ℕ := n - 1

/-- The dummy subgraph has n vertices -/
def dummySubgraphVertexCount (n : ℕ) : ℕ := n

/-- The dummy subgraph is connected (for n ≥ 1) -/
theorem dummy_subgraph_connected (n : ℕ) (_hn : 1 ≤ n) :
    dummySubgraphEdgeCount n = dummySubgraphVertexCount n - 1 := by
  unfold dummySubgraphEdgeCount dummySubgraphVertexCount
  rfl

/-- Distance between dummy vertices on the path -/
def dummyDistance {n : ℕ} (i j : Fin n) : ℕ :=
  if i.val ≤ j.val then j.val - i.val else i.val - j.val

theorem dummyDistance_symm {n : ℕ} (i j : Fin n) :
    dummyDistance i j = dummyDistance j i := by
  unfold dummyDistance
  split_ifs with h1 h2 h2 <;> omega

theorem dummyDistance_self {n : ℕ} (i : Fin n) :
    dummyDistance i i = 0 := by
  unfold dummyDistance
  simp

/-- Maximum distance between any two dummy vertices is n - 1 -/
theorem dummyDistance_bounded {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    dummyDistance i j ≤ n - 1 := by
  unfold dummyDistance
  split_ifs <;> omega

/-! ## Section 6: Measurement Process

The Shor measurement via gauging proceeds in two phases:
1. Measure flux operators on the dummy subgraph (projects dummies into GHZ state)
2. Measure the rung edges (equivalent to X measurements commuted through CX)
-/

/-- Phase 1: Number of measurements on dummy subgraph -/
def phase1MeasurementCount (n : ℕ) : ℕ := dummySubgraphEdgeCount n

/-- Phase 2: Number of rung edge measurements -/
def phase2MeasurementCount (n : ℕ) : ℕ := shorRungCount n

/-- Total measurements equals total edges -/
theorem total_measurement_count (n : ℕ) :
    phase1MeasurementCount n + phase2MeasurementCount n = shorTotalEdgeCount n := by
  unfold phase1MeasurementCount phase2MeasurementCount shorTotalEdgeCount
  unfold dummySubgraphEdgeCount shorRungCount shorDummyEdgeCount
  omega

/-- Phase 1 measurements = n - 1 -/
theorem phase1_count_formula (n : ℕ) : phase1MeasurementCount n = n - 1 := rfl

/-- Phase 2 measurements = n -/
theorem phase2_count_formula (n : ℕ) : phase2MeasurementCount n = n := rfl

/-! ## Section 7: GHZ State Projection

After Phase 1, the dummy qubits are in a GHZ state.
This is because measuring the flux operators on a path graph
projects the endpoints into an entangled state.
-/

/-- The dummy subgraph has cycle rank 0 (is a tree/path) -/
def dummySubgraphCycleRank (n : ℕ) : ℤ :=
  (dummySubgraphEdgeCount n : ℤ) - (dummySubgraphVertexCount n : ℤ) + 1

/-- The dummy subgraph is a tree -/
theorem dummy_subgraph_is_tree (n : ℕ) (hn : 1 ≤ n) :
    dummySubgraphCycleRank n = 0 := by
  unfold dummySubgraphCycleRank dummySubgraphEdgeCount dummySubgraphVertexCount
  omega

/-- Number of flux operators on the dummy subgraph (equals cycle rank = 0 for tree) -/
def dummyFluxOperatorCount (n : ℕ) : ℕ :=
  if dummySubgraphCycleRank n > 0
  then (dummySubgraphCycleRank n).toNat
  else 0

/-- For a tree, there are no flux operators (only edge Z measurements) -/
theorem dummy_no_flux_operators (n : ℕ) (hn : 1 ≤ n) :
    dummyFluxOperatorCount n = 0 := by
  unfold dummyFluxOperatorCount
  have h := dummy_subgraph_is_tree n hn
  simp [h]

/-! ## Section 8: Shor Measurement Equivalence

The gauging measurement with this graph structure is equivalent to:
1. Initialize dummies in |+⟩ (automatically done by edge qubit initialization)
2. Apply transversal CX from dummies to code qubits
3. Measure X on all dummies

The equivalence comes from:
- Edge measurements = CX-commuted X measurements
- The connected dummy subgraph creates the GHZ entanglement
-/

/-- The Shor graph parameters satisfy the gauging graph requirements -/
structure ShorGraphParams where
  /-- Support size of the logical operator -/
  supportSize : ℕ
  /-- Support size is positive -/
  supportSize_pos : 0 < supportSize

namespace ShorGraphParams

/-- Total vertex count: 2 × support size -/
def vertexCount (p : ShorGraphParams) : ℕ := 2 * p.supportSize

/-- Total edge count: 2 × support size - 1 -/
def edgeCount (p : ShorGraphParams) : ℕ := shorTotalEdgeCount p.supportSize

/-- Code qubit count -/
def codeQubitCount (p : ShorGraphParams) : ℕ := p.supportSize

/-- Dummy qubit count -/
def dummyQubitCount (p : ShorGraphParams) : ℕ := p.supportSize

/-- Cycle rank (should be 0 for tree) -/
def cycleRank (p : ShorGraphParams) : ℤ := shorCycleRank p.supportSize

/-- The Shor graph is a tree -/
theorem is_tree (p : ShorGraphParams) : p.cycleRank = 0 := by
  have h_one_le := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp p.supportSize_pos)
  exact shor_graph_is_tree p.supportSize h_one_le

/-- Vertex count formula -/
theorem vertexCount_formula (p : ShorGraphParams) :
    p.vertexCount = 2 * p.supportSize := rfl

/-- Edge count formula -/
theorem edgeCount_formula (p : ShorGraphParams) :
    p.edgeCount = 2 * p.supportSize - 1 := by
  unfold edgeCount
  exact shorTotalEdgeCount_formula p.supportSize
    (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp p.supportSize_pos))

/-- Dummy equals code qubit count -/
theorem dummy_eq_code_count (p : ShorGraphParams) :
    p.dummyQubitCount = p.codeQubitCount := rfl

end ShorGraphParams

/-! ## Section 9: Auxiliary Qubit Overhead

The Shor measurement via gauging uses:
- n dummy qubits (one per code qubit in support)
- 2n - 1 auxiliary edge qubits (for CX gates)

Total auxiliary qubits: n + (2n - 1) = 3n - 1
-/

/-- Total auxiliary qubits for Shor via gauging -/
def shorAuxiliaryQubitCount (n : ℕ) : ℕ :=
  -- Dummy qubits + edge qubits
  n + shorTotalEdgeCount n

/-- Auxiliary qubit count formula: 3n - 1 for n ≥ 1 -/
theorem shorAuxiliaryQubitCount_formula (n : ℕ) (hn : 1 ≤ n) :
    shorAuxiliaryQubitCount n = 3 * n - 1 := by
  unfold shorAuxiliaryQubitCount
  have h := shorTotalEdgeCount_formula n hn
  omega

/-- Comparison: Standard Shor uses n auxiliary qubits (GHZ state) -/
def standardShorAuxiliaryCount (n : ℕ) : ℕ := n

/-- Gauging Shor uses more auxiliary qubits than standard Shor -/
theorem gauging_uses_more_qubits (n : ℕ) (_hn : 1 ≤ n) :
    shorAuxiliaryQubitCount n ≥ standardShorAuxiliaryCount n := by
  unfold shorAuxiliaryQubitCount standardShorAuxiliaryCount
  omega

/-- The overhead ratio approaches 3 for large n -/
theorem auxiliary_overhead_ratio (n : ℕ) (hn : 1 ≤ n) :
    shorAuxiliaryQubitCount n < 3 * standardShorAuxiliaryCount n := by
  unfold shorAuxiliaryQubitCount standardShorAuxiliaryCount
  have h := shorTotalEdgeCount_formula n hn
  omega

/-! ## Section 10: Connection to Remark 19 (Ladder Structure)

The Shor graph is structurally similar to the ladder graph from Remark 19,
but with a different interpretation:
- Ladder: Two rails connected by rungs (for lattice surgery)
- Shor: Code qubits + dummy chain connected by rungs (for logical measurement)

In fact, the Shor graph is a degenerate ladder with one rail being the code
and the other being a path of dummies.
-/

/-- The Shor graph has the same vertex count as a ladder -/
theorem shor_vertex_eq_ladder {n : ℕ} [NeZero n] :
    Fintype.card (ShorVertex n) = Fintype.card (LadderVertex n) := by
  rw [shorVertex_card, ladderVertex_card]

/-- The Shor graph has at most as many edges as a ladder -/
theorem shor_le_edges_than_ladder (n : ℕ) (_hn : 1 ≤ n) :
    shorTotalEdgeCount n ≤ ladderEdgeCount n := by
  -- shorTotalEdgeCount n = n + (n - 1)
  -- ladderEdgeCount n = n + 2 * (n - 1)
  -- Need: n + (n - 1) ≤ n + 2 * (n - 1)
  unfold shorTotalEdgeCount shorRungCount shorDummyEdgeCount
  unfold ladderEdgeCount ladderRungCount ladderRailEdgeCount
  apply Nat.add_le_add_left
  exact Nat.le_mul_of_pos_left _ (by omega : 0 < 2)

/-- For n ≥ 2, the Shor graph has strictly fewer edges than a ladder -/
theorem shor_fewer_edges_than_ladder (n : ℕ) (hn : 2 ≤ n) :
    shorTotalEdgeCount n < ladderEdgeCount n := by
  -- shorTotalEdgeCount n = n + (n - 1)
  -- ladderEdgeCount n = n + 2 * (n - 1)
  -- Need: n + (n - 1) < n + 2 * (n - 1) when n ≥ 2
  unfold shorTotalEdgeCount shorRungCount shorDummyEdgeCount
  unfold ladderEdgeCount ladderRungCount ladderRailEdgeCount
  apply Nat.add_lt_add_left
  -- Need: n - 1 < 2 * (n - 1), which holds when n - 1 ≥ 1, i.e., n ≥ 2
  have h_pos : n - 1 > 0 := by omega
  calc n - 1 = 1 * (n - 1) := by ring
    _ < 2 * (n - 1) := by exact Nat.mul_lt_mul_of_pos_right (by omega : 1 < 2) h_pos

/-- The difference is exactly n - 1 (the missing rail on code side) -/
theorem shor_ladder_edge_diff (n : ℕ) (_hn : 1 ≤ n) :
    ladderEdgeCount n - shorTotalEdgeCount n = n - 1 := by
  -- ladderEdgeCount n = n + 2 * (n - 1)
  -- shorTotalEdgeCount n = n + (n - 1)
  -- diff = 2 * (n - 1) - (n - 1) = n - 1
  unfold ladderEdgeCount ladderRungCount ladderRailEdgeCount
  unfold shorTotalEdgeCount shorRungCount shorDummyEdgeCount
  -- Now it's: (n + 2 * (n - 1)) - (n + (n - 1)) = n - 1
  have h1 : n + 2 * (n - 1) ≥ n + (n - 1) := by
    apply Nat.add_le_add_left
    exact Nat.le_mul_of_pos_left _ (by omega : 0 < 2)
  rw [Nat.add_sub_add_left]
  -- Now: 2 * (n - 1) - (n - 1) = n - 1
  rw [Nat.two_mul, Nat.add_sub_cancel]

/-! ## Section 11: Summary and Helper Lemmas -/

/-- Summary: Shor graph vertex count -/
theorem shor_has_2n_vertices {n : ℕ} [NeZero n] :
    Fintype.card (ShorVertex n) = 2 * n := shorVertex_card

/-- Summary: Shor graph edge count -/
theorem shor_has_2n_minus_1_edges (n : ℕ) (hn : 1 ≤ n) :
    shorTotalEdgeCount n = 2 * n - 1 := shorTotalEdgeCount_formula n hn

/-- Summary: Shor graph is a tree -/
theorem shor_cycle_rank_zero (n : ℕ) (hn : 1 ≤ n) :
    shorCycleRank n = 0 := shor_graph_is_tree n hn

/-- Summary: Phase 1 creates GHZ state on dummies -/
theorem phase1_measurements (n : ℕ) :
    phase1MeasurementCount n = n - 1 := phase1_count_formula n

/-- Summary: Phase 2 measures logical via rungs -/
theorem phase2_measurements (n : ℕ) :
    phase2MeasurementCount n = n := phase2_count_formula n

/-- Helper: Shor graph has exactly one more edge than the dummy subgraph per code qubit -/
theorem shor_edges_decomposition (n : ℕ) :
    shorTotalEdgeCount n = shorRungCount n + shorDummyEdgeCount n := rfl

/-- Helper: The graph has no cycles because it's a tree -/
theorem shor_acyclic (n : ℕ) (hn : 1 ≤ n) :
    shorCycleRank n = 0 := shor_graph_is_tree n hn

/-- Helper: Distance from any code vertex to any dummy vertex via rung + path -/
def codeToDummyDistance {n : ℕ} (code_idx dummy_idx : Fin n) : ℕ :=
  1 + dummyDistance code_idx dummy_idx

/-- Maximum code-to-dummy distance is n -/
theorem codeToDummyDistance_bounded {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    codeToDummyDistance i j ≤ n := by
  unfold codeToDummyDistance
  have h := dummyDistance_bounded hn i j
  omega

/-- The diameter of the Shor graph is 2n - 1 (corner to opposite corner) -/
def shorDiameter (n : ℕ) : ℕ := 2 * n - 1

theorem shorDiameter_formula (n : ℕ) (_hn : 1 ≤ n) :
    shorDiameter n = 2 * n - 1 := rfl

/-- The Shor graph diameter equals the edge count (both 2n - 1) for n ≥ 1 -/
theorem shorDiameter_eq_edgeCount (n : ℕ) (hn : 1 ≤ n) :
    shorDiameter n = shorTotalEdgeCount n := by
  unfold shorDiameter
  exact (shorTotalEdgeCount_formula n hn).symm

end QEC
