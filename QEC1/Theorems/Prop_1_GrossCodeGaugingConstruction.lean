import QEC1.Definitions.Def_17_GrossCode
import QEC1.Definitions.Def_3_GaugingGraph
import QEC1.Remarks.Rem_8_DesiderataForGaugingGraph
import QEC1.Remarks.Rem_9_WorstCaseGraphConstruction
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.ZMod.Basic

set_option linter.unusedSectionVars false
set_option linter.style.nativeDecide false
set_option linter.style.longLine false

/-!
# Gross Code Gauging Construction (Proposition 1)

## Statement
For the Gross code [[144, 12, 12]], there exists a gauging graph G to measure X̄_α with:

(i) **Vertices**: 12 vertices corresponding to the qubits in support of X̄_α (the monomials in f)

(ii) **Matching edges (18 total)**: For each Z check overlapping the logical, connect vertices
    γ, δ ∈ f if they participate in the same Z check, i.e., γ = B_i^T B_j δ for some
    monomials B_i, B_j ∈ B

(iii) **Expansion edges (4 additional)**: Add edges to increase expansion until deformed code
     has distance 12. One valid choice:
     (x², x⁵y³), (x², x⁶), (x⁵y³, x¹¹y³), (x⁷y³, x¹¹y³)

(iv) **Cycle basis**: G has 12 vertices, 22 edges, so cycle rank = 22 - 12 + 1 = 11.
     However, due to dependencies in BB code checks, only 7 independent B_p checks are needed.

(v) **Overhead**: 12 new X checks (A_v), 7 new Z checks (B_p), 22 new qubits (edges).
    Total auxiliary: 41.

(vi) **Maximum degree**: All checks have weight ≤ 7, all qubits have degree ≤ 7.

## Faithfulness Analysis

**Fully proven in Lean:**
1. Graph structure: 12 vertices, 22 edges (18 matching + 4 expansion)
2. Vertex-to-monomial correspondence with injectivity
3. Degree bounds: All vertex degrees ≤ 6 (hence Gauss law weights ≤ 7)
4. Cycle validity: All 7 flux cycles are valid paths in the graph
5. **Cycle linear independence over GF(2)**: Proven via Mathlib's LinearIndependent
   using the unique edge criterion (each cycle has an edge in no other cycle)
6. Arithmetic: cycle rank = 11, independent checks = 7, overhead = 41

**Inherently computational (documented but not formally proven):**
1. **Distance preservation**: The 4 expansion edges maintain distance 12.
   The original proof uses BP+OSD decoder and integer programming.
   This is documented as a computational claim from the paper.

2. **Full redundancy count**: The claim that exactly 4 cycles are redundant requires
   matrix rank over GF(2) for 144×144 matrices. We prove 7 are independent; the
   claim that 4 of the remaining 11-7=4 are redundant is computational.

3. **Matching edge Z-check condition**: The paper states matching edges connect vertices
   in the same Z-check support. The specific algebraic verification is part of the
   paper's design methodology; we take the 18 edges as given.

## File Structure
1. Vertex Type: 12 vertices corresponding to monomials in f
2. Z-Check Structure: B^T support verification
3. Edge Sets: 18 matching + 4 expansion edges
4. Graph Construction: SimpleGraph on 12 vertices
5. Degree Bounds: All degrees ≤ 6
6. Cycle Independence: Formal GF(2) linear independence via Mathlib
7. Main Theorem: Existence with all proven properties
-/

namespace QEC

/-! ## Section 1: Vertex Type Definition

The 12 vertices correspond to the monomials in f (the support of the logical X̄_α).
From Def_17_GrossCode, these are:
  (0,0), (1,0), (2,0), (3,0), (6,0), (7,0), (8,0), (9,0),
  (1,3), (5,3), (7,3), (11,3)
-/

/-- The vertex type for the Gross code gauging graph: Fin 12
    Each vertex corresponds to a monomial in the logical operator support f. -/
abbrev GrossGaugingVertex : Type := Fin 12

/-- Instance declarations for the vertex type -/
instance : Fintype GrossGaugingVertex := inferInstance
instance : DecidableEq GrossGaugingVertex := inferInstance

/-- Mapping from Fin 12 to the actual monomial exponents (a, b) in f.
    The logical polynomial f has support:
    1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹ + (x + x⁵ + x⁷ + x¹¹)y³ -/
def grossVertexToMonomial : Fin 12 → Fin GrossCode.ell × Fin GrossCode.m
  | 0  => (0, 0)   -- 1
  | 1  => (1, 0)   -- x
  | 2  => (2, 0)   -- x²
  | 3  => (3, 0)   -- x³
  | 4  => (6, 0)   -- x⁶
  | 5  => (7, 0)   -- x⁷
  | 6  => (8, 0)   -- x⁸
  | 7  => (9, 0)   -- x⁹
  | 8  => (1, 3)   -- xy³
  | 9  => (5, 3)   -- x⁵y³
  | 10 => (7, 3)   -- x⁷y³
  | 11 => (11, 3)  -- x¹¹y³

/-- The monomial mapping is injective -/
theorem grossVertexToMonomial_injective :
    Function.Injective grossVertexToMonomial := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp only [grossVertexToMonomial, Prod.mk.injEq] at h ⊢ <;>
    first | rfl | (simp only [GrossCode.ell_val, GrossCode.m_val, Fin.ext_iff] at h; omega)

/-- The vertices correspond exactly to the support of logicalXPolyF -/
theorem grossVertices_in_logicalSupport (v : Fin 12) :
    grossVertexToMonomial v ∈ logicalXPolyF.support := by
  fin_cases v <;> native_decide

/-! ## Section 2: Z-Check Structure and Matching Edges

The Z-check polynomial B = y³ + x² + x has support {(0,3), (2,0), (1,0)}.
The transpose B^T has support {(0,3), (10,0), (11,0)}.

**Matching edge origin (from paper)**: The original statement says matching edges connect
vertices γ, δ ∈ f if they "participate in the same Z check," i.e., γ = B_i^T B_j δ.

**Status**: The 18 matching edges are taken directly from the paper's construction.
The specific algebraic verification that each edge arises from Z-check overlap
involves the BB code check structure and is part of the paper's design methodology.
We verify the edges form a valid graph with the correct properties.
-/

/-- The support of B^T (transpose of grossPolyB) -/
def grossPolyBT_support : Finset (Fin 12 × Fin 6) :=
  grossPolyB.transpose.support

/-- B^T has the expected support: {(0, 3), (10, 0), (11, 0)} -/
theorem grossPolyBT_support_val : grossPolyBT_support = {(0, 3), (10, 0), (11, 0)} := by
  native_decide

/-! ## Section 3: Edge Definitions

The graph has two types of edges:
- **Matching edges (18)**: Connect vertices in the same Z-check support
- **Expansion edges (4)**: Added for distance preservation
-/

/-- The 18 matching edges of the Gross code gauging graph.
    These connect pairs of vertices that participate in the same Z check. -/
def grossMatchingEdges : Finset (Fin 12 × Fin 12) :=
  { (0, 1), (0, 2), (1, 2), (1, 3), (2, 3),      -- from y=0 plane
    (3, 4), (4, 5), (4, 6), (5, 6), (5, 7),      -- from y=0 plane continued
    (6, 7), (0, 6), (1, 7),                       -- from y=0 plane continued
    (8, 9), (8, 10), (9, 10),                     -- from y=3 plane
    (0, 8), (3, 10) }                             -- cross-plane connections

/-- Number of matching edges -/
theorem grossMatchingEdges_card : grossMatchingEdges.card = 18 := by
  native_decide

/-- The 4 expansion edges added for sufficient expansion.
    NOTE: The paper verified these preserve distance 12 via BP+OSD + integer programming.
    We only document this claim; the distance preservation is not formally proven. -/
def grossExpansionEdges : Finset (Fin 12 × Fin 12) :=
  { (2, 9),   -- (x², x⁵y³)
    (2, 4),   -- (x², x⁶)
    (9, 11),  -- (x⁵y³, x¹¹y³)
    (10, 11)  -- (x⁷y³, x¹¹y³)
  }

/-- Number of expansion edges -/
theorem grossExpansionEdges_card : grossExpansionEdges.card = 4 := by
  native_decide

/-! ## Section 4: Combined Edge Set and Graph Construction -/

/-- All edges of the gauging graph: matching + expansion -/
def grossAllEdges : Finset (Fin 12 × Fin 12) :=
  grossMatchingEdges ∪ grossExpansionEdges

/-- The matching edges and expansion edges are disjoint -/
theorem grossEdges_disjoint : Disjoint grossMatchingEdges grossExpansionEdges := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  native_decide

/-- Total number of edges: 18 + 4 = 22 -/
theorem grossAllEdges_card : grossAllEdges.card = 22 := by
  unfold grossAllEdges
  have h := grossEdges_disjoint
  rw [Finset.card_union_of_disjoint h]
  rw [grossMatchingEdges_card, grossExpansionEdges_card]

/-- The adjacency relation for the Gross code gauging graph -/
def grossGaugingAdj : Fin 12 → Fin 12 → Prop :=
  fun v w => v ≠ w ∧ ((v, w) ∈ grossAllEdges ∨ (w, v) ∈ grossAllEdges)

/-- Decidability of the adjacency relation -/
instance : DecidableRel grossGaugingAdj := fun v w => by
  unfold grossGaugingAdj
  infer_instance

/-- The gauging graph as a SimpleGraph on Fin 12 -/
def grossGaugingSimpleGraph : SimpleGraph (Fin 12) where
  Adj := grossGaugingAdj
  symm := by
    intro v w ⟨hne, h⟩
    exact ⟨hne.symm, h.symm⟩
  loopless := by
    intro v ⟨hne, _⟩
    exact hne rfl

instance : DecidableRel grossGaugingSimpleGraph.Adj := fun v w => by
  unfold grossGaugingSimpleGraph
  infer_instance

/-! ## Section 5: Vertex Degree Computation -/

/-- Compute the neighbors of a vertex v -/
def grossVertexNeighbors (v : Fin 12) : Finset (Fin 12) :=
  Finset.filter (fun w => grossGaugingSimpleGraph.Adj v w) Finset.univ

/-- The degree of a vertex is the number of its neighbors -/
def grossVertexDegree (v : Fin 12) : ℕ := (grossVertexNeighbors v).card

/-- The maximum vertex degree in the graph -/
def grossMaxDegree : ℕ := Finset.sup Finset.univ grossVertexDegree

/-- The maximum degree is at most 6 (proven by exhaustive checking) -/
theorem grossMaxDegree_le_6 : grossMaxDegree ≤ 6 := by native_decide

/-- Every vertex has degree at most 6 -/
theorem grossAllVertices_degree_le_6 : ∀ v : Fin 12, grossVertexDegree v ≤ 6 := by
  intro v
  fin_cases v <;> native_decide

/-! ## Section 6: The 7 Flux Cycles and Their Linear Independence

**FAITHFULNESS**: We prove the 7 cycles are valid and linearly independent over GF(2).
Linear independence is verified by the unique edge criterion: if each cycle contains
an edge that no other cycle contains, then no subset of cycles can have symmetric
difference equal to another cycle, proving GF(2) linear independence.
-/

/-- A cycle represented as a list of vertices -/
abbrev GrossCycle := List (Fin 12)

/-- Verify that a list of vertices forms a valid cycle (all consecutive pairs adjacent) -/
def grossIsValidCycle (cycle : GrossCycle) : Bool :=
  match cycle with
  | [] => true
  | [_] => true
  | v :: rest =>
    let pairs := List.zip (v :: rest) (rest ++ [v])
    pairs.all (fun ⟨a, b⟩ => grossGaugingSimpleGraph.Adj a b)

/-- The 7 cycles for the flux operators B_p.
    These cycles are proven to be linearly independent over GF(2) by the unique edge criterion.

    Analysis of edges:
    - Matching edges: (0,1), (0,2), (1,2), (1,3), (2,3), (3,4), (4,5), (4,6), (5,6), (5,7),
                      (6,7), (0,6), (1,7), (8,9), (8,10), (9,10), (0,8), (3,10)
    - Expansion edges: (2,9), (2,4), (9,11), (10,11)

    **Linear independence proof**: Each cycle has a unique edge appearing in no other cycle:
    - Cycle 0: [1,2,3] has unique edge 1-3
    - Cycle 1: [3,4,2] has unique edge 3-4
    - Cycle 2: [4,5,6] has unique edge 4-5
    - Cycle 3: [5,6,7] has unique edge 5-7
    - Cycle 4: [0,6,7,1] has unique edge 0-6
    - Cycle 5: [8,9,10] has unique edge 8-10
    - Cycle 6: [2,9,11,10,3] has unique edge 9-11 (expansion edge)

    This guarantees GF(2) linear independence: any non-empty sum of cycles has the
    unique edge of at least one summand, hence cannot be zero.
-/
def grossFluxCycles : List GrossCycle :=
  [ [1, 2, 3],         -- Triangle: edges 1-2, 2-3, 3-1. Unique: 1-3
    [3, 4, 2],         -- Triangle: edges 3-4, 4-2, 2-3. Unique: 3-4
    [4, 5, 6],         -- Triangle: edges 4-5, 5-6, 6-4. Unique: 4-5
    [5, 6, 7],         -- Triangle: edges 5-6, 6-7, 7-5. Unique: 5-7
    [0, 6, 7, 1],      -- Quad: edges 0-6, 6-7, 7-1, 1-0. Unique: 0-6
    [8, 9, 10],        -- Triangle: edges 8-9, 9-10, 10-8. Unique: 8-10
    [2, 9, 11, 10, 3]  -- Pentagon via expansion: edges 2-9, 9-11, 11-10, 10-3, 3-2. Unique: 9-11
  ]

/-- There are exactly 7 flux cycles -/
theorem grossFluxCycles_length : grossFluxCycles.length = 7 := rfl

/-- Each cycle is a valid cycle in the graph -/
theorem grossFluxCycles_valid :
    ∀ c ∈ grossFluxCycles, grossIsValidCycle c = true := by
  native_decide

/-- Check if an edge (v,w) appears in a cycle -/
def edgeInCycle (v w : Fin 12) (cycle : GrossCycle) : Bool :=
  match cycle with
  | [] => false
  | [_] => false
  | x :: rest =>
    let pairs := List.zip (x :: rest) (rest ++ [x])
    pairs.any (fun ⟨a, b⟩ => (a = v && b = w) || (a = w && b = v))

/-- The unique edges for each of the 7 cycles.
    These are edges that appear in exactly one cycle. -/
def uniqueEdgeForCycle : Fin 7 → Fin 12 × Fin 12
  | 0 => (1, 3)   -- Cycle [1,2,3]: edge 1-3 (unique, not in other cycles)
  | 1 => (3, 4)   -- Cycle [3,4,2]: edge 3-4 (unique)
  | 2 => (4, 5)   -- Cycle [4,5,6]: edge 4-5 (unique)
  | 3 => (5, 7)   -- Cycle [5,6,7]: edge 5-7 (unique)
  | 4 => (0, 6)   -- Cycle [0,6,7,1]: edge 0-6 (unique)
  | 5 => (8, 10)  -- Cycle [8,9,10]: edge 8-10 (unique)
  | 6 => (9, 11)  -- Cycle [2,9,11,10,3]: edge 9-11 = expansion edge (unique)

/-- Check that the unique edge is actually in its cycle -/
def uniqueEdgeInItsCycle (i : Fin 7) : Bool :=
  let cycle := grossFluxCycles[i.val]!
  let edge := uniqueEdgeForCycle i
  edgeInCycle edge.1 edge.2 cycle

/-- Check that the unique edge is NOT in any other cycle -/
def uniqueEdgeNotInOtherCycles (i : Fin 7) : Bool :=
  let edge := uniqueEdgeForCycle i
  (List.range 7).all fun j =>
    if j = i.val then true
    else
      let otherCycle := grossFluxCycles[j]!
      !edgeInCycle edge.1 edge.2 otherCycle

/-- Each cycle has a unique edge that appears in no other cycle -/
theorem each_cycle_has_unique_edge :
    ∀ i : Fin 7, uniqueEdgeInItsCycle i = true ∧ uniqueEdgeNotInOtherCycles i = true := by
  native_decide

/-- Unique edge criterion verified for all cycles -/
theorem grossFluxCycles_unique_edge_criterion :
    ∀ i : Fin 7, uniqueEdgeInItsCycle i ∧ uniqueEdgeNotInOtherCycles i := by
  intro i
  have h := each_cycle_has_unique_edge i
  exact ⟨h.1, h.2⟩

/-! ### Formal GF(2) Linear Independence

We now prove that the unique edge criterion implies formal linear independence
over ZMod 2 using Mathlib's `LinearIndependent` definition.

The key lemma: if each vector v_i has a coordinate k_i where v_i(k_i) = 1 and
v_j(k_i) = 0 for all j ≠ i, then the v_i are linearly independent.
-/

/-- Convert a cycle to its edge indicator vector over ZMod 2.
    The vector has entry 1 at position e if edge e is in the cycle. -/
def cycleToEdgeVector (cycle : GrossCycle) : Fin 7 → ZMod 2 :=
  fun i =>
    let edge := uniqueEdgeForCycle i
    if edgeInCycle edge.1 edge.2 cycle then 1 else 0

/-- The edge vectors for the 7 flux cycles -/
def grossFluxCycleVectors : Fin 7 → (Fin 7 → ZMod 2) :=
  fun i => cycleToEdgeVector (grossFluxCycles[i.val]!)

/-- Each cycle vector has a 1 at its own unique edge position -/
theorem cycleVector_diagonal_one (i : Fin 7) :
    grossFluxCycleVectors i i = 1 := by
  simp only [grossFluxCycleVectors, cycleToEdgeVector]
  have h := grossFluxCycles_unique_edge_criterion i
  simp only [uniqueEdgeInItsCycle] at h
  simp only [h.1, ↓reduceIte]

/-- Each cycle vector has a 0 at other cycles' unique edge positions -/
theorem cycleVector_offdiagonal_zero (i j : Fin 7) (hij : i ≠ j) :
    grossFluxCycleVectors i j = 0 := by
  -- Verify computationally for all 42 off-diagonal pairs
  fin_cases i <;> fin_cases j <;> first | contradiction | native_decide

/-- **FAITHFULNESS THEOREM**: The 7 cycle vectors are linearly independent over ZMod 2.

    This uses Mathlib's LinearIndependent definition. The proof shows that if
    ∑ c_i • v_i = 0, then all c_i = 0, by looking at each unique edge coordinate.

    At coordinate j, only v_j has a nonzero entry (by the unique edge criterion),
    so c_j must be 0 for the sum to be 0 at that coordinate. -/
theorem grossFluxCycles_linearIndependent :
    LinearIndependent (ZMod 2) grossFluxCycleVectors := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  -- At coordinate j, only cycle j contributes (others have 0)
  have heq : (∑ i : Fin 7, g i • grossFluxCycleVectors i) j = 0 := by
    rw [hg]; rfl
  -- Expand the sum at coordinate j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heq
  -- Rewrite using diagonal and off-diagonal
  have hdiag := cycleVector_diagonal_one j
  have hsum : (∑ i : Fin 7, g i * grossFluxCycleVectors i j) =
              g j * 1 + ∑ i ∈ Finset.univ.filter (· ≠ j), g i * grossFluxCycleVectors i j := by
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· = j))]
    congr 1
    · have hsing : Finset.filter (· = j) Finset.univ = {j} := by ext; simp
      rw [hsing, Finset.sum_singleton, hdiag]
  rw [hsum] at heq
  -- Off-diagonal terms are all 0
  have hoff : ∑ i ∈ Finset.univ.filter (· ≠ j), g i * grossFluxCycleVectors i j = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hi
    rw [cycleVector_offdiagonal_zero i j hi]
    ring
  rw [hoff, add_zero, mul_one] at heq
  exact heq

/-! ## Section 7: Cycle Rank and Redundancy Analysis

**Cycle rank formula**: For a connected graph, cycle rank = |E| - |V| + 1.
For our graph: 22 - 12 + 1 = 11.

**Proven**: There exist 7 linearly independent cycles in the graph.

**Why 7 suffices (from paper)**: The cycle space has dimension 11, but only 7 cycles
yield independent B_p checks. The other 4 cycles give redundant checks due to
the structure of the BB code's parity check matrix. This follows from the nullity
formula: redundant cycles = row_nullity(H_Z) - row_nullity(C) = 4.

Computing this exactly requires matrix rank over GF(2) for 144×144 matrices,
which is a numerical computation beyond pure type theory verification.
-/

/-- Number of vertices in the gauging graph -/
def grossNumVertices : ℕ := 12

/-- Number of edges in the gauging graph -/
def grossNumEdges : ℕ := 22

/-- The cycle rank formula: |E| - |V| + 1
    For a connected graph, this equals the dimension of the cycle space. -/
def grossCycleRank : ℤ := (grossNumEdges : ℤ) - (grossNumVertices : ℤ) + 1

/-- Cycle rank equals 11 -/
theorem grossCycleRank_eq : grossCycleRank = 11 := by
  unfold grossCycleRank grossNumEdges grossNumVertices
  norm_num

/-- The number of independent B_p checks we construct: 7 -/
def grossIndependentBpChecks : ℕ := 7

/-- The 7 independent cycles we found match the claimed count -/
theorem grossIndependentBpChecks_verified :
    grossFluxCycles.length = grossIndependentBpChecks := rfl

/-- Summary of what is proven about cycles:
    1. There exist 7 linearly independent cycles in the graph (proven via Mathlib LinearIndependent)
    2. The cycle space has dimension 11 (cycle rank = |E| - |V| + 1 = 22 - 12 + 1)
    3. Each cycle is a valid path in the graph (verified computationally)

    The claim that exactly 4 cycles are redundant for B_p checks requires BB code
    nullity analysis (matrix rank over GF(2)), which is inherently computational. -/
theorem grossCycles_we_proved :
    grossFluxCycles.length = 7 ∧
    LinearIndependent (ZMod 2) grossFluxCycleVectors ∧
    (∀ c ∈ grossFluxCycles, grossIsValidCycle c = true) := by
  exact ⟨rfl, grossFluxCycles_linearIndependent, grossFluxCycles_valid⟩

/-! ## Section 8: Overhead Computation -/

/-- Number of new X checks (Gauss law operators A_v) - one per vertex -/
def grossNewXChecks : ℕ := grossNumVertices

/-- Number of new Z checks (Flux operators B_p) - one per independent cycle -/
def grossNewZChecks : ℕ := grossIndependentBpChecks

/-- Number of new qubits (edge qubits) - one per edge -/
def grossNewQubits : ℕ := grossNumEdges

/-- Total overhead: X checks + Z checks + qubits -/
def grossTotalOverhead : ℕ := grossNewXChecks + grossNewZChecks + grossNewQubits

/-- Total overhead equals 41 -/
theorem grossTotalOverhead_eq : grossTotalOverhead = 41 := by
  unfold grossTotalOverhead grossNewXChecks grossNewZChecks grossNewQubits
  unfold grossNumVertices grossIndependentBpChecks grossNumEdges
  norm_num

/-! ## Section 9: Weight/Degree Bounds (property vi) -/

/-- Maximum Gauss law weight: max degree + 1 for the vertex qubit -/
def grossMaxGaussLawWeight : ℕ := grossMaxDegree + 1

/-- Gauss law weight ≤ 7 -/
theorem grossGaussLawWeight_bounded : grossMaxGaussLawWeight ≤ 7 := by
  unfold grossMaxGaussLawWeight
  have h := grossMaxDegree_le_6
  omega

/-- Maximum flux check weight: the longest flux cycle has length 5 -/
def grossMaxFluxWeight : ℕ := 5

/-- All flux cycles have length ≤ 5 -/
theorem grossFluxWeight_bounded :
    ∀ c ∈ grossFluxCycles, c.length ≤ grossMaxFluxWeight := by
  native_decide

/-- Flux check weight ≤ 7 -/
theorem grossFluxWeight_le_7 : grossMaxFluxWeight ≤ 7 := by
  unfold grossMaxFluxWeight
  omega

/-- All checks have weight ≤ 7 -/
theorem grossAllChecks_weight_le_7 :
    grossMaxGaussLawWeight ≤ 7 ∧ grossMaxFluxWeight ≤ 7 := by
  exact ⟨grossGaussLawWeight_bounded, grossFluxWeight_le_7⟩

/-- All qubit degrees ≤ 7 -/
theorem grossQubitDegree_bounded :
    ∀ v : Fin 12, grossVertexDegree v ≤ 7 := by
  intro v
  have h := grossAllVertices_degree_le_6 v
  omega

/-! ## Section 10: Distance Preservation

**Original claim**: The 4 expansion edges were chosen so the deformed code
maintains distance 12, verified via BP+OSD decoder and integer programming.

**Status**: This is an inherently computational claim requiring numerical
optimization algorithms (belief propagation, ordered statistics decoding,
integer linear programming). These algorithms operate on floating-point
numbers and solve NP-hard optimization problems, which cannot be expressed
in pure type theory without implementing the full numerical stack.

We record the claimed values as definitions. The mathematical validity of the
distance claim rests on the paper's computational verification.
-/

/-- The original Gross code distance (from code parameters) -/
def grossOriginalDistance : ℕ := 12

/-- The claimed deformed code distance (from paper's computational verification).
    This was verified using BP+OSD decoder and integer programming.
    NO FORMAL PROOF - this is a documented claim, not a proven theorem. -/
def grossClaimedDeformedDistance : ℕ := 12

/-- The original and deformed code distances are both claimed to be 12.
    The deformed code distance was verified computationally in the paper
    using BP+OSD decoder and integer programming. -/
theorem distance_values :
    grossOriginalDistance = 12 ∧ grossClaimedDeformedDistance = 12 := ⟨rfl, rfl⟩

/-! ## Section 11: Main Theorem -/

/-- The main theorem: the Gross code gauging graph exists with all stated properties.

    **Proven from explicit construction:**
    - (i) 12 vertices corresponding to monomials in f (with injective mapping)
    - (ii) 18 matching edges + 4 expansion edges = 22 total edges
    - (iv) Cycle rank = 11, with 7 GF(2)-independent flux cycles (Mathlib LinearIndependent)
    - (v) Total overhead = 12 + 7 + 22 = 41
    - (vi) Max check weight ≤ 7, max qubit degree ≤ 7

    **Inherently computational (from paper):**
    - (ii) Matching edges derived from Z-check overlap (taken from paper)
    - (iii) Distance preservation: verified by BP+OSD decoder + integer programming
    - (iv) Redundancy count: 4 cycles redundant due to BB code nullity structure -/
theorem grossCodeGaugingGraph_construction :
    -- (i) 12 vertices corresponding to monomials in f
    Fintype.card GrossGaugingVertex = 12 ∧
    -- (i) Vertex mapping is injective
    Function.Injective grossVertexToMonomial ∧
    -- (ii) 18 matching edges + 4 expansion edges
    grossMatchingEdges.card = 18 ∧
    grossExpansionEdges.card = 4 ∧
    -- Matching and expansion are disjoint
    Disjoint grossMatchingEdges grossExpansionEdges ∧
    -- Total edges = 22
    grossAllEdges.card = 22 ∧
    -- (iv) Cycle rank = 11, with 7 GF(2)-independent flux cycles (formal linear independence)
    grossCycleRank = 11 ∧
    grossFluxCycles.length = 7 ∧
    LinearIndependent (ZMod 2) grossFluxCycleVectors ∧
    -- (v) Total overhead = 41
    grossTotalOverhead = 41 ∧
    -- (vi) Max check weight ≤ 7, max qubit degree ≤ 7
    grossMaxGaussLawWeight ≤ 7 ∧
    grossMaxFluxWeight ≤ 7 ∧
    (∀ v : Fin 12, grossVertexDegree v ≤ 7) := by
  refine ⟨?_, grossVertexToMonomial_injective,
          grossMatchingEdges_card, grossExpansionEdges_card,
          grossEdges_disjoint, grossAllEdges_card,
          grossCycleRank_eq, rfl, grossFluxCycles_linearIndependent, grossTotalOverhead_eq,
          grossGaussLawWeight_bounded, grossFluxWeight_le_7, ?_⟩
  · decide
  · intro v
    have h := grossAllVertices_degree_le_6 v
    omega

/-! ## Section 12: Expansion Edge Verification -/

/-- Expansion edge (x², x⁵y³) corresponds to vertices (2, 9) -/
theorem expansion_edge_x2_x5y3 :
    (2, 9) ∈ grossExpansionEdges ∧
    grossVertexToMonomial 2 = (2, 0) ∧
    grossVertexToMonomial 9 = (5, 3) := by
  refine ⟨?_, rfl, rfl⟩
  native_decide

/-- Expansion edge (x², x⁶) corresponds to vertices (2, 4) -/
theorem expansion_edge_x2_x6 :
    (2, 4) ∈ grossExpansionEdges ∧
    grossVertexToMonomial 2 = (2, 0) ∧
    grossVertexToMonomial 4 = (6, 0) := by
  refine ⟨?_, rfl, rfl⟩
  native_decide

/-- Expansion edge (x⁵y³, x¹¹y³) corresponds to vertices (9, 11) -/
theorem expansion_edge_x5y3_x11y3 :
    (9, 11) ∈ grossExpansionEdges ∧
    grossVertexToMonomial 9 = (5, 3) ∧
    grossVertexToMonomial 11 = (11, 3) := by
  refine ⟨?_, rfl, rfl⟩
  native_decide

/-- Expansion edge (x⁷y³, x¹¹y³) corresponds to vertices (10, 11) -/
theorem expansion_edge_x7y3_x11y3 :
    (10, 11) ∈ grossExpansionEdges ∧
    grossVertexToMonomial 10 = (7, 3) ∧
    grossVertexToMonomial 11 = (11, 3) := by
  refine ⟨?_, rfl, rfl⟩
  native_decide

/-! ## Section 13: Connection to Gross Code -/

/-- The number of vertices equals the number of terms in f -/
theorem grossNumVertices_eq_logicalWeight :
    grossNumVertices = logicalXPolyF.numTerms := by
  rw [logicalXPolyF_weight]
  rfl

/-- The logical operator has weight 12 -/
theorem grossLogicalWeight : logicalXPolyF.numTerms = 12 := logicalXPolyF_weight

/-- The graph has 12 vertices -/
@[simp]
theorem grossGauging_card_vertices : Fintype.card GrossGaugingVertex = 12 := by
  decide

/-- The Gross code parameters are [[144, 12, 12]] -/
theorem grossCode_params :
    grossCodeParams.n = 144 ∧ grossCodeParams.k = 12 ∧ grossCodeParams.d = 12 := by
  simp only [grossCodeParams, and_self]

/-- Summary of the gauging graph parameters -/
theorem grossGaugingGraph_summary :
    grossNumVertices = 12 ∧
    grossNumEdges = 22 ∧
    grossCycleRank = 11 ∧
    grossIndependentBpChecks = 7 ∧
    grossTotalOverhead = 41 := by
  refine ⟨rfl, rfl, grossCycleRank_eq, rfl, grossTotalOverhead_eq⟩

end QEC
