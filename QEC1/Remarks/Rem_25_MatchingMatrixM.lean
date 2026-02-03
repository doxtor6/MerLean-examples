import QEC1.Definitions.Def_9_DeformedCheck
import QEC1.Definitions.Def_21_TannerGraph
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matching Matrix M (Remark 25)

## Statement
The **matching matrix** M in the deformed code Tanner graph (Figure 1) encodes how original
checks are deformed by paths in G.

**Structure**: M is a binary matrix with:
- Rows indexed by checks in S (checks with Z-support on L)
- Columns indexed by edges in G
- M_{j,e} = 1 iff edge e is in the deforming path γ_j for check s_j

**Optimization goal**: Choose paths {γ_j} to minimize:
- Row weight of M (path lengths)
- Column weight of M (edge participation in multiple paths)

**Perfect matching approach**: When |S_{Z,j} ∩ V| = 2 for all checks s_j ∈ S,
a Z₂-perfect-matching ensures each row of M has weight 1.

## Main Results
**Main Structure** (`MatchingMatrix`): Binary matrix encoding check-to-edge relationships
**Row Weight** (`rowWeight`): Number of edges in a check's path (path length)
**Column Weight** (`colWeight`): Number of checks using an edge
**Perfect Matching** (`isPerfectMatching`): Each row has weight exactly 1
**Optimization** (`optimizationGoal`): Minimize total row and column weights

## File Structure
1. Type S Checks: Checks with Z-support on L (need nontrivial paths)
2. Matching Matrix Definition: Binary matrix M encoding paths
3. Row and Column Weights: Path lengths and edge participation counts
4. Optimization Goals: Minimization objectives
5. Perfect Matching: Special case when |S_{Z,j} ∩ V| = 2
6. Helper Lemmas: Basic properties
-/

namespace QEC

open Matrix

variable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}

/-! ## Section 1: Type S Checks (Checks with Z-support on L)

The set S consists of checks s_j where S_{Z,j} ∩ L ≠ ∅.
These are the checks that require nontrivial deforming paths γ_j.
-/

/-- The set of Type S check indices: checks with Z-support on the logical operator L.
    These are the rows of the matching matrix M. -/
def typeSCheckIndices (L : XTypeLogical C) : Finset (Fin (n - k)) :=
  Finset.filter (fun j => (C.checks j).supportZ ∩ L.support ≠ ∅) Finset.univ

/-- Cardinality of Type S checks -/
def numTypeSChecks (L : XTypeLogical C) : ℕ := (typeSCheckIndices L).card

/-! ## Section 2: Matching Matrix Definition

The matching matrix M is a binary matrix where:
- Rows are indexed by Type S checks (checks in S)
- Columns are indexed by edges in the gauging graph G
- M_{j,e} = 1 iff edge e is in the deforming path γ_j for check s_j
-/

/-- A matching matrix configuration specifying which edges are used by which checks.
    This encodes the paths γ_j chosen for each Type S check s_j.

    We use a simpler representation where each check maps to its edge set directly,
    avoiding dependent types in the edge membership. -/
structure MatchingMatrixConfig (n k : ℕ) (C : StabilizerCode n k)
    (L : XTypeLogical C) (G : GaugingGraph C L) where
  /-- The set of Type S check indices (row indices) -/
  typeSChecks : Finset (Fin (n - k))
  /-- For each check, the set of edges in its deforming path (empty if not Type S) -/
  checkPathSet : Fin (n - k) → Finset (Sym2 G.Vertex)
  /-- Only Type S checks have nonempty paths -/
  nonTypeS_empty : ∀ j, j ∉ typeSChecks → checkPathSet j = ∅
  /-- All edges in paths are valid graph edges -/
  pathEdgesValid : ∀ j (e : Sym2 G.Vertex), e ∈ checkPathSet j → e ∈ G.graph.edgeSet

namespace MatchingMatrixConfig

variable {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)

/-- Get the entry M_{j,e}: 1 if edge e is in path γ_j, 0 otherwise -/
def entry (j : Fin (n - k)) (e : Sym2 G.Vertex) : ZMod 2 :=
  if e ∈ M.checkPathSet j then 1 else 0

/-- Entry is 1 iff edge is in the path -/
theorem entry_eq_one_iff (j : Fin (n - k)) (e : Sym2 G.Vertex) :
    M.entry j e = 1 ↔ e ∈ M.checkPathSet j := by
  unfold entry
  constructor
  · intro h
    by_cases he : e ∈ M.checkPathSet j
    · exact he
    · simp only [he, ↓reduceIte] at h
      exact absurd h (by decide)
  · intro h
    simp only [h, ↓reduceIte]

/-- Entry is 0 iff edge is not in the path -/
theorem entry_eq_zero_iff (j : Fin (n - k)) (e : Sym2 G.Vertex) :
    M.entry j e = 0 ↔ e ∉ M.checkPathSet j := by
  unfold entry
  constructor
  · intro h
    by_cases he : e ∈ M.checkPathSet j
    · simp only [he, ↓reduceIte] at h
      exact absurd h (by decide)
    · exact he
  · intro h
    simp only [h, ↓reduceIte]

end MatchingMatrixConfig

/-! ## Section 3: Row Weight (Path Length)

The row weight of M at row j equals the number of edges in γ_j,
which is the length of the deforming path for check s_j.
-/

/-- Row weight: number of edges in the path for check j -/
def MatchingMatrixConfig.rowWeight {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (j : Fin (n - k)) : ℕ :=
  (M.checkPathSet j).card

/-- Row weight equals path length -/
theorem MatchingMatrixConfig.rowWeight_eq_pathLength {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (j : Fin (n - k)) :
    M.rowWeight j = (M.checkPathSet j).card := rfl

/-- Row weight for non-Type S check is zero -/
theorem MatchingMatrixConfig.rowWeight_nonTypeS {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (j : Fin (n - k)) (hj : j ∉ M.typeSChecks) :
    M.rowWeight j = 0 := by
  unfold rowWeight
  rw [M.nonTypeS_empty j hj]
  rfl

/-! ## Section 4: Column Weight (Edge Participation)

The column weight of M at column e equals the number of checks whose paths contain e.
This measures how many deforming paths pass through edge e.
-/

/-- Column weight: number of checks whose path contains edge e -/
def MatchingMatrixConfig.colWeight {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (e : Sym2 G.Vertex) : ℕ :=
  (Finset.filter (fun j => e ∈ M.checkPathSet j) Finset.univ).card

/-- Column weight counts checks using the edge -/
theorem MatchingMatrixConfig.colWeight_eq {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (e : Sym2 G.Vertex) :
    M.colWeight e = (Finset.filter (fun j => e ∈ M.checkPathSet j) Finset.univ).card := rfl

/-- Column weight only counts Type S checks (since others have empty paths) -/
theorem MatchingMatrixConfig.colWeight_typeS_only {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (e : Sym2 G.Vertex) :
    M.colWeight e = (M.typeSChecks.filter (fun j => e ∈ M.checkPathSet j)).card := by
  unfold colWeight
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro he
    constructor
    · by_contra hj
      have h := M.nonTypeS_empty j hj
      rw [h] at he
      exact Finset.notMem_empty e he
    · exact he
  · intro ⟨_, he⟩
    exact he

/-! ## Section 5: Optimization Goals

The optimization goal is to choose paths {γ_j} to minimize:
1. Total row weight = Σ_j |γ_j| (sum of path lengths)
2. Maximum column weight = max_e |{j : e ∈ γ_j}| (max edge participation)
-/

/-- Total row weight: sum of all path lengths -/
def MatchingMatrixConfig.totalRowWeight {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) : ℕ :=
  M.typeSChecks.sum (fun j => M.rowWeight j)

/-- Maximum column weight across all edges -/
noncomputable def MatchingMatrixConfig.maxColWeight {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) : ℕ :=
  if h : G.graph.edgeFinset.Nonempty then
    G.graph.edgeFinset.sup' h (fun e => M.colWeight e)
  else 0

/-- Optimization goal structure -/
structure OptimizationGoal where
  /-- Target maximum row weight (path length bound) -/
  maxRowWeight : ℕ
  /-- Target maximum column weight (edge participation bound) -/
  maxColWeight : ℕ

/-- A matching matrix satisfies the optimization goal -/
def MatchingMatrixConfig.satisfiesGoal {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (goal : OptimizationGoal) : Prop :=
  (∀ j ∈ M.typeSChecks, M.rowWeight j ≤ goal.maxRowWeight) ∧
  (∀ e, M.colWeight e ≤ goal.maxColWeight)

/-! ## Section 6: Perfect Matching Case

When |S_{Z,j} ∩ V| = 2 for all Type S checks s_j, a Z₂-perfect-matching approach
can ensure each row of M has weight exactly 1. This means each check's path
consists of a single edge connecting its two boundary vertices.
-/

/-- The Z-support size on vertices for a check
    (counting qubits in Z-support that are in L.support) -/
def checkZSupportOnV (j : Fin (n - k)) : ℕ :=
  ((C.checks j).supportZ ∩ L.support).card

/-- Condition: all Type S checks have exactly 2 vertices in Z-support ∩ V -/
def allTypeSHaveTwoVertices : Prop :=
  ∀ j ∈ typeSCheckIndices L, checkZSupportOnV (L := L) j = 2

/-- A matching matrix is a perfect matching if each Type S row has weight exactly 1 -/
def MatchingMatrixConfig.isPerfectMatching {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) : Prop :=
  ∀ j ∈ M.typeSChecks, M.rowWeight j = 1

/-- Perfect matching implies each path is a single edge -/
theorem MatchingMatrixConfig.perfectMatching_single_edge {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (hpm : M.isPerfectMatching)
    (j : Fin (n - k)) (hj : j ∈ M.typeSChecks) :
    (M.checkPathSet j).card = 1 := by
  unfold isPerfectMatching rowWeight at hpm
  exact hpm j hj

/-- For perfect matching, the total row weight equals the number of Type S checks -/
theorem MatchingMatrixConfig.perfectMatching_totalWeight {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (hpm : M.isPerfectMatching) :
    M.totalRowWeight = M.typeSChecks.card := by
  unfold totalRowWeight
  have h : ∀ j ∈ M.typeSChecks, M.rowWeight j = 1 := hpm
  calc M.typeSChecks.sum (fun j => M.rowWeight j)
      = M.typeSChecks.sum (fun _ => 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact h j hj
    _ = M.typeSChecks.card := by
        simp only [Finset.sum_const, smul_eq_mul, mul_one]

/-! ## Section 7: Binary Matrix Representation

We can represent M as an actual Mathlib Matrix over ZMod 2.
-/

/-- The matching matrix M as a Mathlib Matrix.
    Rows are indexed by all checks, columns by a given edge set. -/
def matchingMatrixOfConfig {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (edges : Finset (Sym2 G.Vertex)) :
    Matrix (Fin (n - k)) edges (ZMod 2) :=
  fun j ⟨e, _⟩ => M.entry j e

/-- Matrix entry matches configuration entry -/
theorem matchingMatrix_entry {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (edges : Finset (Sym2 G.Vertex)) (j : Fin (n - k)) (e : edges) :
    matchingMatrixOfConfig M edges j e = M.entry j e.1 := rfl

/-! ## Section 8: Row and Column Weight as Matrix Operations

The row and column weights can be expressed using matrix operations.
-/

/-- Row weight as cardinality of support in that row -/
theorem rowWeight_as_support {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (j : Fin (n - k)) :
    M.rowWeight j = (M.checkPathSet j).card := rfl

/-- Column weight counts checks using the edge -/
theorem colWeight_counts_checks {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (e : Sym2 G.Vertex) :
    M.colWeight e = (Finset.filter (fun j => e ∈ M.checkPathSet j) Finset.univ).card := rfl

/-! ## Section 9: Empty and Trivial Configurations -/

/-- Empty configuration when there are no Type S checks -/
def emptyMatchingConfig (G : GaugingGraph C L) : MatchingMatrixConfig n k C L G where
  typeSChecks := ∅
  checkPathSet := fun _ => ∅
  nonTypeS_empty := fun _ _ => rfl
  pathEdgesValid := fun _ e he => absurd he (Finset.notMem_empty e)

/-- Empty configuration has no rows -/
theorem emptyMatchingConfig_noRows (G : GaugingGraph C L) :
    (emptyMatchingConfig G).typeSChecks = ∅ := rfl

/-- Empty configuration has total row weight 0 -/
theorem emptyMatchingConfig_totalWeight (G : GaugingGraph C L) :
    (emptyMatchingConfig G).totalRowWeight = 0 := by
  unfold MatchingMatrixConfig.totalRowWeight emptyMatchingConfig
  simp only [Finset.sum_empty]

/-- Empty configuration has all row weights 0 -/
theorem emptyMatchingConfig_rowWeight (G : GaugingGraph C L) (j : Fin (n - k)) :
    (emptyMatchingConfig G).rowWeight j = 0 := by
  unfold MatchingMatrixConfig.rowWeight emptyMatchingConfig
  rfl

/-- Empty configuration has all column weights 0 -/
theorem emptyMatchingConfig_colWeight (G : GaugingGraph C L) (e : Sym2 G.Vertex) :
    (emptyMatchingConfig G).colWeight e = 0 := by
  unfold MatchingMatrixConfig.colWeight emptyMatchingConfig
  simp only [Finset.notMem_empty, Finset.filter_false, Finset.card_empty]

/-! ## Section 10: Bounds on Weights

Upper bounds on row and column weights relate to path lengths and graph degree.
-/

/-- If all rows have weight at most κ, total weight is at most κ × number of rows -/
theorem totalRowWeight_bound {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G) (κ : ℕ)
    (hrow : ∀ j ∈ M.typeSChecks, M.rowWeight j ≤ κ) :
    M.totalRowWeight ≤ κ * M.typeSChecks.card := by
  unfold MatchingMatrixConfig.totalRowWeight
  calc M.typeSChecks.sum (fun j => M.rowWeight j)
      ≤ M.typeSChecks.sum (fun _ => κ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hrow j hj
    _ = κ * M.typeSChecks.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Perfect matching achieves optimal row weight bound -/
theorem perfectMatching_optimal_rowWeight {G : GaugingGraph C L}
    (M : MatchingMatrixConfig n k C L G) (hpm : M.isPerfectMatching) :
    M.totalRowWeight ≤ 1 * M.typeSChecks.card := by
  apply totalRowWeight_bound
  intro j hj
  rw [hpm j hj]

/-! ## Section 11: Helper Lemmas -/

/-- Type S check indices are exactly those with nonempty Z-support intersection with L -/
@[simp]
theorem mem_typeSCheckIndices (j : Fin (n - k)) :
    j ∈ typeSCheckIndices L ↔ (C.checks j).supportZ ∩ L.support ≠ ∅ := by
  unfold typeSCheckIndices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Number of Type S checks is at most total number of checks -/
theorem numTypeSChecks_le (L : XTypeLogical C) :
    numTypeSChecks L ≤ n - k := by
  unfold numTypeSChecks typeSCheckIndices
  calc (Finset.filter (fun j => (C.checks j).supportZ ∩ L.support ≠ ∅) Finset.univ).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card (Fin (n - k)) := Finset.card_univ
    _ = n - k := Fintype.card_fin _

/-- Row weight is nonnegative (trivially true for ℕ) -/
theorem rowWeight_nonneg {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (j : Fin (n - k)) :
    M.rowWeight j ≥ 0 := Nat.zero_le _

/-- Column weight is nonnegative (trivially true for ℕ) -/
theorem colWeight_nonneg {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (e : Sym2 G.Vertex) :
    M.colWeight e ≥ 0 := Nat.zero_le _

/-- For a perfect matching, row weight of Type S check is exactly 1 -/
@[simp]
theorem perfectMatching_rowWeight {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (hpm : M.isPerfectMatching) (j : Fin (n - k)) (hj : j ∈ M.typeSChecks) :
    M.rowWeight j = 1 := hpm j hj

/-- Entry of a non-Type S check row is always 0 -/
theorem entry_nonTypeS_zero {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (j : Fin (n - k)) (hj : j ∉ M.typeSChecks) (e : Sym2 G.Vertex) :
    M.entry j e = 0 := by
  rw [M.entry_eq_zero_iff]
  have h := M.nonTypeS_empty j hj
  rw [h]
  exact Finset.notMem_empty e

/-- Perfect matching with k Type S checks has total weight k -/
theorem perfectMatching_total_eq_card {G : GaugingGraph C L} (M : MatchingMatrixConfig n k C L G)
    (hpm : M.isPerfectMatching) :
    M.totalRowWeight = M.typeSChecks.card := M.perfectMatching_totalWeight hpm

end QEC
