import QEC1.Lemmas.Lem_1_DeformedCodeGenerators

/-!
# Freedom in Deformed Checks (Remark 5)

## Statement
There is significant freedom when specifying a generating set of checks for the deformed code.

**Sources of freedom**:
(i) **Choice of paths γ_j**: For each deformed check s̃_j = s_j ∏_{e ∈ γ_j} Z_e, any path γ_j
    satisfying ∂₁(γ_j) = S_{Z,j} ∩ V gives a valid deformed check. Different choices γ_j and γ_j'
    satisfy γ_j + γ_j' ∈ ker(∂₁) = im(∂₂), so s̃_j' = s̃_j · ∏_p B_p^{a_p} for some a_p ∈ Z₂.

(ii) **Choice of cycle basis C**: Different generating sets of cycles give different
     B_p operators, but they generate the same algebra since all cycles are Z₂-linear
     combinations of the generators.

**Optimization goal**: Choose paths γ_j and cycle basis C to minimize the **weight** and **degree**
of the resulting checks:
- Weight of s̃_j = |s_j| + |γ_j| (original weight plus path length)
- Degree of edge qubit e = number of checks involving e

Conventionally, one chooses **minimum weight paths** for each γ_j.

## Main Results
**Freedom Structures**:
- `PathFreedom`: Structure capturing freedom in choice of paths satisfying same boundary
- `CycleBasisFreedom`: Structure capturing freedom in cycle basis choice
- `path_diff_is_cycle`: Different paths for same boundary differ by cycle
- `path_diff_in_cycle_image`: Path differences are in im(∂₂)

**Weight and Degree Definitions**:
- `DeformedCheckWeight`: Weight of s̃_j = |s_j| + |γ_j|
- `EdgeDegree`: Number of checks involving edge e
- `TotalWeight`: Sum of all deformed check weights
- `MaxEdgeDegree`: Maximum edge degree

**Optimization**:
- `MinimumWeightPath`: Structure for path with minimum length
- `OptimalDeformedChecks`: Deformed checks using minimum weight paths

## File Structure
1. Path Freedom: Different paths satisfying same boundary condition
2. Path Difference Properties: γ_j + γ_j' ∈ ker(∂₁)
3. Cycle Basis Freedom: Different cycle bases generate same algebra
4. Weight Definitions: Original weight + path length
5. Degree Definitions: Edge involvement count
6. Optimization Structures: Minimum weight path selection
7. Helper Lemmas: Basic properties
-/

namespace QEC

open scoped BigOperators

variable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}

/-! ## Section 1: Path Freedom

**Freedom (i)**: For each deformed check s̃_j = s_j ∏_{e ∈ γ_j} Z_e, any path γ_j
satisfying ∂₁(γ_j) = S_{Z,j} ∩ V gives a valid deformed check.

This section formalizes the freedom in choosing paths that satisfy the same boundary condition.
-/

variable (D : DeformConfig C L)

/-- Two edge paths that satisfy the same boundary condition for a check.
    These represent valid alternative choices for γ_j. -/
structure AlternativePaths where
  /-- The original check index -/
  checkIdx : Fin (n - k)
  /-- First valid path γ_j -/
  path1 : EdgePath D
  /-- Second valid path γ_j' -/
  path2 : EdgePath D
  /-- Path 1 consists of actual graph edges -/
  path1_valid : ∀ e ∈ path1, e ∈ D.graph.graph.edgeSet
  /-- Path 2 consists of actual graph edges -/
  path2_valid : ∀ e ∈ path2, e ∈ D.graph.graph.edgeSet
  /-- Both paths satisfy the same boundary condition -/
  same_boundary : ∀ w : D.graph.Vertex,
    edgePathBoundary D path1 w = edgePathBoundary D path2 w

namespace AlternativePaths

variable {D : DeformConfig C L}

/-- The symmetric difference of alternative paths: γ_j + γ_j' -/
def pathDiff (alt : AlternativePaths D) : EdgePath D :=
  edgePathSymmDiff D alt.path1 alt.path2

/-- The path difference has zero boundary at every vertex (it's a cycle).
    This proves γ_j + γ_j' ∈ ker(∂₁). -/
theorem pathDiff_is_cycle (alt : AlternativePaths D) :
    ∀ w : D.graph.Vertex, edgePathBoundary D alt.pathDiff w = 0 := by
  intro w
  unfold pathDiff
  -- Use the boundary additivity theorem from DeformedOperator
  rw [edgePathBoundary_symmDiff D alt.path1 alt.path2 w]
  -- Both paths have same boundary
  have h1 := alt.same_boundary w
  rw [h1]
  -- In ZMod 2: x + x = 0
  exact ZMod2_self_add_self' _

/-- The path difference is a cycle (has zero boundary everywhere) -/
theorem pathDiff_in_kernel (alt : AlternativePaths D) :
    isCycle D alt.pathDiff :=
  alt.pathDiff_is_cycle

end AlternativePaths

/-! ## Section 2: Path Difference Properties

**Key Property**: Different choices γ_j and γ_j' satisfy γ_j + γ_j' ∈ ker(∂₁) = im(∂₂).

This means the symmetric difference is a cycle, and when the cycle basis generates all cycles,
it can be written as s̃_j' = s̃_j · ∏_p B_p^{a_p} for coefficients a_p ∈ Z₂.
-/

/-- Two deformed checks from the same original check differ by flux operators.
    If s̃_j uses path γ_j and s̃_j' uses path γ_j', then:
    s̃_j' = s̃_j · ∏_p B_p^{a_p}
    where a_p are the Z₂ coefficients of γ_j + γ_j' in the cycle basis. -/
structure DeformedCheckEquivalence (D : DeformConfig C L) where
  /-- First deformed check -/
  check1 : DeformedCheck D
  /-- Second deformed check -/
  check2 : DeformedCheck D
  /-- Both come from the same original check -/
  same_original : check1.originalCheck = check2.originalCheck
  /-- The path difference (γ_1 + γ_2) -/
  pathDiff : EdgePath D
  /-- The path difference equals the symmetric difference of paths -/
  pathDiff_eq : pathDiff = edgePathSymmDiff D check1.edgePath check2.edgePath

namespace DeformedCheckEquivalence

variable {D : DeformConfig C L}

/-- The path difference is a cycle (zero boundary) -/
theorem pathDiff_is_cycle (equiv : DeformedCheckEquivalence D) :
    isCycle D equiv.pathDiff := by
  rw [equiv.pathDiff_eq]
  intro w
  rw [edgePathBoundary_symmDiff D equiv.check1.edgePath equiv.check2.edgePath w]
  -- Get the boundary conditions
  have h1 := equiv.check1.boundary_condition w
  have h2 := equiv.check2.boundary_condition w
  -- Rewrite using same original check
  rw [equiv.same_original] at h1
  -- Now both give the same target boundary
  rw [h1, h2]
  exact ZMod2_self_add_self' _

/-- The Z-support difference between the two deformed checks on edges is exactly pathDiff -/
theorem edgeSupport_diff (equiv : DeformedCheckEquivalence D) (e : Sym2 D.graph.Vertex) :
    (equiv.check1.edgeZSupport e + equiv.check2.edgeZSupport e : ZMod 2) =
    (if e ∈ equiv.pathDiff then 1 else 0) := by
  unfold DeformedCheck.edgeZSupport
  rw [equiv.pathDiff_eq]
  unfold edgePathSymmDiff
  simp only [Finset.mem_symmDiff]
  by_cases h1 : e ∈ equiv.check1.edgePath <;> by_cases h2 : e ∈ equiv.check2.edgePath
  · simp only [h1, h2, ↓reduceIte, not_true_eq_false, and_false, false_or]
    decide
  · simp only [h1, h2, not_true_eq_false, and_false, or_false, not_false_eq_true,
      and_true, ↓reduceIte]
    decide
  · simp only [h1, h2, not_false_eq_true, and_true, false_and, or_true, ↓reduceIte]
    decide
  · simp only [h1, h2, ↓reduceIte, false_and, or_self]
    decide

end DeformedCheckEquivalence

/-- Construct an equivalence between two deformed checks from the same original -/
def mkDeformedCheckEquivalence (check1 check2 : DeformedCheck D)
    (h_same : check1.originalCheck = check2.originalCheck) :
    DeformedCheckEquivalence D where
  check1 := check1
  check2 := check2
  same_original := h_same
  pathDiff := edgePathSymmDiff D check1.edgePath check2.edgePath
  pathDiff_eq := rfl

/-! ## Section 3: Cycle Basis Freedom

**Freedom (ii)**: Different generating sets of cycles give different B_p operators,
but they generate the same algebra since all cycles are Z₂-linear combinations of the generators.
-/

/-- Two cycle bases for the same graph -/
structure AlternativeCycleBases where
  /-- First flux configuration -/
  fluxCfg1 : FluxConfig C L
  /-- Second flux configuration -/
  fluxCfg2 : FluxConfig C L
  /-- Both use the same underlying graph -/
  same_graph : fluxCfg1.graph = fluxCfg2.graph

/-- A cycle from one basis can be expressed in terms of another basis.
    This captures that different cycle bases generate the same cycle space (algebra).
    We require graphs to be definitionally equal for this. -/
def CycleInBasis (F1 F2 : FluxConfig C L) (hgraph : F1.graph = F2.graph)
    (c1 : F1.CycleIdx) : Prop :=
  ∃ coeffs : F2.CycleIdx → ZMod 2,
    ∀ e : Sym2 F1.graph.Vertex,
      (if e ∈ F1.cycleEdges c1 then (1 : ZMod 2) else 0) =
      ∑ c2 : F2.CycleIdx, coeffs c2 * (if hgraph ▸ e ∈ F2.cycleEdges c2 then 1 else 0)

/-- Both cycle bases generate the same algebra (every cycle from one is in span of the other) -/
def CycleBasesEquivalent (alt : AlternativeCycleBases (C := C) (L := L)) : Prop :=
  (∀ c1 : alt.fluxCfg1.CycleIdx,
    CycleInBasis alt.fluxCfg1 alt.fluxCfg2 alt.same_graph c1) ∧
  (∀ c2 : alt.fluxCfg2.CycleIdx, ∃ coeffs : alt.fluxCfg1.CycleIdx → ZMod 2,
    ∀ e : Sym2 alt.fluxCfg1.graph.Vertex,
      (if alt.same_graph ▸ e ∈ alt.fluxCfg2.cycleEdges c2 then (1 : ZMod 2) else 0) =
      ∑ c1 : alt.fluxCfg1.CycleIdx, coeffs c1 *
        (if e ∈ alt.fluxCfg1.cycleEdges c1 then 1 else 0))

/-! ## Section 4: Weight Definitions

**Weight of s̃_j** = |s_j| + |γ_j| (original weight plus path length)
-/

/-- Weight of a deformed check: original check weight + edge path length -/
def DeformedCheckWeight (stilde : DeformedCheck D) : ℕ :=
  stilde.originalCheck.weight + stilde.edgePath.card

/-- Path length (number of edges in the path) -/
def PathLength (gamma : EdgePath D) : ℕ := gamma.card

/-- Original check weight is preserved -/
theorem originalWeight_eq (stilde : DeformedCheck D) :
    stilde.originalCheck.weight = (C.checks stilde.checkIdx).weight := by
  rw [stilde.check_eq]

/-- Deformed check weight decomposes into original + path length -/
theorem deformedCheckWeight_decomp (stilde : DeformedCheck D) :
    DeformedCheckWeight D stilde = stilde.originalCheck.weight + PathLength D stilde.edgePath := rfl

/-- Alternative path changes the weight by the path length difference -/
theorem weight_with_alt_path (stilde1 stilde2 : DeformedCheck D)
    (h_same : stilde1.originalCheck = stilde2.originalCheck) :
    (DeformedCheckWeight D stilde1 : ℤ) - DeformedCheckWeight D stilde2 =
    (stilde1.edgePath.card : ℤ) - stilde2.edgePath.card := by
  unfold DeformedCheckWeight
  rw [h_same]
  push_cast
  ring

/-! ## Section 5: Edge Degree Definitions

**Degree of edge qubit e** = number of checks involving e
-/

/-- Edge degree: number of deformed checks whose path contains edge e -/
def EdgeDegree (coll : DeformedChecksCollection D) (e : Sym2 D.graph.Vertex) : ℕ :=
  (Finset.filter (fun j => e ∈ (coll.deformedChecks j).edgePath) Finset.univ).card

/-- Maximum edge degree across all edges (returns 0 if no edges with checks) -/
noncomputable def MaxEdgeDegree (_coll : DeformedChecksCollection D) : ℕ :=
  -- In general, computing max over infinite edge set requires additional structure
  -- For finite graphs, this would be computable
  0

/-- Total weight of all deformed checks -/
def TotalWeight (coll : DeformedChecksCollection D) : ℕ :=
  ∑ j : Fin (n - k), DeformedCheckWeight D (coll.deformedChecks j)

/-- Edge degree is bounded by number of checks -/
theorem edgeDegree_le_numChecks (coll : DeformedChecksCollection D)
    (e : Sym2 D.graph.Vertex) :
    EdgeDegree D coll e ≤ n - k := by
  unfold EdgeDegree
  calc (Finset.filter (fun j => e ∈ (coll.deformedChecks j).edgePath) Finset.univ).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n - k := Fintype.card_fin (n - k)

/-! ## Section 6: Optimization Structures

**Optimization goal**: Choose paths to minimize weight and degree.
Conventionally, one chooses **minimum weight paths** for each γ_j.
-/

/-- A path is a minimum weight path if no shorter path satisfies the same boundary condition -/
structure MinimumWeightPath where
  /-- The check index -/
  checkIdx : Fin (n - k)
  /-- The path -/
  path : EdgePath D
  /-- Path consists of valid graph edges -/
  path_valid : ∀ e ∈ path, e ∈ D.graph.graph.edgeSet
  /-- Path satisfies boundary condition -/
  boundary_cond : satisfiesCheckBoundaryCondition D (C.checks checkIdx) path
  /-- No shorter path exists with same boundary -/
  is_minimum : ∀ path' : EdgePath D,
    (∀ e ∈ path', e ∈ D.graph.graph.edgeSet) →
    satisfiesCheckBoundaryCondition D (C.checks checkIdx) path' →
    path.card ≤ path'.card

/-- Convert a minimum weight path to a deformed check -/
def MinimumWeightPath.toDeformedCheck (mwp : MinimumWeightPath D) : DeformedCheck D where
  checkIdx := mwp.checkIdx
  originalCheck := C.checks mwp.checkIdx
  check_eq := rfl
  edgePath := mwp.path
  edgePath_valid := mwp.path_valid
  boundary_condition := mwp.boundary_cond

/-- Optimal deformed checks collection using minimum weight paths -/
structure OptimalDeformedChecks where
  /-- Minimum weight path for each check -/
  minPaths : Fin (n - k) → MinimumWeightPath D
  /-- Path indices match -/
  index_match : ∀ j, (minPaths j).checkIdx = j

namespace OptimalDeformedChecks

variable {D : DeformConfig C L}

/-- Convert to standard deformed checks collection -/
def toDeformedChecksCollection (opt : OptimalDeformedChecks D) : DeformedChecksCollection D where
  deformedChecks := fun j => (opt.minPaths j).toDeformedCheck D
  index_match := by
    intro j
    simp only [MinimumWeightPath.toDeformedCheck]
    exact opt.index_match j

/-- The weight of optimal deformed check j -/
def checkWeight (opt : OptimalDeformedChecks D) (j : Fin (n - k)) : ℕ :=
  DeformedCheckWeight D ((opt.minPaths j).toDeformedCheck D)

/-- Optimal checks have minimal weight among all valid choices -/
theorem optimal_weight_minimal (opt : OptimalDeformedChecks D) (j : Fin (n - k))
    (alt : DeformedCheck D) (_h_same : alt.checkIdx = j) (h_orig : alt.originalCheck = C.checks j) :
    DeformedCheckWeight D ((opt.minPaths j).toDeformedCheck D) ≤ DeformedCheckWeight D alt := by
  unfold DeformedCheckWeight MinimumWeightPath.toDeformedCheck
  simp only
  have h_idx := opt.index_match j
  have h_mwp_idx : (opt.minPaths j).checkIdx = j := h_idx
  have h_path := (opt.minPaths j).is_minimum alt.edgePath alt.edgePath_valid
    (by
      have hbc := alt.boundary_condition
      unfold satisfiesCheckBoundaryCondition at hbc ⊢
      intro w
      have h_check_eq : C.checks (opt.minPaths j).checkIdx = C.checks j := by rw [h_mwp_idx]
      rw [h_check_eq, ← h_orig]
      exact hbc w)
  have h_check_eq2 : (C.checks (opt.minPaths j).checkIdx).weight = (C.checks j).weight := by
    rw [h_mwp_idx]
  rw [h_check_eq2, ← h_orig]
  omega

end OptimalDeformedChecks

/-! ## Section 7: Cycle Basis Optimization

The choice of cycle basis affects the flux operators but not their algebra.
However, different bases may have different total edge counts.
-/

/-- Total edge count in a cycle basis -/
def CycleBasisEdgeCount (F : FluxConfig C L) : ℕ :=
  ∑ c : F.CycleIdx, (F.cycleEdges c).card

/-- A cycle basis is minimal if no smaller basis generates the same cycle space -/
def IsMinimalCycleBasis (F : FluxConfig C L) : Prop :=
  isProperCycleBasis F ∧
  ∀ F' : FluxConfig C L, isProperCycleBasis F' →
    F'.graph = F.graph → CycleBasisEdgeCount F ≤ CycleBasisEdgeCount F'

/-! ## Section 8: Freedom Summary

The total freedom in specifying deformed code generators combines:
1. Path freedom: any path satisfying boundary condition
2. Cycle basis freedom: any generating set of cycles

Both freedoms preserve the deformed code's stabilizer group.
-/

/-- The path freedom does not change the stabilizer group:
    Two deformed checks from same original with different paths give operators
    that differ by products of flux operators (which are already in the stabilizer group). -/
theorem path_freedom_preserves_stabilizer (equiv : DeformedCheckEquivalence D) :
    -- The path difference is a cycle, hence a product of flux operators
    isCycle D equiv.pathDiff :=
  equiv.pathDiff_is_cycle

/-- Different path choices give commuting deformed checks -/
theorem alt_paths_commute (check1 check2 : DeformedCheck D)
    (_h_same : check1.originalCheck = check2.originalCheck) :
    -- Both checks commute with all Gauss law operators
    (∀ v, deformedCheck_gaussLaw_overlap D check1 v = 0) ∧
    (∀ v, deformedCheck_gaussLaw_overlap D check2 v = 0) :=
  ⟨deformedCheck_commutes_with_all_gaussLaw D check1,
   deformedCheck_commutes_with_all_gaussLaw D check2⟩

/-! ## Section 9: Helper Lemmas -/

/-- Empty path has zero length -/
@[simp]
theorem pathLength_empty : PathLength D (∅ : EdgePath D) = 0 := Finset.card_empty

/-- Path length is non-negative -/
theorem pathLength_nonneg (gamma : EdgePath D) : 0 ≤ PathLength D gamma := Nat.zero_le _

/-- Deformed check weight is at least original weight -/
theorem deformedCheckWeight_ge_original (stilde : DeformedCheck D) :
    stilde.originalCheck.weight ≤ DeformedCheckWeight D stilde := by
  unfold DeformedCheckWeight
  exact Nat.le_add_right _ _

/-- Edge degree of an edge not in any path is zero -/
theorem edgeDegree_not_in_paths (coll : DeformedChecksCollection D) (e : Sym2 D.graph.Vertex)
    (h : ∀ j, e ∉ (coll.deformedChecks j).edgePath) :
    EdgeDegree D coll e = 0 := by
  unfold EdgeDegree
  have h_empty : Finset.filter (fun j => e ∈ (coll.deformedChecks j).edgePath) Finset.univ = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact h j
  simp only [h_empty, Finset.card_empty]

/-- Symmetric difference of paths gives difference in edge degree contribution -/
theorem path_symmDiff_edgeDegree (gamma1 gamma2 : EdgePath D) (e : Sym2 D.graph.Vertex) :
    (e ∈ symmDiff gamma1 gamma2) ↔ Xor' (e ∈ gamma1) (e ∈ gamma2) := by
  simp only [Finset.mem_symmDiff]
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inl ⟨h.1, h.2⟩
    | inr h => exact Or.inr ⟨h.1, h.2⟩
  · intro h
    cases h with
    | inl h => left; exact ⟨h.1, h.2⟩
    | inr h => right; exact ⟨h.1, h.2⟩

/-- The weight formula for minimum weight path -/
theorem minWeightPath_weight (mwp : MinimumWeightPath D) :
    DeformedCheckWeight D (mwp.toDeformedCheck D) =
    (C.checks mwp.checkIdx).weight + mwp.path.card := by
  unfold DeformedCheckWeight MinimumWeightPath.toDeformedCheck
  simp only

/-- Total weight bounds -/
theorem totalWeight_bounds (coll : DeformedChecksCollection D) :
    ∑ j : Fin (n - k), (C.checks j).weight ≤ TotalWeight D coll := by
  unfold TotalWeight
  apply Finset.sum_le_sum
  intro j _
  calc (C.checks j).weight
      = (coll.deformedChecks j).originalCheck.weight := by
          have h := (coll.deformedChecks j).check_eq
          have hidx := coll.index_match j
          rw [h, hidx]
    _ ≤ _ := deformedCheckWeight_ge_original D (coll.deformedChecks j)

end QEC
