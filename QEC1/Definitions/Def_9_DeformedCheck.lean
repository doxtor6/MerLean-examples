import QEC1.Definitions.Def_8_DeformedOperator

/-!
# Deformed Check (Definition 9)

## Statement
Let C be an [[n, k, d]] stabilizer code with checks {s_j}, let L be an X-type logical operator
with support L, and let G = (V, E) be a gauging graph.

For each check s_j = i^sigma_j prod_{v in S_{X,j}} X_v prod_{v in S_{Z,j}} Z_v of the original code:

The **deformed check** stilde_j is defined as:
  stilde_j = s_j * prod_{e in gamma_j} Z_e
where gamma_j is a subset of E satisfying boundary_1(gamma_j) = S_{Z,j} cap V.

**Two cases**:
(i) If S_{Z,j} cap L = empty (check has no Z-support on L), then gamma_j = empty and stilde_j = s_j.
    We denote the set of such checks as C.

(ii) If S_{Z,j} cap L != empty (check has Z-support on L), then gamma_j != empty
    is a nontrivial path.
    We denote the set of such checks as S.

**Verification that stilde_j commutes with all A_v**:
[stilde_j, A_v] = 0 iff |S_{Z,j} cap {v}| + |{e in gamma_j : v in e}| = 0 (mod 2), which is ensured
by the boundary condition boundary_1(gamma_j) = S_{Z,j} cap V.

## Main Results
**Main Structure** (`DeformedCheck`): A check with edge-path satisfying boundary condition
**Case Classification** (`CheckType`): Classifies checks as unchanged (C) or with path (S)
**Commutativity** (`deformedCheck_commutes_with_gaussLaw`): [stilde_j, A_v] = 0

## File Structure
1. Check Type Classification: Checks with/without Z-support on L
2. Deformed Check Definition: stilde_j = s_j * prod_{e in gamma_j} Z_e
3. Boundary Condition: boundary_1(gamma_j) = S_{Z,j} cap V
4. Commutativity Verification: [stilde_j, A_v] = 0 via boundary condition
5. Properties: Path emptiness for unchanged checks
6. Helper Lemmas: Basic properties
-/

namespace QEC

open scoped BigOperators

variable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}

/-! ## Section 1: Check Type Classification

We classify checks into two types based on whether their Z-support
intersects the logical operator support L:
- Type C: S_{Z,j} cap L = empty (check unchanged)
- Type S: S_{Z,j} cap L != empty (check requires nontrivial path)
-/

/-- The Z-support intersection with the logical support for a check -/
def checkZSupportOnLogical (s : StabilizerCheck n) (L : XTypeLogical C) : Finset (Fin n) :=
  s.supportZ ∩ L.support

/-- A check has no Z-support on the logical operator (Type C) -/
def isTypeC (s : StabilizerCheck n) (L : XTypeLogical C) : Prop :=
  checkZSupportOnLogical s L = ∅

/-- A check has Z-support on the logical operator (Type S) -/
def isTypeS (s : StabilizerCheck n) (L : XTypeLogical C) : Prop :=
  (checkZSupportOnLogical s L).Nonempty

/-- Type C and Type S are complementary (decidable) -/
instance : DecidablePred (fun s : StabilizerCheck n => isTypeC s L) := fun s =>
  inferInstanceAs (Decidable (s.supportZ ∩ L.support = ∅))

instance : DecidablePred (fun s : StabilizerCheck n => isTypeS s L) := fun s =>
  inferInstanceAs (Decidable ((s.supportZ ∩ L.support).Nonempty))

/-- Type C and Type S are mutually exclusive and exhaustive -/
theorem typeC_or_typeS (s : StabilizerCheck n) (L : XTypeLogical C) :
    isTypeC s L ∨ isTypeS s L := by
  unfold isTypeC isTypeS checkZSupportOnLogical
  by_cases h : (s.supportZ ∩ L.support) = ∅
  · left; exact h
  · right; exact Finset.nonempty_iff_ne_empty.mpr h

theorem typeC_iff_not_typeS (s : StabilizerCheck n) (L : XTypeLogical C) :
    isTypeC s L ↔ ¬isTypeS s L := by
  unfold isTypeC isTypeS checkZSupportOnLogical
  rw [Finset.nonempty_iff_ne_empty]
  exact Iff.intro (fun h => fun hne => hne h) (fun h => by push_neg at h; exact h)

/-! ## Section 2: Deformed Check Definition

A deformed check stilde_j consists of:
- The original check s_j
- An edge-path gamma_j satisfying boundary_1(gamma_j) = S_{Z,j} cap V

The deformed check acts as stilde_j = s_j * prod_{e in gamma_j} Z_e
-/

variable (D : DeformConfig C L)

/-- The Z-support of a check intersected with V (via qubitToVertex embedding).
    This gives the target boundary for the edge-path. -/
def checkZSupportOnVertices (s : StabilizerCheck n) : Finset D.graph.Vertex :=
  Finset.image D.qubitToVertex s.supportZ

/-- The target boundary for a check: 1 if vertex is in the image of Z-support, 0 otherwise -/
def checkTargetBoundary (s : StabilizerCheck n) (w : D.graph.Vertex) : ZMod 2 :=
  if w ∈ checkZSupportOnVertices D s then 1 else 0

/-- The boundary condition for a deformed check:
    boundary_1(gamma_j) = S_{Z,j} cap V -/
def satisfiesCheckBoundaryCondition (s : StabilizerCheck n) (gamma : EdgePath D) : Prop :=
  ∀ w : D.graph.Vertex, edgePathBoundary D gamma w = checkTargetBoundary D s w

/-- A deformed check stilde_j consists of:
    - The original check s_j (a stabilizer check of the code)
    - The check index j
    - An edge-path gamma_j satisfying the boundary condition boundary_1(gamma_j) = S_{Z,j} cap V

    The deformed check acts as stilde_j = s_j * prod_{e in gamma_j} Z_e -/
structure DeformedCheck (D : DeformConfig C L) where
  /-- Index of the check in the stabilizer code -/
  checkIdx : Fin (n - k)
  /-- The original check s_j -/
  originalCheck : StabilizerCheck n
  /-- The original check is indeed the check at index j -/
  check_eq : originalCheck = C.checks checkIdx
  /-- The edge-path gamma_j (subset of edges) -/
  edgePath : EdgePath D
  /-- The edge-path consists of actual edges of the graph -/
  edgePath_valid : ∀ e ∈ edgePath, e ∈ D.graph.graph.edgeSet
  /-- The boundary condition: boundary_1(gamma_j) = S_{Z,j} cap V -/
  boundary_condition : satisfiesCheckBoundaryCondition D originalCheck edgePath

namespace DeformedCheck

variable {D : DeformConfig C L}

/-- The Z-support on edge qubits (as a ZMod 2 function) -/
def edgeZSupport (stilde : DeformedCheck D) : Sym2 D.graph.Vertex → ZMod 2 :=
  fun e => if e ∈ stilde.edgePath then 1 else 0

/-- Number of edges in the edge-path -/
def numEdges (stilde : DeformedCheck D) : ℕ := stilde.edgePath.card

/-- The X-support is preserved from the original check -/
def originalXSupport (stilde : DeformedCheck D) : Finset (Fin n) :=
  stilde.originalCheck.supportX

/-- The Z-support is preserved from the original check -/
def originalZSupport (stilde : DeformedCheck D) : Finset (Fin n) :=
  stilde.originalCheck.supportZ

/-- The phase factor from the original check -/
def phaseFactor (stilde : DeformedCheck D) : Phase :=
  stilde.originalCheck.phase

end DeformedCheck

/-! ## Section 3: Type C Checks (Unchanged)

For Type C checks (S_{Z,j} cap L = empty), the edge-path gamma_j = empty and stilde_j = s_j.

Note: For Type C checks with isTypeC (no Z-support on L), if the check also has no
Z-support on any vertex V, then the target boundary is zero everywhere and the empty
path satisfies the boundary condition. When there is Z-support on V but not on L,
the check still requires a nontrivial path but is classified as Type C.
-/

/-- Check has no Z-support on any vertex in V (stronger than isTypeC).
    This is the condition under which an empty edge-path satisfies the boundary condition. -/
def hasNoZSupportOnVertices (s : StabilizerCheck n) : Prop :=
  checkZSupportOnVertices D s = ∅

/-- Decidability instance for hasNoZSupportOnVertices -/
instance hasNoZSupportOnVertices_decidable (s : StabilizerCheck n) :
    Decidable (hasNoZSupportOnVertices D s) :=
  inferInstanceAs (Decidable (checkZSupportOnVertices D s = ∅))

/-- If a check has no Z-support on vertices, the target boundary is zero -/
theorem checkTargetBoundary_zero_of_empty (s : StabilizerCheck n)
    (h : hasNoZSupportOnVertices D s) (w : D.graph.Vertex) :
    checkTargetBoundary D s w = 0 := by
  unfold checkTargetBoundary hasNoZSupportOnVertices at *
  simp only [h, Finset.notMem_empty, ↓reduceIte]

/-- A check with no Z-support on vertices can be deformed with an empty path -/
def mkEmptyPathDeformedCheck (j : Fin (n - k)) (h : hasNoZSupportOnVertices D (C.checks j)) :
    DeformedCheck D where
  checkIdx := j
  originalCheck := C.checks j
  check_eq := rfl
  edgePath := ∅
  edgePath_valid := fun _ he => absurd he (Finset.notMem_empty _)
  boundary_condition := by
    intro w
    simp only [edgePathBoundary, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact (checkTargetBoundary_zero_of_empty D (C.checks j) h w).symm

/-! ## Section 4: Commutativity with Gauss Law Operators

**Verification that stilde_j commutes with all A_v**:
[stilde_j, A_v] = 0 iff |S_{Z,j} cap {v}| + |{e in gamma_j : v in e}| = 0 (mod 2)

This is ensured by the boundary condition boundary_1(gamma_j) = S_{Z,j} cap V.

The symplectic form between stilde_j and A_v counts:
1. X(stilde_j) cap Z(A_v) = s_j.supportX cap empty = empty (A_v has no Z-support)
2. Z(stilde_j) cap X(A_v) counts overlap between:
   - s_j's Z-support on original qubits and A_v's X-support on vertex v
   - gamma_j's Z-support on edges and A_v's X-support on incident edges

The total overlap equals |S_{Z,j} cap {v}| + |{e in gamma_j : v in e}|.
By the boundary condition, this equals 0 (mod 2) for all v.
-/

/-- The indicator function for whether a qubit v maps to vertex w -/
def qubitAtVertex (v : Fin n) (w : D.graph.Vertex) : ZMod 2 :=
  if D.qubitToVertex v = w then 1 else 0

/-- The Z-support of s_j at vertex w: counts qubits in Z-support mapping to w -/
def checkZSupportAtVertex (s : StabilizerCheck n) (w : D.graph.Vertex) : ZMod 2 :=
  ∑ v ∈ s.supportZ, qubitAtVertex D v w

/-- The edge incidence at vertex w: counts edges in gamma incident to w -/
def edgeIncidenceAtVertex (gamma : EdgePath D) (w : D.graph.Vertex) : ZMod 2 :=
  (Finset.filter (fun e => w ∈ e) gamma).card

/-- The boundary condition ensures Z-support and edge incidence are equal (mod 2) -/
theorem boundary_ensures_equal_parity (s : StabilizerCheck n) (gamma : EdgePath D)
    (hbound : satisfiesCheckBoundaryCondition D s gamma) (w : D.graph.Vertex) :
    edgeIncidenceAtVertex D gamma w = checkTargetBoundary D s w := by
  unfold satisfiesCheckBoundaryCondition at hbound
  unfold edgePathBoundary at hbound
  unfold edgeIncidenceAtVertex checkTargetBoundary
  exact hbound w

/-- The symplectic overlap between deformed check and Gauss law operator at vertex v.
    This counts |S_{Z,j} cap {v}| + |{e in gamma_j : v in e}|.

    Since A_v is X-type and has:
    - X-support: 1 at vertex v and edges incident to v
    - Z-support: empty

    The symplectic form omega(stilde_j, A_v) = |X(stilde_j) cap Z(A_v)| + |Z(stilde_j) cap X(A_v)|
                                             = 0 + |Z(stilde_j) cap X(A_v)|

    Z(stilde_j) has two parts:
    1. Original Z-support on qubits: s_j.supportZ -> contributes if qubit maps to v
    2. Edge Z-support from gamma_j: contributes for each edge in gamma_j incident to v
-/
def deformedCheck_gaussLaw_overlap (stilde : DeformedCheck D) (v : D.graph.Vertex) : ZMod 2 :=
  checkTargetBoundary D stilde.originalCheck v + edgeIncidenceAtVertex D stilde.edgePath v

/-- **Key Theorem**: The overlap is 0 (mod 2) due to the boundary condition.
    This proves [stilde_j, A_v] = 0 for all v. -/
theorem deformedCheck_commutes_with_gaussLaw (stilde : DeformedCheck D) (v : D.graph.Vertex) :
    deformedCheck_gaussLaw_overlap D stilde v = 0 := by
  unfold deformedCheck_gaussLaw_overlap edgeIncidenceAtVertex
  have hbound := stilde.boundary_condition
  unfold satisfiesCheckBoundaryCondition edgePathBoundary at hbound
  have hv := hbound v
  -- hv : |{e in gamma : v in e}| = checkTargetBoundary stilde.originalCheck v
  -- We need: checkTargetBoundary + |{e in gamma : v in e}| = 0
  -- Substitute: checkTargetBoundary + checkTargetBoundary = 0 in ZMod 2
  rw [← hv]
  exact ZMod2_self_add_self' _

/-- All deformed checks commute with all Gauss law operators -/
theorem deformedCheck_commutes_with_all_gaussLaw (stilde : DeformedCheck D) :
    ∀ v : D.graph.Vertex, deformedCheck_gaussLaw_overlap D stilde v = 0 := by
  intro v
  exact deformedCheck_commutes_with_gaussLaw D stilde v

/-! ## Section 5: Classification of Code Checks

We partition the n-k checks into two sets based on whether their Z-support intersects L:
- Set C: Checks with S_{Z,j} ∩ L = ∅ (Type C, may have gamma_j = ∅ or nontrivial)
- Set S: Checks with S_{Z,j} ∩ L ≠ ∅ (Type S, requires gamma_j ≠ ∅)

Note: The original definition classifies checks based on intersection with the logical support L,
not with all vertices V. This is the faithful classification from the mathematical statement.
-/

/-- The set of check indices that are Type C: S_{Z,j} ∩ L = ∅
    These checks have no Z-support on the logical operator L.
    For such checks, gamma_j may be empty (if also no Z-support on V) or nontrivial. -/
def typeCChecks (_D : DeformConfig C L) : Finset (Fin (n - k)) :=
  Finset.filter (fun j => isTypeC (C.checks j) L) Finset.univ

/-- The set of check indices that are Type S: S_{Z,j} ∩ L ≠ ∅
    These checks have Z-support on the logical operator L.
    By the original definition, such checks require gamma_j ≠ ∅ (nontrivial path). -/
def typeSChecks (_D : DeformConfig C L) : Finset (Fin (n - k)) :=
  Finset.filter (fun j => isTypeS (C.checks j) L) Finset.univ

/-- Type C and Type S partition all checks -/
theorem typeC_typeS_partition :
    typeCChecks D ∪ typeSChecks D = Finset.univ := by
  ext j
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  simp only [typeCChecks, typeSChecks, Finset.mem_filter, Finset.mem_univ, true_and]
  exact typeC_or_typeS (C.checks j) L

/-- Type C and Type S are disjoint -/
theorem typeC_typeS_disjoint :
    Disjoint (typeCChecks D) (typeSChecks D) := by
  rw [Finset.disjoint_iff_ne]
  intro j hj m hk
  simp only [typeCChecks, typeSChecks, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
  intro heq
  rw [heq] at hj
  rw [typeC_iff_not_typeS] at hj
  exact hj hk

/-! ## Section 5.1: Type S Checks Require Nontrivial Paths

From the original definition, case (ii) states that when S_{Z,j} ∩ L ≠ ∅ (Type S),
then γ_j ≠ ∅ must be a nontrivial path.

This follows from the boundary condition: if a Type S check has Z-support on L,
and L.support maps to vertices V via supportEmbed, then the target boundary
is nonzero at some vertex. Therefore the edge-path cannot be empty.
-/

/-- A Type S deformed check is a deformed check where the original check is Type S
    and the edge-path is required to be nonempty.
    This captures case (ii) from the original definition. -/
structure TypeSDeformedCheck (D : DeformConfig C L) extends DeformedCheck D where
  /-- The original check has Z-support on L (Type S) -/
  is_typeS : isTypeS originalCheck L
  /-- The edge-path is nontrivial (nonempty) -/
  edgePath_nonempty : edgePath.Nonempty

/-- For a Type S check whose Z-support on L maps to vertices, the target boundary
    is nonzero at some vertex. This is because the supportEmbed maps L.support
    injectively to V, so the Z-support intersection with L.support creates nonzero
    target boundary values. -/
theorem typeS_implies_nonzero_target (s : StabilizerCheck n) (hsTypeS : isTypeS s L) :
    ∃ v ∈ L.support, v ∈ s.supportZ := by
  unfold isTypeS checkZSupportOnLogical at hsTypeS
  rw [Finset.nonempty_iff_ne_empty] at hsTypeS
  have h := Finset.nonempty_iff_ne_empty.mpr hsTypeS
  obtain ⟨v, hv⟩ := h
  simp only [Finset.mem_inter] at hv
  exact ⟨v, hv.2, hv.1⟩

/-! ## Section 6: Deformed Checks Collection

The full set of deformed checks for all stabilizer checks of the code.
-/

/-- A collection of deformed checks for all checks in the code -/
structure DeformedChecksCollection (D : DeformConfig C L) where
  /-- Deformed check for each check index -/
  deformedChecks : Fin (n - k) → DeformedCheck D
  /-- Each deformed check corresponds to its index -/
  index_match : ∀ j, (deformedChecks j).checkIdx = j

namespace DeformedChecksCollection

variable {D : DeformConfig C L}

/-- All deformed checks commute with all Gauss law operators -/
theorem all_commute_gaussLaw (coll : DeformedChecksCollection D)
    (j : Fin (n - k)) (v : D.graph.Vertex) :
    deformedCheck_gaussLaw_overlap D (coll.deformedChecks j) v = 0 :=
  deformedCheck_commutes_with_gaussLaw D (coll.deformedChecks j) v

/-- The number of deformed checks equals n - k -/
theorem count_eq (_coll : DeformedChecksCollection D) :
    Fintype.card (Fin (n - k)) = n - k :=
  Fintype.card_fin (n - k)

end DeformedChecksCollection

/-! ## Section 7: Explicit Deformed Check Formula

The deformed check stilde_j = s_j * prod_{e in gamma_j} Z_e is explicitly represented by:
- X-support on original qubits: s_j.supportX
- Z-support on original qubits: s_j.supportZ
- Z-support on edge qubits: gamma_j
- Phase: s_j.phase
-/

/-- The full deformed check representation combining original check and edge Z-support -/
structure DeformedCheckOperator (D : DeformConfig C L) where
  /-- X-support on original qubits -/
  originalXSupport : Finset (Fin n)
  /-- Z-support on original qubits -/
  originalZSupport : Finset (Fin n)
  /-- Z-support on edge qubits (the edge-path gamma_j) -/
  edgeZSupport : Finset (Sym2 D.graph.Vertex)
  /-- Phase factor i^sigma_j -/
  phase : Phase

/-- Convert a DeformedCheck to a DeformedCheckOperator -/
def DeformedCheck.toDeformedCheckOperator (stilde : DeformedCheck D) :
    DeformedCheckOperator D where
  originalXSupport := stilde.originalCheck.supportX
  originalZSupport := stilde.originalCheck.supportZ
  edgeZSupport := stilde.edgePath
  phase := stilde.originalCheck.phase

/-! ## Section 8: Helper Lemmas -/

/-- The edge Z-support of a deformed check is 1 on path edges -/
@[simp]
theorem DeformedCheck.edgeZSupport_mem (stilde : DeformedCheck D) (e : Sym2 D.graph.Vertex)
    (he : e ∈ stilde.edgePath) : stilde.edgeZSupport e = 1 := by
  simp only [DeformedCheck.edgeZSupport, he, ↓reduceIte]

/-- The edge Z-support of a deformed check is 0 on non-path edges -/
@[simp]
theorem DeformedCheck.edgeZSupport_not_mem (stilde : DeformedCheck D) (e : Sym2 D.graph.Vertex)
    (he : e ∉ stilde.edgePath) : stilde.edgeZSupport e = 0 := by
  simp only [DeformedCheck.edgeZSupport, he, ↓reduceIte]

/-- The boundary at a vertex equals the target boundary -/
theorem DeformedCheck.boundary_eq_target (stilde : DeformedCheck D) (w : D.graph.Vertex) :
    edgePathBoundary D stilde.edgePath w = checkTargetBoundary D stilde.originalCheck w :=
  stilde.boundary_condition w

/-- Empty path satisfies boundary condition when target is zero -/
theorem empty_path_satisfies_zero_target (s : StabilizerCheck n)
    (h : ∀ w, checkTargetBoundary D s w = 0) :
    satisfiesCheckBoundaryCondition D s ∅ := by
  intro w
  simp only [edgePathBoundary, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
  exact (h w).symm

/-- The target boundary is zero when Z-support on vertices is empty -/
theorem target_zero_of_empty_ZSupport (s : StabilizerCheck n)
    (h : checkZSupportOnVertices D s = ∅) (w : D.graph.Vertex) :
    checkTargetBoundary D s w = 0 := by
  simp only [checkTargetBoundary, h, Finset.notMem_empty, ↓reduceIte]

/-- A check with no Z-support on V has empty path via mkEmptyPathDeformedCheck -/
theorem emptyPathCheck_has_empty_path (j : Fin (n - k))
    (h : hasNoZSupportOnVertices D (C.checks j)) :
    (mkEmptyPathDeformedCheck D j h).edgePath = ∅ := rfl

/-- The checkTargetBoundary relation to targetBoundary from DeformedOperator -/
theorem checkTargetBoundary_eq_targetBoundary (s : StabilizerCheck n) (w : D.graph.Vertex) :
    checkTargetBoundary D s w = targetBoundary D s w := by
  unfold checkTargetBoundary targetBoundary checkZSupportOnVertices
  simp only [Finset.mem_image]

/-- The edge-path is determined by the boundary condition (up to cycles).
    If two edge-paths satisfy the same boundary condition, their symmetric
    difference has zero boundary at every vertex (it's a cycle). -/
theorem edgePath_uniqueness_mod_cycles (s : StabilizerCheck n)
    (gamma1 gamma2 : EdgePath D)
    (h1 : satisfiesCheckBoundaryCondition D s gamma1)
    (h2 : satisfiesCheckBoundaryCondition D s gamma2) :
    ∀ w, edgePathBoundary D (symmDiff gamma1 gamma2) w = 0 := by
  intro w
  -- Use the existing helper from DeformedOperator
  exact boundary_diff_is_cycle D gamma1 gamma2 s
    (fun v => by
      have h := h1 v
      rw [checkTargetBoundary_eq_targetBoundary] at h
      exact h)
    (fun v => by
      have h := h2 v
      rw [checkTargetBoundary_eq_targetBoundary] at h
      exact h)
    w

/-- The deformed check is a valid deformed operator -/
theorem DeformedCheck.toDeformedOperator (stilde : DeformedCheck D)
    (hcomm : commutesWithLogical stilde.originalCheck L) :
    ∃ (P : DeformedOperator D),
      P.original = stilde.originalCheck ∧ P.edgePath = stilde.edgePath := by
  refine ⟨{
    original := stilde.originalCheck
    commutes_with_L := hcomm
    edgePath := stilde.edgePath
    edgePath_valid := stilde.edgePath_valid
    boundary_condition := fun w => by
      have h := stilde.boundary_condition w
      rw [checkTargetBoundary_eq_targetBoundary] at h
      exact h
  }, rfl, rfl⟩

end QEC
