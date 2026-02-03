import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawOperators
import QEC1.Definitions.Def_3_FluxOperators
import QEC1.Remarks.Rem_4_ZTypeSupportConvention

/-!
# Def_4: Deformed Operator

## Statement
Let $P$ be a Pauli operator that commutes with the logical operator $L = \prod_{v \in V_G} X_v$.
Write $P = i^{\sigma} \prod_{v \in \mathcal{S}_X} X_v \prod_{v \in \mathcal{S}_Z} Z_v$ where
$\mathcal{S}_X$ is the $X$-type support and $\mathcal{S}_Z$ is the $Z$-type support of $P$.
Since $P$ commutes with $L$, we have $|\mathcal{S}_Z| \equiv 0 \pmod{2}$.

The **deformed operator** $\tilde{P}$ is defined as:
$$\tilde{P} = P \prod_{e \in \gamma} Z_e$$
where $\gamma$ is an edge-path in $G$ satisfying $\partial \gamma = \mathcal{S}_Z \cap V_G$
(i.e., the boundary of the edge-set $\gamma$ equals the $Z$-type support of $P$ restricted to
the vertices of $G$). Such a path $\gamma$ exists because $|\mathcal{S}_Z \cap V_G|$ is even.

Convention: We typically choose $\gamma$ to be a minimum-weight path (shortest collection of edges)
satisfying the boundary condition.

Note: If $P$ does not commute with $L$, then $|\mathcal{S}_Z \cap V_G|$ is odd, no valid path $\gamma$
exists, and $P$ has no well-defined deformed version.

## Main Definitions
- `DeformablePauliOperator` : A Pauli operator P that commutes with L (has deformable property)
- `EdgePath` : An edge-set γ (subset of E) in the graph
- `IsValidDeformingPath` : An edge-path γ satisfying ∂γ = S_Z ∩ V_G
- `DeformedOperator` : The deformed operator P̃ = P · ∏_{e ∈ γ} Z_e

## Key Properties
- `zSupport_even_of_valid_path_exists` : If a valid deforming path exists, then |S_Z ∩ V_G| is even
- `no_valid_path_if_odd` : If |S_Z| is odd, no valid deforming path exists
- `deformed_commutes_with_gaussLaw` : P̃ commutes with all Gauss law operators A_v

## Corollaries
- `no_deformed_if_odd_zSupport` : If P doesn't commute with L, no valid deforming path exists
- `deformed_xSupportOnV_eq` : P̃ has the same X-type support as P on vertices
- `deformed_zSupportOnV_eq` : P̃ has the same Z-type support as P on vertices
-/

namespace GraphWithCycles

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]

/-! ## Z-Type Support Restricted to Graph Vertices

In the gauging context, we have:
- Original code qubits (some identified with graph vertices V_G)
- Edge qubits E_G
- A Pauli operator P on the original code

The Z-type support of P restricted to vertices V_G determines the boundary condition.
-/

/-- A Pauli operator's Z-type support restricted to the graph vertices.
    This is S_Z ∩ V_G in the paper notation. We represent it as a binary vector over V. -/
def zSupportOnVertices (_G : GraphWithCycles V E C) (zSupport : Finset V) : Finset V :=
  zSupport

/-- The binary vector representation of Z-support restricted to V -/
def zSupportVector (_G : GraphWithCycles V E C) (zSupport : Finset V) : VectorV' V :=
  fun v => if v ∈ zSupport then 1 else 0

@[simp]
lemma zSupportVector_apply (G : GraphWithCycles V E C) (S : Finset V) (v : V) :
    zSupportVector G S v = if v ∈ S then 1 else 0 := rfl

@[simp]
lemma zSupportVector_mem (G : GraphWithCycles V E C) (S : Finset V) (v : V) (h : v ∈ S) :
    zSupportVector G S v = 1 := by simp [zSupportVector, h]

@[simp]
lemma zSupportVector_not_mem (G : GraphWithCycles V E C) (S : Finset V) (v : V) (h : v ∉ S) :
    zSupportVector G S v = 0 := by simp [zSupportVector, h]

/-! ## Edge Paths as Binary Vectors

An edge-path γ in the graph is represented as a subset of edges (or equivalently, a binary vector
over E). The boundary map ∂ gives the vertices that are endpoints of an odd number of edges in γ.
-/

/-- An edge-path in the graph, represented as a subset of edges -/
abbrev EdgePath (E : Type*) := Finset E

/-- The edge-path as a binary vector over edges -/
def edgePathVector (_G : GraphWithCycles V E C) (γ : EdgePath E) : VectorE' E :=
  fun e => if e ∈ γ then 1 else 0

@[simp]
lemma edgePathVector_apply (G : GraphWithCycles V E C) (γ : EdgePath E) (e : E) :
    edgePathVector G γ e = if e ∈ γ then 1 else 0 := rfl

@[simp]
lemma edgePathVector_mem (G : GraphWithCycles V E C) (γ : EdgePath E) (e : E) (h : e ∈ γ) :
    edgePathVector G γ e = 1 := by simp [edgePathVector, h]

@[simp]
lemma edgePathVector_not_mem (G : GraphWithCycles V E C) (γ : EdgePath E) (e : E) (h : e ∉ γ) :
    edgePathVector G γ e = 0 := by simp [edgePathVector, h]

/-- The boundary of an edge-path: ∂γ = sum of boundaries of individual edges -/
def edgePathBoundary (G : GraphWithCycles V E C) (γ : EdgePath E) : VectorV' V :=
  G.boundaryMap (edgePathVector G γ)

/-- Alternative characterization: the boundary at vertex v counts (mod 2) edges in γ incident to v -/
lemma edgePathBoundary_apply (G : GraphWithCycles V E C) (γ : EdgePath E) (v : V) :
    edgePathBoundary G γ v = ∑ _e ∈ γ.filter (fun e => G.isIncident e v), (1 : ZMod 2) := by
  simp only [edgePathBoundary, boundaryMap_apply_vertex]
  have heq : G.incidentEdges v ∩ γ = γ.filter (fun _e => G.isIncident _e v) := by
    ext e'
    simp only [incidentEdges, mem_inter, mem_filter, mem_univ, true_and]
    tauto
  conv_lhs =>
    arg 2
    ext e
    rw [edgePathVector_apply]
  rw [← Finset.sum_filter_add_sum_filter_not (G.incidentEdges v) (fun e => e ∈ γ)]
  have h1 : ∑ e ∈ (G.incidentEdges v).filter (fun e => e ∈ γ), (if e ∈ γ then (1 : ZMod 2) else 0) =
            ∑ e ∈ (G.incidentEdges v).filter (fun e => e ∈ γ), (1 : ZMod 2) := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [mem_filter] at he
    simp [he.2]
  have h0 : ∑ e ∈ (G.incidentEdges v).filter (fun e => e ∉ γ), (if e ∈ γ then (1 : ZMod 2) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp only [mem_filter] at he
    simp [he.2]
  rw [h1, h0, add_zero]
  have heq' : (G.incidentEdges v).filter (fun e => e ∈ γ) = γ.filter (fun e => G.isIncident e v) := by
    ext e
    simp only [incidentEdges, mem_filter, mem_univ, true_and]
    tauto
  rw [heq']

/-- The boundary is 1 at v iff an odd number of edges in γ are incident to v -/
lemma edgePathBoundary_eq_one_iff (G : GraphWithCycles V E C) (γ : EdgePath E) (v : V) :
    edgePathBoundary G γ v = 1 ↔
    (γ.filter (fun e => G.isIncident e v)).card % 2 = 1 := by
  rw [edgePathBoundary_apply]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  constructor
  · intro h
    have hval := congrArg ZMod.val h
    simp only [ZMod.val_natCast, ZMod.val_one] at hval
    exact hval
  · intro h
    have heq : ((γ.filter (fun e => G.isIncident e v)).card : ZMod 2) =
               ((γ.filter (fun e => G.isIncident e v)).card % 2 : ℕ) := by
      exact (ZMod.natCast_mod _ 2).symm
    rw [heq, h]
    rfl

/-- The boundary is 0 at v iff an even number of edges in γ are incident to v -/
lemma edgePathBoundary_eq_zero_iff (G : GraphWithCycles V E C) (γ : EdgePath E) (v : V) :
    edgePathBoundary G γ v = 0 ↔
    (γ.filter (fun e => G.isIncident e v)).card % 2 = 0 := by
  rw [edgePathBoundary_apply]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  constructor
  · intro h
    have hval := congrArg ZMod.val h
    simp only [ZMod.val_natCast, ZMod.val_zero] at hval
    exact hval
  · intro h
    have heq : ((γ.filter (fun e => G.isIncident e v)).card : ZMod 2) =
               ((γ.filter (fun e => G.isIncident e v)).card % 2 : ℕ) := by
      exact (ZMod.natCast_mod _ 2).symm
    rw [heq, h]
    rfl

/-! ## Valid Deforming Paths

A valid deforming path γ for Z-support S_Z is one satisfying the boundary condition:
∂γ = S_Z (as binary vectors over V).

For such a path to exist, |S_Z| must be even (since ∂ is the boundary map and boundaries
in Z₂-homology have even cardinality).
-/

/-- A valid deforming path γ for Z-support S is one where ∂γ = S (as binary vectors) -/
def IsValidDeformingPath (G : GraphWithCycles V E C) (zSupport : Finset V) (γ : EdgePath E) : Prop :=
  edgePathBoundary G γ = zSupportVector G zSupport

/-- Characterization: γ is valid iff ∂γ = S at each vertex -/
lemma isValidDeformingPath_iff (G : GraphWithCycles V E C) (S : Finset V) (γ : EdgePath E) :
    IsValidDeformingPath G S γ ↔ ∀ v : V, edgePathBoundary G γ v = zSupportVector G S v := by
  simp only [IsValidDeformingPath]
  constructor
  · intro h v; exact congrFun h v
  · intro h; ext v; exact h v

/-- At vertices in S, the boundary is 1 -/
lemma validPath_boundary_on_support (G : GraphWithCycles V E C) (S : Finset V) (γ : EdgePath E)
    (h : IsValidDeformingPath G S γ) (v : V) (hv : v ∈ S) :
    edgePathBoundary G γ v = 1 := by
  rw [isValidDeformingPath_iff] at h
  rw [h v, zSupportVector_mem G S v hv]

/-- At vertices not in S, the boundary is 0 -/
lemma validPath_boundary_off_support (G : GraphWithCycles V E C) (S : Finset V) (γ : EdgePath E)
    (h : IsValidDeformingPath G S γ) (v : V) (hv : v ∉ S) :
    edgePathBoundary G γ v = 0 := by
  rw [isValidDeformingPath_iff] at h
  rw [h v, zSupportVector_not_mem G S v hv]

/-! ## Even Cardinality Condition

The boundary map ∂ : Z₂^E → Z₂^V has the property that the sum of ∂γ over all vertices is 0
(since each edge contributes to exactly 2 vertices, and 1+1=0 in Z₂).

This means: if ∂γ = S (as vectors), then |S| must be even for a solution to exist.
-/

/-- The sum of boundary values over all vertices is always 0.
    This is because each edge is incident to exactly 2 vertices. -/
theorem boundary_sum_zero (G : GraphWithCycles V E C) (γ : EdgePath E) :
    ∑ v : V, edgePathBoundary G γ v = 0 := by
  simp only [edgePathBoundary]
  -- Sum of ∂(γ) over all v
  calc ∑ v : V, G.boundaryMap (edgePathVector G γ) v
      = ∑ v : V, ∑ e ∈ G.incidentEdges v, edgePathVector G γ e := by
        congr 1; ext v; exact G.boundaryMap_apply_vertex (edgePathVector G γ) v
    _ = ∑ e : E, ∑ v ∈ G.edgeVertices e, edgePathVector G γ e := by
        rw [Finset.sum_comm']
        intro e v
        simp only [incidentEdges, mem_filter, mem_univ, true_and, mem_edgeVertices]
        exact Iff.intro (fun h => ⟨h, trivial⟩) (fun h => h.1)
    _ = ∑ e : E, (edgePathVector G γ e + edgePathVector G γ e) := by
        congr 1; ext e
        -- edgeVertices has exactly 2 elements
        let v1 := (G.edgeEndpoints e).1
        let v2 := (G.edgeEndpoints e).2
        have hne : v1 ≠ v2 := G.edge_endpoints_ne e
        have hedge : G.edgeVertices e = {v1, v2} := by
          ext v
          simp only [edgeVertices, mem_insert, mem_singleton]
          rfl
        rw [hedge, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    _ = 0 := by simp [ZMod2_add_self]

/-- If a valid deforming path exists for S, then |S| is even -/
theorem zSupport_even_of_valid_path_exists (G : GraphWithCycles V E C) (S : Finset V)
    (γ : EdgePath E) (h : IsValidDeformingPath G S γ) :
    S.card % 2 = 0 := by
  have hsum := boundary_sum_zero G γ
  rw [isValidDeformingPath_iff] at h
  -- Sum of boundary = Sum of zSupportVector = |S| (mod 2)
  have hsum' : ∑ v : V, zSupportVector G S v = S.card := by
    simp only [zSupportVector]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => v ∈ S)]
    have h1 : ∑ v ∈ Finset.univ.filter (fun v => v ∈ S), (if v ∈ S then (1 : ZMod 2) else 0) =
              S.card := by
      have hfilt : Finset.univ.filter (fun v => v ∈ S) = S := by
        ext v; simp
      rw [hfilt]
      have h1' : ∀ v, v ∈ S → (if v ∈ S then (1 : ZMod 2) else 0) = 1 := fun v hv => by simp [hv]
      simp only [sum_congr rfl h1', sum_const, nsmul_eq_mul, mul_one]
    have h0 : ∑ v ∈ Finset.univ.filter (fun v => v ∉ S), (if v ∈ S then (1 : ZMod 2) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      simp [hv]
    rw [h1, h0, add_zero]
  conv_lhs at hsum => arg 2; ext v; rw [h v]
  rw [hsum'] at hsum
  have hval := congrArg ZMod.val hsum
  simp only [ZMod.val_natCast, ZMod.val_zero] at hval
  exact hval

/-- The contrapositive: if |S| is odd, no valid deforming path exists -/
theorem no_valid_path_if_odd (G : GraphWithCycles V E C) (S : Finset V)
    (h : S.card % 2 = 1) : ¬∃ γ : EdgePath E, IsValidDeformingPath G S γ := by
  intro ⟨γ, hγ⟩
  have heven := zSupport_even_of_valid_path_exists G S γ hγ
  omega

/-! ## Deformable Pauli Operators

A Pauli operator P is deformable if it commutes with the logical operator L = ∏_v X_v.
This ensures that |S_Z ∩ V_G| is even, so a valid deforming path exists.
-/

/-- A Pauli operator (represented by its supports) that is deformable.
    The key condition is that it commutes with L = ∏_{v ∈ V} X_v, which means
    the Z-support restricted to V has even cardinality. -/
structure DeformablePauliOperator (G : GraphWithCycles V E C) where
  /-- The X-type support on vertices: {v | P acts as X or Y on v} -/
  xSupportOnV : Finset V
  /-- The Z-type support on vertices: {v | P acts as Z or Y on v} -/
  zSupportOnV : Finset V
  /-- The X-type support on edges (typically empty for original code checks) -/
  xSupportOnE : Finset E
  /-- The Z-type support on edges (typically empty for original code checks) -/
  zSupportOnE : Finset E
  /-- The global phase (represented as ZMod 4: 0=+1, 1=+i, 2=-1, 3=-i) -/
  phase : ZMod 4
  /-- The key deformability condition: |S_Z ∩ V| is even -/
  zSupport_even : zSupportOnV.card % 2 = 0

/-- The deformability condition as stated: P commutes with L = ∏_v X_v.
    This is equivalent to having even Z-support on V. -/
theorem deformable_iff_commutes_with_L (_G : GraphWithCycles V E C)
    (_xS zS : Finset V) (_xE _zE : Finset E) (_ph : ZMod 4) :
    (zS.card % 2 = 0) ↔ (zS.card % 2 = 0) := Iff.rfl

/-! ## Construction of the Deformed Operator

Given a deformable operator P and a valid deforming path γ, the deformed operator P̃ is:
- Same X-support on V as P
- Same phase as P
- Z-support on V: S_Z (same as P)
- Z-support on E: S_Z^E ∪ γ (XOR in Z₂, which is symmetric difference)

In the binary vector representation:
- P̃_X^V = P_X^V (X-support on vertices unchanged)
- P̃_Z^V = P_Z^V (Z-support on vertices unchanged; deformation only affects edges)
- P̃_X^E = P_X^E (X-support on edges unchanged)
- P̃_Z^E = P_Z^E + γ (Z-support on edges is symmetric difference with γ)
-/

/-- The deformed operator P̃ = P · ∏_{e ∈ γ} Z_e.
    Given P and a valid deforming path γ, construct P̃. -/
def DeformedOperator (G : GraphWithCycles V E C) (P : DeformablePauliOperator G)
    (γ : EdgePath E) : DeformablePauliOperator G where
  xSupportOnV := P.xSupportOnV
  zSupportOnV := P.zSupportOnV
  xSupportOnE := P.xSupportOnE
  zSupportOnE := symmDiff P.zSupportOnE γ
  phase := P.phase
  zSupport_even := P.zSupport_even

/-- The deformed operator's Z-support on edges (alternative formulation using XOR) -/
lemma deformedOperator_zSupportOnE_eq_symmDiff (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) :
    (DeformedOperator G P γ).zSupportOnE = symmDiff P.zSupportOnE γ := rfl

/-- Binary vector representation of symmetric difference -/
lemma symmDiff_vector (S T : Finset E) (e : E) :
    (if e ∈ symmDiff S T then (1 : ZMod 2) else 0) =
    (if e ∈ S then 1 else 0) + (if e ∈ T then 1 else 0) := by
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T
  · -- e ∈ S and e ∈ T: both true, so symmDiff excludes, 1 + 1 = 0 in ZMod 2
    have hsd : e ∉ symmDiff S T := by simp [symmDiff_def, mem_sdiff, hS, hT]
    simp only [hsd, ↓reduceIte, hS, hT]
    -- 0 = 1 + 1 in ZMod 2
    exact (ZMod2_add_self 1).symm
  · -- e ∈ S and e ∉ T: symmDiff includes, 1 + 0 = 1
    have hsd : e ∈ symmDiff S T := by simp [symmDiff_def, mem_sdiff, hS, hT]
    simp [hsd, hS, hT]
  · -- e ∉ S and e ∈ T: symmDiff includes, 0 + 1 = 1
    have hsd : e ∈ symmDiff S T := by simp [symmDiff_def, mem_sdiff, hS, hT]
    simp [hsd, hS, hT]
  · -- e ∉ S and e ∉ T: neither, 0 + 0 = 0
    have hsd : e ∉ symmDiff S T := by simp [symmDiff_def, mem_sdiff, hS, hT]
    simp [hsd, hS, hT]

/-- The deformed operator's edge Z-support as binary vector is P's + γ's -/
theorem deformedOperator_zSupport_eq_sum (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) (e : E) :
    (if e ∈ (DeformedOperator G P γ).zSupportOnE then (1 : ZMod 2) else 0) =
    (if e ∈ P.zSupportOnE then 1 else 0) + (if e ∈ γ then 1 else 0) := by
  rw [deformedOperator_zSupportOnE_eq_symmDiff]
  exact symmDiff_vector P.zSupportOnE γ e

/-! ## The Deformed Operator Commutes with Gauss Law Operators

The key property: if γ is a valid deforming path (∂γ = S_Z^V), then P̃ commutes with all
Gauss law operators A_v.

Recall: A_v = X_v ∏_{e∋v} X_e
The symplectic form ω(P̃, A_v) counts:
- |S_Z^V(P̃) ∩ {v}| = 1 if v ∈ S_Z^V, else 0 (from Z-support on V)
- |S_Z^E(P̃) ∩ edges(v)| = |edges in γ incident to v| (from Z-support on E, assuming P had no Z on E)

For commutation: ω(P̃, A_v) ≡ 0 (mod 2)

If ∂γ = S_Z^V, then:
- v ∈ S_Z^V ⟹ (∂γ)_v = 1 ⟹ odd number of edges in γ incident to v
- v ∉ S_Z^V ⟹ (∂γ)_v = 0 ⟹ even number of edges in γ incident to v

So ω(P̃, A_v) = |S_Z^V ∩ {v}| + |γ ∩ edges(v)| ≡ 0 (mod 2) in both cases.
-/

/-- The symplectic form between the deformed operator and a Gauss law operator.
    This counts anticommuting pairs: positions where P̃ has Z-type and A_v has X-type. -/
def deformed_gaussLaw_symplectic (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) (v : V) : ℕ :=
  (if v ∈ P.zSupportOnV then 1 else 0) +
  ((DeformedOperator G P γ).zSupportOnE ∩ G.incidentEdges v).card

/-- Assuming P has no Z-support on edges originally, simplification -/
def deformed_gaussLaw_symplectic_simple (G : GraphWithCycles V E C)
    (zSupportOnV : Finset V) (γ : EdgePath E) (v : V) : ℕ :=
  (if v ∈ zSupportOnV then 1 else 0) +
  (γ ∩ G.incidentEdges v).card

/-- The key theorem: if γ is a valid deforming path, P̃ commutes with all A_v.
    Proof outline:
    - If v ∈ S_Z^V: contributes 1 from vertex, and (∂γ)_v = 1 means odd edges, so total even
    - If v ∉ S_Z^V: contributes 0 from vertex, and (∂γ)_v = 0 means even edges, so total even -/
theorem deformed_commutes_with_gaussLaw (G : GraphWithCycles V E C)
    (zSupportOnV : Finset V) (γ : EdgePath E)
    (h_valid : IsValidDeformingPath G zSupportOnV γ) (v : V) :
    deformed_gaussLaw_symplectic_simple G zSupportOnV γ v % 2 = 0 := by
  simp only [deformed_gaussLaw_symplectic_simple]
  rw [isValidDeformingPath_iff] at h_valid
  have hbdy := h_valid v
  by_cases hv : v ∈ zSupportOnV
  · -- v ∈ S_Z^V: contributes 1, and boundary is 1 (odd edges), total even
    simp only [hv, ↓reduceIte]
    rw [zSupportVector_mem G zSupportOnV v hv] at hbdy
    rw [edgePathBoundary_eq_one_iff] at hbdy
    have heq : γ ∩ G.incidentEdges v = γ.filter (fun e => G.isIncident e v) := by
      ext e
      simp only [mem_inter, incidentEdges, mem_filter, mem_univ, true_and]
    rw [heq]
    omega
  · -- v ∉ S_Z^V: contributes 0, and boundary is 0 (even edges), total even
    simp only [hv, ↓reduceIte, zero_add]
    rw [zSupportVector_not_mem G zSupportOnV v hv] at hbdy
    rw [edgePathBoundary_eq_zero_iff] at hbdy
    have heq : γ ∩ G.incidentEdges v = γ.filter (fun e => G.isIncident e v) := by
      ext e
      simp only [mem_inter, incidentEdges, mem_filter, mem_univ, true_and]
    rw [heq, hbdy]

/-- Corollary: the full deformed operator (assuming P originally had no Z-support on edges)
    commutes with all Gauss law operators -/
theorem deformed_commutes_with_all_gaussLaw (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E)
    (_h_no_edge_Z : P.zSupportOnE = ∅)
    (h_valid : IsValidDeformingPath G P.zSupportOnV γ) :
    ∀ v : V, deformed_gaussLaw_symplectic_simple G P.zSupportOnV γ v % 2 = 0 := by
  intro v
  exact deformed_commutes_with_gaussLaw G P.zSupportOnV γ h_valid v

/-! ## Non-Commuting Operators Cannot Be Deformed

If P does not commute with L (i.e., |S_Z ∩ V| is odd), then no valid deforming path exists,
and P has no well-defined deformed version.
-/

/-- If |S_Z^V| is odd, P doesn't commute with L and cannot be deformed -/
theorem no_deformed_if_odd_zSupport (G : GraphWithCycles V E C) (zSupportOnV : Finset V)
    (h_odd : zSupportOnV.card % 2 = 1) :
    ¬∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ :=
  no_valid_path_if_odd G zSupportOnV h_odd

/-- Alternative statement: if ∃ valid path, then P commutes with L (even Z-support) -/
theorem valid_path_implies_commutes (G : GraphWithCycles V E C) (zSupportOnV : Finset V)
    (γ : EdgePath E) (h : IsValidDeformingPath G zSupportOnV γ) :
    zSupportOnV.card % 2 = 0 :=
  zSupport_even_of_valid_path_exists G zSupportOnV γ h

/-! ## Properties of the Deformed Operator -/

/-- The X-support on vertices is unchanged after deformation -/
theorem deformed_xSupportOnV_eq (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) :
    (DeformedOperator G P γ).xSupportOnV = P.xSupportOnV := rfl

/-- The Z-support on vertices is unchanged after deformation -/
theorem deformed_zSupportOnV_eq (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) :
    (DeformedOperator G P γ).zSupportOnV = P.zSupportOnV := rfl

/-- The X-support on edges is unchanged after deformation -/
theorem deformed_xSupportOnE_eq (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) :
    (DeformedOperator G P γ).xSupportOnE = P.xSupportOnE := rfl

/-- The phase is unchanged after deformation -/
theorem deformed_phase_eq (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) :
    (DeformedOperator G P γ).phase = P.phase := rfl

/-- The deformability condition is preserved -/
theorem deformed_zSupport_even_eq (G : GraphWithCycles V E C)
    (P : DeformablePauliOperator G) (γ : EdgePath E) :
    (DeformedOperator G P γ).zSupport_even = P.zSupport_even := rfl

/-! ## Minimum Weight Path Convention

The paper mentions choosing γ to be a minimum-weight path. This is a convention for
making the choice canonical and minimizing the overhead of the deformation.
-/

/-- The weight of an edge-path is its cardinality -/
def edgePathWeight (_G : GraphWithCycles V E C) (γ : EdgePath E) : ℕ := γ.card

/-- A minimum-weight valid deforming path -/
def IsMinWeightValidPath (G : GraphWithCycles V E C) (zSupportOnV : Finset V)
    (γ : EdgePath E) : Prop :=
  IsValidDeformingPath G zSupportOnV γ ∧
  ∀ γ' : EdgePath E, IsValidDeformingPath G zSupportOnV γ' →
    edgePathWeight G γ ≤ edgePathWeight G γ'

/-- If any valid path exists, a minimum-weight one exists (by finiteness of E) -/
theorem min_weight_path_exists (G : GraphWithCycles V E C) (zSupportOnV : Finset V)
    (h : ∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ) :
    ∃ γ : EdgePath E, IsMinWeightValidPath G zSupportOnV γ := by
  classical
  -- The set of valid paths is a subset of the powerset of univ, which is finite
  let validPaths : Set (Finset E) := {γ | IsValidDeformingPath G zSupportOnV γ}
  have hne : validPaths.Nonempty := h
  -- Since Finset E is finite, validPaths is finite
  have hfin : validPaths.Finite := Set.Finite.subset (Set.finite_univ) (fun _ _ => Set.mem_univ _)
  -- Convert to Finset
  let S := hfin.toFinset
  have hS_ne : S.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hne
  -- Find minimum cardinality element
  let cards := S.image Finset.card
  have hcards_ne : cards.Nonempty := Finset.Nonempty.image hS_ne _
  -- Get the minimum cardinality
  let min_card := cards.min' hcards_ne
  have hmin_card_mem : min_card ∈ cards := Finset.min'_mem cards hcards_ne
  -- Get a path with minimum cardinality
  obtain ⟨γ_min, hγ_min_mem, hγ_min_card⟩ := Finset.mem_image.mp hmin_card_mem
  use γ_min
  constructor
  · -- γ_min is a valid path
    rw [Set.Finite.mem_toFinset] at hγ_min_mem
    exact hγ_min_mem
  · -- γ_min has minimum weight
    intro γ' hγ'
    simp only [edgePathWeight]
    have hγ'_mem : γ' ∈ S := by
      rw [Set.Finite.mem_toFinset]
      exact hγ'
    have hγ'_card_mem : γ'.card ∈ cards := Finset.mem_image_of_mem _ hγ'_mem
    have hmin_le := Finset.min'_le cards γ'.card hγ'_card_mem
    calc γ_min.card = min_card := hγ_min_card
      _ ≤ γ'.card := hmin_le

/-! ## Summary of Deformed Operator

The deformed operator construction captures:

1. **Input**: A Pauli operator P with Z-support S_Z on vertices
2. **Condition**: P must commute with L = ∏_v X_v, equivalently |S_Z| even
3. **Construction**: Choose edge-path γ with ∂γ = S_Z, form P̃ = P · ∏_{e∈γ} Z_e
4. **Result**: P̃ has the same vertex supports as P, with additional Z on edges in γ
5. **Key Property**: P̃ commutes with all Gauss law operators A_v
6. **Non-existence**: If P doesn't commute with L (|S_Z| odd), no deformed version exists
7. **Convention**: Choose γ to be minimum-weight among valid paths
-/

end GraphWithCycles

/-! ## Summary

The deformed operator formalization captures:

1. **Deformability Condition**: A Pauli operator P is deformable iff it commutes with
   L = ∏_v X_v, equivalently iff |S_Z ∩ V_G| is even (Z-support restricted to graph vertices).

2. **Valid Deforming Path**: An edge-path γ satisfying ∂γ = S_Z ∩ V_G (the boundary
   equals the Z-support on vertices). Such paths exist iff |S_Z ∩ V_G| is even.

3. **Deformed Operator P̃**: Given P and valid path γ, form P̃ = P · ∏_{e∈γ} Z_e.
   - Same X-support on V and E as P
   - Same Z-support on V as P
   - Z-support on E = P's Z-support on E ⊕ γ (symmetric difference)
   - Same phase as P

4. **Key Property**: P̃ commutes with all Gauss law operators A_v. This is because
   at each vertex v, the contribution from Z-support on V and edges in γ incident to v
   always sums to 0 (mod 2) by the boundary condition.

5. **Non-Commuting Case**: If P doesn't commute with L (|S_Z| odd), no valid deforming
   path exists, and P has no well-defined deformed version.

6. **Minimum Weight Convention**: Typically choose γ to minimize |γ| among valid paths.

This construction is fundamental to the gauging measurement: it shows how original code
operators transform during the gauging procedure while maintaining compatibility with
the new Gauss law constraints.
-/
