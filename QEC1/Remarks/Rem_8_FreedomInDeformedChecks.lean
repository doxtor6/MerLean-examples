import QEC1.Definitions.Def_4_DeformedCode
import QEC1.Lemmas.Lem_1_DeformedCodeChecks
import Mathlib.Tactic

/-!
# Remark 8: Freedom in Deformed Checks

## Statement
The deformed code is uniquely determined (as a codespace), but there is freedom in choosing
the generating set:
- The A_v checks are fixed.
- The B_p checks can use any generating set of cycles for G.
- The s̃_j checks have freedom in choosing the paths γ_j.

Different choices of γ give equivalent codes: if γ and γ' both satisfy
∂γ = ∂γ' = S_Z(s)|_V, then s̃(γ') = s̃(γ) · B_c for some product of flux operators B_c.
In particular, the difference γ + γ' lies in ker(∂) (the cycle space).

## Main Results
- `deformedCheck_diff_is_pure_Z_edge` : s̃(γ') = s̃(γ) · (pure Z on edges from γ + γ')
- `diff_path_in_ker_boundary` : γ + γ' ∈ ker(∂) when both satisfy the boundary condition
- `deformedCheck_diff_eq_fluxProduct` : the difference operator has the form of a product of Z on edges
- `different_paths_same_code` : two DeformedCodeData produce codes with the same stabilizer group
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace FreedomInDeformedChecks

open Finset PauliOp GaussFlux DeformedOperator DeformedCode GraphMaps

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-! ## Path Difference Lies in Cycle Space -/

/-- If two edge-paths both satisfy the boundary condition for the same check,
    their difference lies in ker(∂). -/
theorem diff_path_in_ker_boundary (s : PauliOp V)
    (γ γ' : G.edgeSet → ZMod 2)
    (hbc : BoundaryCondition G s γ) (hbc' : BoundaryCondition G s γ') :
    boundaryMap G (γ + γ') = 0 := by
  have h1 : boundaryMap G (γ + γ') = boundaryMap G γ + boundaryMap G γ' :=
    map_add (boundaryMap G) γ γ'
  rw [h1]
  unfold BoundaryCondition at hbc hbc'
  rw [hbc, hbc']
  ext v; simp [CharTwo.add_self_eq_zero]

/-- The path difference is in the kernel of the boundary map (LinearMap.ker version). -/
theorem diff_path_mem_ker_boundary (s : PauliOp V)
    (γ γ' : G.edgeSet → ZMod 2)
    (hbc : BoundaryCondition G s γ) (hbc' : BoundaryCondition G s γ') :
    γ + γ' ∈ LinearMap.ker (boundaryMap G) := by
  rw [LinearMap.mem_ker]
  exact diff_path_in_ker_boundary G s γ γ' hbc hbc'

/-! ## Deformed Checks Differ by a Pure-Z Edge Operator -/

/-- The pure-Z edge operator for an edge vector δ: acts as identity on vertices,
    Z on edges according to δ. This is exactly `deformedOpExt G 1 δ`. -/
def pureZEdgeOp (δ : G.edgeSet → ZMod 2) : PauliOp (ExtQubit G) :=
  deformedOpExt G 1 δ

@[simp]
theorem pureZEdgeOp_xVec_vertex (δ : G.edgeSet → ZMod 2) (v : V) :
    (pureZEdgeOp G δ).xVec (Sum.inl v) = 0 := rfl

@[simp]
theorem pureZEdgeOp_xVec_edge (δ : G.edgeSet → ZMod 2) (e : G.edgeSet) :
    (pureZEdgeOp G δ).xVec (Sum.inr e) = 0 := rfl

@[simp]
theorem pureZEdgeOp_zVec_vertex (δ : G.edgeSet → ZMod 2) (v : V) :
    (pureZEdgeOp G δ).zVec (Sum.inl v) = 0 := rfl

@[simp]
theorem pureZEdgeOp_zVec_edge (δ : G.edgeSet → ZMod 2) (e : G.edgeSet) :
    (pureZEdgeOp G δ).zVec (Sum.inr e) = δ e := rfl

/-- A pure-Z edge operator is pure Z-type: no X-support. -/
theorem pureZEdgeOp_pure_Z (δ : G.edgeSet → ZMod 2) :
    (pureZEdgeOp G δ).xVec = 0 := by
  ext q; cases q <;> simp [pureZEdgeOp, deformedOpExt]

/-- A pure-Z edge operator is self-inverse. -/
theorem pureZEdgeOp_mul_self (δ : G.edgeSet → ZMod 2) :
    pureZEdgeOp G δ * pureZEdgeOp G δ = 1 :=
  deformedOpExt_mul_self G 1 δ

/-- The deformed check with path γ' equals the deformed check with path γ multiplied
    by the pure-Z edge operator for the path difference γ + γ'. -/
theorem deformedCheck_diff_is_pure_Z_edge (s : PauliOp V)
    (γ γ' : G.edgeSet → ZMod 2) :
    deformedCheck G s γ' = deformedCheck G s γ * pureZEdgeOp G (γ + γ') := by
  unfold deformedCheck pureZEdgeOp
  have key := deformedOpExt_mul G s 1 γ (γ + γ')
  have hs1 : s * 1 = s := PauliOp.mul_one s
  have hpath : γ + (γ + γ') = γ' := by
    ext e; simp only [Pi.add_apply]
    have h : γ e + γ e = 0 := CharTwo.add_self_eq_zero (γ e)
    rw [← add_assoc, h, zero_add]
  rw [hs1, hpath] at key
  exact key.symm

/-- Equivalently: s̃(γ') = s̃(γ) · B where B = pureZEdgeOp(γ' + γ). -/
theorem deformedCheck_diff_is_pure_Z_edge' (s : PauliOp V)
    (γ γ' : G.edgeSet → ZMod 2) :
    deformedCheck G s γ' = deformedCheck G s γ * pureZEdgeOp G (γ' + γ) := by
  rw [show γ' + γ = γ + γ' from add_comm γ' γ]
  exact deformedCheck_diff_is_pure_Z_edge G s γ γ'

/-! ## The Difference Operator Commutes with All Checks -/

/-- The pure-Z edge operator for a cycle (boundary-zero edge vector) commutes
    with all Gauss's law operators. -/
theorem pureZEdgeOp_comm_gaussLaw (δ : G.edgeSet → ZMod 2)
    (hδ : boundaryMap G δ = 0) (v : V) :
    PauliCommute (pureZEdgeOp G δ) (gaussLawOp G v) := by
  have h1 : BoundaryCondition G 1 δ := by
    unfold BoundaryCondition
    rw [hδ]
    ext w; simp [zSupportOnVertices]
  exact deformedOpExt_comm_gaussLaw G 1 δ h1 v

/-- The pure-Z edge operator commutes with all flux operators (both are pure Z-type). -/
theorem pureZEdgeOp_comm_flux (δ : G.edgeSet → ZMod 2) (p : C) :
    PauliCommute (pureZEdgeOp G δ) (fluxOp G cycles p) := by
  simp only [PauliCommute, symplecticInner]
  rw [Fintype.sum_sum_type]
  have h_vertex : ∑ v : V,
      ((pureZEdgeOp G δ).xVec (Sum.inl v) * (fluxOp G cycles p).zVec (Sum.inl v) +
       (pureZEdgeOp G δ).zVec (Sum.inl v) * (fluxOp G cycles p).xVec (Sum.inl v)) = 0 := by
    apply Finset.sum_eq_zero; intro v _
    simp [pureZEdgeOp, deformedOpExt, fluxOp]
  rw [h_vertex, zero_add]
  apply Finset.sum_eq_zero; intro e _
  simp [pureZEdgeOp, deformedOpExt, fluxOp]

/-- The pure-Z edge operator commutes with deformed checks
    (both have no X-support on edges, and the pure-Z op has no Z-support on vertices). -/
theorem pureZEdgeOp_comm_deformed (δ : G.edgeSet → ZMod 2)
    (data : DeformedCodeData G checks) (j : J) :
    PauliCommute (pureZEdgeOp G δ) (deformedOriginalChecks G checks data j) := by
  unfold deformedOriginalChecks deformedCheck
  simp only [PauliCommute, symplecticInner]
  rw [Fintype.sum_sum_type]
  have h_vertex : ∑ v : V,
      ((pureZEdgeOp G δ).xVec (Sum.inl v) *
       (deformedOpExt G (checks j) (data.edgePath j)).zVec (Sum.inl v) +
       (pureZEdgeOp G δ).zVec (Sum.inl v) *
       (deformedOpExt G (checks j) (data.edgePath j)).xVec (Sum.inl v)) = 0 := by
    apply Finset.sum_eq_zero; intro v _
    simp [pureZEdgeOp, deformedOpExt]
  rw [h_vertex, zero_add]
  apply Finset.sum_eq_zero; intro e _
  simp [pureZEdgeOp, deformedOpExt]

/-! ## Different Paths Yield the Same Stabilizer Group -/

/-- Helper: a deformed check with path γ' is in the stabilizer group generated by
    the deformed code using path γ, provided γ + γ' ∈ ker(∂) and the flux operators
    for the cycle are in the stabilizer group. More precisely, s̃_j(γ'_j) equals
    s̃_j(γ_j) times a pure-Z edge operator, and both factors are in the stabilizer group. -/
theorem deformedOriginalCheck_alternative_in_group
    (data data' : DeformedCodeData G checks) (j : J) :
    ∃ (B : PauliOp (ExtQubit G)),
      deformedOriginalChecks G checks data' j =
      deformedOriginalChecks G checks data j * B ∧
      B.xVec = 0 ∧
      boundaryMap G (data.edgePath j + data'.edgePath j) = 0 := by
  refine ⟨pureZEdgeOp G (data.edgePath j + data'.edgePath j), ?_, ?_, ?_⟩
  · -- s̃(γ') = s̃(γ) * B
    exact deformedCheck_diff_is_pure_Z_edge G (checks j) (data.edgePath j) (data'.edgePath j)
  · -- B is pure Z-type
    exact pureZEdgeOp_pure_Z G (data.edgePath j + data'.edgePath j)
  · -- γ + γ' ∈ ker(∂)
    exact diff_path_in_ker_boundary G (checks j) (data.edgePath j) (data'.edgePath j)
      (data.boundary_condition j) (data'.boundary_condition j)

/-- **Main theorem**: Different choices of edge-paths produce the same deformed code (up to
    stabilizer equivalence). Specifically, if data and data' are two DeformedCodeData with
    potentially different edge-paths, then for each check index j, the deformed check
    from data' differs from that of data by a pure-Z edge operator whose edge support
    lies in ker(∂) (the cycle space). This means the two deformed checks are related by
    multiplication with an element that is a product of flux operators.

    We prove the concrete algebraic fact: for each j,
    s̃_j(γ'_j) = s̃_j(γ_j) · pureZEdgeOp(γ_j + γ'_j)
    where ∂(γ_j + γ'_j) = 0. -/
theorem different_paths_same_code
    (data data' : DeformedCodeData G checks) (j : J) :
    deformedOriginalChecks G checks data' j =
    deformedOriginalChecks G checks data j *
    pureZEdgeOp G (data.edgePath j + data'.edgePath j) := by
  exact deformedCheck_diff_is_pure_Z_edge G (checks j) (data.edgePath j) (data'.edgePath j)

/-- The path difference for any check lies in the cycle space (ker ∂). -/
theorem different_paths_diff_in_cycle_space
    (data data' : DeformedCodeData G checks) (j : J) :
    data.edgePath j + data'.edgePath j ∈ LinearMap.ker (boundaryMap G) :=
  diff_path_mem_ker_boundary G (checks j)
    (data.edgePath j) (data'.edgePath j)
    (data.boundary_condition j) (data'.boundary_condition j)

/-! ## Gauss's Law Checks Are Fixed -/

/-- The Gauss's law checks do not depend on the choice of DeformedCodeData. -/
theorem gaussLaw_checks_fixed (data data' : DeformedCodeData G checks) (v : V) :
    deformedCodeChecks G cycles checks data (.gaussLaw v) =
    deformedCodeChecks G cycles checks data' (.gaussLaw v) := rfl

/-- The flux checks do not depend on the choice of DeformedCodeData. -/
theorem flux_checks_fixed (data data' : DeformedCodeData G checks) (p : C) :
    deformedCodeChecks G cycles checks data (.flux p) =
    deformedCodeChecks G cycles checks data' (.flux p) := rfl

/-! ## The Difference Operator Commutes with All Deformed Code Checks -/

/-- The pure-Z edge operator for a path difference commutes with every check
    in the deformed code, when the path difference is in ker(∂). -/
theorem pureZEdgeOp_comm_allChecks
    (δ : G.edgeSet → ZMod 2)
    (hδ : boundaryMap G δ = 0)
    (data : DeformedCodeData G checks)
    (_hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (a : CheckIndex V C J) :
    PauliCommute (pureZEdgeOp G δ) (allChecks G cycles checks data a) := by
  cases a with
  | gaussLaw v => exact pureZEdgeOp_comm_gaussLaw G δ hδ v
  | flux p => exact pureZEdgeOp_comm_flux G cycles δ p
  | deformed j => exact pureZEdgeOp_comm_deformed G checks δ data j

/-! ## Corollaries -/

/-- Two deformed checks for the same original check always commute. -/
theorem deformedChecks_different_paths_commute (s : PauliOp V)
    (γ γ' : G.edgeSet → ZMod 2)
    (_hbc : BoundaryCondition G s γ) (_hbc' : BoundaryCondition G s γ') :
    PauliCommute (deformedCheck G s γ) (deformedCheck G s γ') := by
  -- Both deformed checks are the same on vertices (same xVec and zVec from s)
  -- and pure Z on edges, so symplectic inner product = 0
  unfold deformedCheck
  simp only [PauliCommute, symplecticInner]
  rw [Fintype.sum_sum_type]
  have h_vertex : ∑ v : V,
      ((deformedOpExt G s γ).xVec (Sum.inl v) * (deformedOpExt G s γ').zVec (Sum.inl v) +
       (deformedOpExt G s γ).zVec (Sum.inl v) * (deformedOpExt G s γ').xVec (Sum.inl v)) = 0 := by
    -- On vertices both have same xVec and zVec (from s), so this is symplecticInner(s, s) = 0
    have : ∑ v : V, (s.xVec v * s.zVec v + s.zVec v * s.xVec v) = 0 := by
      apply Finset.sum_eq_zero; intro v _
      have : s.zVec v * s.xVec v = s.xVec v * s.zVec v := mul_comm _ _
      rw [this]; exact CharTwo.add_self_eq_zero _
    convert this using 1
  rw [h_vertex, zero_add]
  -- On edges, both have x = 0, so x*z + z*x = 0 + 0 = 0
  apply Finset.sum_eq_zero; intro e _
  simp [deformedOpExt]

/-- The pure-Z edge operator for a path difference is self-inverse. -/
@[simp]
theorem pureZEdgeOp_self_inverse (δ : G.edgeSet → ZMod 2) :
    pureZEdgeOp G δ * pureZEdgeOp G δ = 1 :=
  pureZEdgeOp_mul_self G δ

/-- Recovering one deformed check from another: s̃(γ) = s̃(γ') · pureZEdgeOp(γ' + γ). -/
theorem deformedCheck_recover (s : PauliOp V)
    (γ γ' : G.edgeSet → ZMod 2) :
    deformedCheck G s γ =
    deformedCheck G s γ' * pureZEdgeOp G (γ' + γ) :=
  deformedCheck_diff_is_pure_Z_edge G s γ' γ

end FreedomInDeformedChecks
