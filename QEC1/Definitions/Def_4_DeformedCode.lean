import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Definitions.Def_3_DeformedOperator
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import Mathlib.Tactic

/-!
# Definition 4: Deformed Code

## Statement
The deformed code is the stabilizer code defined on the extended qubit system V ⊕ E(G),
whose generating checks are:
1. **Gauss's law operators** {A_v : v ∈ V} — X-type checks from Definition 2
2. **Flux operators** {B_p : p ∈ C} — Z-type checks from Definition 2
3. **Deformed checks** {s̃_j} — each original stabilizer check s_j is deformed

## Main Results
- `deformedCheck` : individual deformed check
- `DeformedCodeData` : edge-paths with boundary conditions for all checks
- `gaussLawChecks`, `fluxChecks`, `deformedOriginalChecks` : the three families of checks
- `CheckIndex` : the index type V ⊕ C ⊕ J
- `allChecks` : the full check map
- `allChecks_commute` : all checks pairwise commute
- `allChecks_self_inverse` : all checks are self-inverse
- `deformedCodeChecks` : anchor definition

## Corollaries
- Pure X/Z type classification
- Product of Gauss's law checks equals the logical
- Weight of flux checks
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace DeformedCode

open Finset PauliOp GaussFlux DeformedOperator

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-! ## Deformed Check -/

/-- Given an original check s and an edge-path γ satisfying the boundary condition,
    the deformed check is the deformed operator extension of s by γ. -/
def deformedCheck (s : PauliOp V) (γ : G.edgeSet → ZMod 2) :
    PauliOp (ExtQubit G) :=
  deformedOpExt G s γ

/-- If s has no Z-support on V, the deformed check with γ = 0 acts as s on
    vertex qubits and as identity on edge qubits. -/
theorem deformedCheck_of_noZSupport (s : PauliOp V)
    (_h : HasNoZSupportOnV s) :
    deformedCheck G s 0 = deformedOpExt G s 0 := rfl

/-- The deformed check commutes with Gauss's law when boundary condition holds. -/
theorem deformedCheck_comm_gaussLaw (s : PauliOp V) (γ : G.edgeSet → ZMod 2)
    (hbc : BoundaryCondition G s γ) (v : V) :
    PauliCommute (deformedCheck G s γ) (gaussLawOp G v) :=
  deformedOpExt_comm_gaussLaw G s γ hbc v

/-- The deformed check is self-inverse. -/
theorem deformedCheck_mul_self (s : PauliOp V) (γ : G.edgeSet → ZMod 2) :
    deformedCheck G s γ * deformedCheck G s γ = 1 :=
  deformedOpExt_mul_self G s γ

/-! ## Deformed Code Data -/

/-- The deformed code data: for each original check j, an edge-path γ_j
    and a proof that the boundary condition ∂γ_j = S_Z(s_j)|_V holds. -/
structure DeformedCodeData where
  edgePath : J → (G.edgeSet → ZMod 2)
  boundary_condition : ∀ j : J, BoundaryCondition G (checks j) (edgePath j)

/-! ## The Three Families of Checks -/

/-- Gauss's law checks on the extended system: A_v for each vertex v ∈ V. -/
def gaussLawChecks (v : V) : PauliOp (ExtQubit G) :=
  gaussLawOp G v

/-- Flux checks on the extended system: B_p for each cycle p ∈ C. -/
def fluxChecks (p : C) : PauliOp (ExtQubit G) :=
  fluxOp G cycles p

/-- Deformed original checks: s̃_j for each j ∈ J, using the edge-paths from data. -/
def deformedOriginalChecks (data : DeformedCodeData G checks) (j : J) :
    PauliOp (ExtQubit G) :=
  deformedCheck G (checks j) (data.edgePath j)

/-! ## Check Index Type -/

/-- The type of all checks in the deformed code: V ⊕ C ⊕ J. -/
inductive CheckIndex (V : Type*) (C : Type*) (J : Type*)
  | gaussLaw : V → CheckIndex V C J
  | flux : C → CheckIndex V C J
  | deformed : J → CheckIndex V C J
  deriving DecidableEq

instance [Fintype V] [Fintype C] [Fintype J] : Fintype (CheckIndex V C J) := by
  have : CheckIndex V C J ≃ (V ⊕ C ⊕ J) := {
    toFun := fun i => match i with
      | .gaussLaw v => Sum.inl v
      | .flux p => Sum.inr (Sum.inl p)
      | .deformed j => Sum.inr (Sum.inr j)
    invFun := fun s => match s with
      | Sum.inl v => .gaussLaw v
      | Sum.inr (Sum.inl p) => .flux p
      | Sum.inr (Sum.inr j) => .deformed j
    left_inv := fun i => by cases i <;> rfl
    right_inv := fun s => by rcases s with v | p | j <;> rfl
  }
  exact Fintype.ofEquiv _ this.symm

/-! ## All Checks Map -/

/-- The full set of checks for the deformed code. -/
def allChecks (data : DeformedCodeData G checks) :
    CheckIndex V C J → PauliOp (ExtQubit G)
  | .gaussLaw v => gaussLawChecks G v
  | .flux p => fluxChecks G cycles p
  | .deformed j => deformedOriginalChecks G checks data j

/-! ## Pairwise Commutation: Gauss-Gauss -/

/-- Gauss's law checks commute with each other. -/
theorem allChecks_pairwise_commute_gaussLaw_gaussLaw (v w : V) :
    PauliCommute (gaussLawChecks G v) (gaussLawChecks G w) :=
  gaussLaw_commute G v w

/-! ## Pairwise Commutation: Flux-Flux -/

/-- Flux checks commute with each other. -/
theorem allChecks_pairwise_commute_flux_flux (p q : C) :
    PauliCommute (fluxChecks G cycles p) (fluxChecks G cycles q) :=
  flux_commute G cycles p q

/-! ## Pairwise Commutation: Gauss-Flux -/

/-- Gauss's law and flux checks commute. -/
theorem allChecks_pairwise_commute_gaussLaw_flux
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (v : V) (p : C) :
    PauliCommute (gaussLawChecks G v) (fluxChecks G cycles p) :=
  gauss_flux_commute G cycles hcyc v p

/-! ## Pairwise Commutation: Gauss-Deformed -/

/-- Gauss's law checks commute with deformed original checks. -/
theorem allChecks_pairwise_commute_gaussLaw_deformed
    (data : DeformedCodeData G checks) (v : V) (j : J) :
    PauliCommute (gaussLawChecks G v) (deformedOriginalChecks G checks data j) := by
  rw [PauliOp.pauliCommute_comm]
  exact deformedOpExt_comm_gaussLaw G (checks j) (data.edgePath j) (data.boundary_condition j) v

/-! ## Pairwise Commutation: Deformed-Flux -/

/-- Deformed and flux checks commute. This holds because flux operators are pure Z-type
    and deformed checks have no X-support on edges. -/
theorem allChecks_pairwise_commute_deformed_flux
    (data : DeformedCodeData G checks) (j : J) (p : C) :
    PauliCommute (deformedOriginalChecks G checks data j) (fluxChecks G cycles p) := by
  unfold deformedOriginalChecks deformedCheck fluxChecks
  simp only [PauliCommute, symplecticInner]
  rw [Fintype.sum_sum_type]
  -- Vertex part: flux has z=0 and x=0 on vertices
  have h_vertex : ∑ v : V,
      ((deformedOpExt G (checks j) (data.edgePath j)).xVec (Sum.inl v) *
       (fluxOp G cycles p).zVec (Sum.inl v) +
       (deformedOpExt G (checks j) (data.edgePath j)).zVec (Sum.inl v) *
       (fluxOp G cycles p).xVec (Sum.inl v)) = 0 := by
    apply Finset.sum_eq_zero; intro v _
    simp [deformedOpExt, fluxOp]
  rw [h_vertex, zero_add]
  -- Edge part: deformed has x=0 on edges, flux has x=0 everywhere
  have h_edge : ∑ e : G.edgeSet,
      ((deformedOpExt G (checks j) (data.edgePath j)).xVec (Sum.inr e) *
       (fluxOp G cycles p).zVec (Sum.inr e) +
       (deformedOpExt G (checks j) (data.edgePath j)).zVec (Sum.inr e) *
       (fluxOp G cycles p).xVec (Sum.inr e)) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    simp [deformedOpExt, fluxOp]
  exact h_edge

/-! ## Pairwise Commutation: Deformed-Deformed -/

/-- Deformed checks commute if the original checks commute.
    On edges both are pure Z-type (Z commutes with Z);
    on vertices the commutation is inherited from the original checks. -/
theorem allChecks_pairwise_commute_deformed_deformed
    (data : DeformedCodeData G checks)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (i j : J) :
    PauliCommute (deformedOriginalChecks G checks data i)
                 (deformedOriginalChecks G checks data j) := by
  unfold deformedOriginalChecks deformedCheck
  simp only [PauliCommute, symplecticInner]
  rw [Fintype.sum_sum_type]
  -- Edge part: both are pure Z on edges, so x*z + z*x = 0*z + z*0 = 0
  have h_edge : ∑ e : G.edgeSet,
      ((deformedOpExt G (checks i) (data.edgePath i)).xVec (Sum.inr e) *
       (deformedOpExt G (checks j) (data.edgePath j)).zVec (Sum.inr e) +
       (deformedOpExt G (checks i) (data.edgePath i)).zVec (Sum.inr e) *
       (deformedOpExt G (checks j) (data.edgePath j)).xVec (Sum.inr e)) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    simp [deformedOpExt]
  -- Vertex part: inherited from original check commutation
  have h_vertex : ∑ v : V,
      ((deformedOpExt G (checks i) (data.edgePath i)).xVec (Sum.inl v) *
       (deformedOpExt G (checks j) (data.edgePath j)).zVec (Sum.inl v) +
       (deformedOpExt G (checks i) (data.edgePath i)).zVec (Sum.inl v) *
       (deformedOpExt G (checks j) (data.edgePath j)).xVec (Sum.inl v)) = 0 := by
    have hij := hcomm i j
    simp only [PauliCommute, symplecticInner] at hij
    convert hij using 1
  rw [h_vertex, h_edge, add_zero]

/-! ## All Checks Commute -/

/-- All checks in the deformed code pairwise commute. -/
theorem allChecks_commute
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (a b : CheckIndex V C J) :
    PauliCommute (allChecks G cycles checks data a) (allChecks G cycles checks data b) := by
  cases a with
  | gaussLaw v =>
    cases b with
    | gaussLaw w => exact allChecks_pairwise_commute_gaussLaw_gaussLaw G v w
    | flux p => exact allChecks_pairwise_commute_gaussLaw_flux G cycles hcyc v p
    | deformed j => exact allChecks_pairwise_commute_gaussLaw_deformed G checks data v j
  | flux p =>
    cases b with
    | gaussLaw v =>
      rw [PauliOp.pauliCommute_comm]
      exact allChecks_pairwise_commute_gaussLaw_flux G cycles hcyc v p
    | flux q => exact allChecks_pairwise_commute_flux_flux G cycles p q
    | deformed j =>
      rw [PauliOp.pauliCommute_comm]
      exact allChecks_pairwise_commute_deformed_flux G cycles checks data j p
  | deformed i =>
    cases b with
    | gaussLaw v =>
      rw [PauliOp.pauliCommute_comm]
      exact allChecks_pairwise_commute_gaussLaw_deformed G checks data v i
    | flux p => exact allChecks_pairwise_commute_deformed_flux G cycles checks data i p
    | deformed j =>
      exact allChecks_pairwise_commute_deformed_deformed G checks data hcomm i j

/-! ## Self-Inverse Properties -/

/-- Gauss's law checks are self-inverse: A_v * A_v = 1. -/
theorem gaussLawChecks_mul_self (v : V) :
    gaussLawChecks G v * gaussLawChecks G v = 1 :=
  PauliOp.mul_self _

/-- Flux checks are self-inverse: B_p * B_p = 1. -/
theorem fluxChecks_mul_self (p : C) :
    fluxChecks G cycles p * fluxChecks G cycles p = 1 :=
  PauliOp.mul_self _

/-- Deformed original checks are self-inverse: s̃_j * s̃_j = 1. -/
theorem deformedOriginalChecks_mul_self
    (data : DeformedCodeData G checks) (j : J) :
    deformedOriginalChecks G checks data j * deformedOriginalChecks G checks data j = 1 :=
  deformedCheck_mul_self G (checks j) (data.edgePath j)

/-- All checks in the deformed code are self-inverse. -/
theorem allChecks_self_inverse
    (data : DeformedCodeData G checks) (a : CheckIndex V C J) :
    allChecks G cycles checks data a * allChecks G cycles checks data a = 1 := by
  cases a with
  | gaussLaw v => exact gaussLawChecks_mul_self G v
  | flux p => exact fluxChecks_mul_self G cycles p
  | deformed j => exact deformedOriginalChecks_mul_self G checks data j

/-! ## Type Classification -/

/-- Gauss's law checks are pure X-type: no Z-support. -/
theorem gaussLawChecks_pure_X (v : V) :
    (gaussLawChecks G v).zVec = 0 :=
  gaussLawOp_zVec G v

/-- Flux checks are pure Z-type: no X-support. -/
theorem fluxChecks_pure_Z (p : C) :
    (fluxChecks G cycles p).xVec = 0 :=
  fluxOp_xVec G cycles p

/-- Deformed checks have no X-support on edge qubits. -/
theorem deformedOriginalChecks_no_xSupport_on_edges
    (data : DeformedCodeData G checks) (j : J) (e : G.edgeSet) :
    (deformedOriginalChecks G checks data j).xVec (Sum.inr e) = 0 :=
  deformedOpExt_xVec_edge G (checks j) (data.edgePath j) e

/-! ## Product of Gauss's Law Checks Equals Logical -/

/-- The product of all Gauss's law checks equals the logical operator L. -/
theorem gaussLawChecks_product_eq_logical :
    (∏ v : V, gaussLawChecks G v) = logicalOp G := by
  convert gaussLaw_product G using 1

/-! ## Constructors for DeformedCodeData -/

/-- Constructor: given edge-paths and boundary proofs, build DeformedCodeData. -/
def mkDeformedCodeData
    (edgePaths : J → (G.edgeSet → ZMod 2))
    (hbc : ∀ j : J, BoundaryCondition G (checks j) (edgePaths j)) :
    DeformedCodeData G checks :=
  ⟨edgePaths, hbc⟩

/-- Constructor for when all original checks have no Z-support on V:
    set all edge-paths to zero. -/
def mkDeformedCodeData_noZSupport
    (hnoZ : ∀ j : J, HasNoZSupportOnV (checks j)) :
    DeformedCodeData G checks :=
  ⟨fun _ => 0, fun j => noZSupport_boundary_zero G (checks j) (hnoZ j)⟩

/-! ## Weight of Flux Checks -/

/-- Helper: In ZMod 2, a ≠ 0 ↔ a = 1. -/
private lemma zmod2_ne_zero_iff_eq_one (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  fin_cases a <;> simp

/-- The weight of flux check B_p equals the number of edges in the cycle p. -/
theorem fluxChecks_weight (p : C) :
    (fluxChecks G cycles p).weight =
    (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles p)).card := by
  unfold fluxChecks PauliOp.weight
  have h_supportX : (fluxOp G cycles p).supportX = ∅ :=
    fluxOp_is_pure_Z G cycles p
  have h_supportZ : (fluxOp G cycles p).supportZ =
      (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles p)).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext q
    simp only [PauliOp.supportZ, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_map, Function.Embedding.coeFn_mk]
    cases q with
    | inl v =>
      constructor
      · intro h; simp [fluxOp] at h
      · rintro ⟨e, _, he⟩; exact absurd he (by simp)
    | inr e =>
      constructor
      · intro h
        refine ⟨e, ?_, rfl⟩
        simp only [fluxOp] at h
        by_contra hne
        simp [hne] at h
      · rintro ⟨e', he', heq⟩
        have : e' = e := Sum.inr_injective heq
        subst this
        simp [fluxOp, if_pos he']
  rw [PauliOp.support_eq_supportX_union_supportZ, h_supportX, Finset.empty_union, h_supportZ]
  rw [Finset.card_map]

/-! ## Anchor Definition: deformedCodeChecks -/

/-- The generating checks for the deformed code on the extended qubit system V ⊕ E(G).
    This is the main definition from Definition 4 of the paper. -/
def deformedCodeChecks
    (data : DeformedCodeData G checks) :
    CheckIndex V C J → PauliOp (ExtQubit G) :=
  allChecks G cycles checks data

@[simp]
theorem deformedCodeChecks_gaussLaw (data : DeformedCodeData G checks) (v : V) :
    deformedCodeChecks G cycles checks data (.gaussLaw v) = gaussLawChecks G v := rfl

@[simp]
theorem deformedCodeChecks_flux (data : DeformedCodeData G checks) (p : C) :
    deformedCodeChecks G cycles checks data (.flux p) = fluxChecks G cycles p := rfl

@[simp]
theorem deformedCodeChecks_deformed (data : DeformedCodeData G checks) (j : J) :
    deformedCodeChecks G cycles checks data (.deformed j) =
    deformedOriginalChecks G checks data j := rfl

end DeformedCode
