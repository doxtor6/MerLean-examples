import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Remarks.Rem_2_NotationPauliOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Tactic

/-!
# Definition 3: Deformed Operator

## Statement
A Pauli operator P that commutes with the logical operator L = ∏_{v ∈ V} X_v can be
written as P̃ = P · ∏_{e ∈ γ} Z_e on the extended qubit system V ⊕ E, where γ is an
edge-path satisfying the boundary condition ∂γ = S_Z(P)|_V.

## Main Results
- `zSupportOnVertices` : Z-support of P restricted to graph vertices
- `CommutesWithLogical` : sum of Z-support on V is 0 in ZMod 2
- `BoundaryCondition` : ∂γ = zSupportOnVertices(P)
- `deformedOpExt` : the deformed operator on V ⊕ E
- `deformedOpExt_comm_gaussLaw` : P̃ commutes with A_v when boundary condition holds
- `deformedOpExt_mul_self` : P̃ is self-inverse
- `boundaryCondition_implies_commutes` : boundary condition ⟹ commutes with logical
- `deformedOperator` : anchor definition bundling P, γ, and boundary condition proof

## Corollaries
- Vertex/edge evaluation @[simp] lemmas
- X/Z-support characterizations
- Compatibility with multiplication
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace DeformedOperator

open Finset PauliOp GaussFlux GraphMaps

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## Z-Support on Vertices -/

/-- The Z-support of a Pauli operator P restricted to the graph vertices V,
    expressed as a binary vector in ZMod 2^V. This is the characteristic function
    of S_Z(P) ∩ V: zSupportOnVertices(P)(v) = 1 if P has Z-action at v (i.e., P.zVec v ≠ 0),
    and 0 otherwise. -/
def zSupportOnVertices (P : PauliOp V) : V → ZMod 2 :=
  fun v => if P.zVec v ≠ 0 then 1 else 0

/-- In ZMod 2, a ≠ 0 ↔ a = 1. -/
private lemma zmod2_ne_zero_iff' (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  fin_cases a <;> simp

/-! ## Commutes With Logical -/

/-- A Pauli operator P commutes with the logical L = ∏_{v ∈ V} X_v if the
    sum of its Z-support on vertices is 0 in ZMod 2 (i.e., even number of
    vertices with Z-action). -/
def CommutesWithLogical (P : PauliOp V) : Prop :=
  ∑ v : V, zSupportOnVertices P v = 0

/-! ## Boundary Condition -/

/-- The boundary condition: ∂γ = zSupportOnVertices(P), i.e., the boundary
    of the edge-path γ equals the Z-support of P restricted to V.
    This is a condition on the choice of edge-path γ given P. -/
def BoundaryCondition (P : PauliOp V) (γ : G.edgeSet → ZMod 2) : Prop :=
  boundaryMap G γ = zSupportOnVertices P

/-! ## Deformed Operator on Extended Qubits -/

/-- The deformed operator P̃ on the extended qubit system V ⊕ G.edgeSet.
    Given a Pauli operator P on V and an edge-path γ (binary vector on edges):
    - On vertex qubits: acts as P (preserves both xVec and zVec)
    - On edge qubits: acts as Z_e if γ(e) = 1, identity if γ(e) = 0
      (i.e., xVec = 0 on edges, zVec = γ(e) on edges) -/
def deformedOpExt (P : PauliOp V) (γ : G.edgeSet → ZMod 2) :
    PauliOp (ExtQubit G) where
  xVec := fun q => match q with
    | Sum.inl v => P.xVec v
    | Sum.inr _ => 0
  zVec := fun q => match q with
    | Sum.inl v => P.zVec v
    | Sum.inr e => γ e

/-! ## Vertex and Edge Evaluation @[simp] Lemmas -/

/-- The deformed operator's X-vector on vertex qubit v equals P's X-vector. -/
@[simp]
theorem deformedOpExt_xVec_vertex (P : PauliOp V) (γ : G.edgeSet → ZMod 2) (v : V) :
    (deformedOpExt G P γ).xVec (Sum.inl v) = P.xVec v := rfl

/-- The deformed operator's Z-vector on vertex qubit v equals P's Z-vector. -/
@[simp]
theorem deformedOpExt_zVec_vertex (P : PauliOp V) (γ : G.edgeSet → ZMod 2) (v : V) :
    (deformedOpExt G P γ).zVec (Sum.inl v) = P.zVec v := rfl

/-- The deformed operator has no X-action on edge qubits: xVec is 0 on edges. -/
@[simp]
theorem deformedOpExt_xVec_edge (P : PauliOp V) (γ : G.edgeSet → ZMod 2) (e : G.edgeSet) :
    (deformedOpExt G P γ).xVec (Sum.inr e) = 0 := rfl

/-- The deformed operator's Z-vector on edge qubit e equals γ(e). -/
@[simp]
theorem deformedOpExt_zVec_edge (P : PauliOp V) (γ : G.edgeSet → ZMod 2) (e : G.edgeSet) :
    (deformedOpExt G P γ).zVec (Sum.inr e) = γ e := rfl

/-! ## Deforming with Special Inputs -/

/-- Deforming the identity operator with edge-path γ gives a pure-Z edge operator. -/
theorem deformedOpExt_one (γ : G.edgeSet → ZMod 2) :
    deformedOpExt G 1 γ =
    { xVec := fun q => match q with | Sum.inl _ => 0 | Sum.inr _ => 0
      zVec := fun q => match q with | Sum.inl _ => 0 | Sum.inr e => γ e } := by
  ext q <;> cases q <;> simp [deformedOpExt]

/-- Deforming with the zero edge-path extends P trivially to edge qubits. -/
theorem deformedOpExt_zero_path (P : PauliOp V) :
    deformedOpExt G P 0 =
    { xVec := fun q => match q with | Sum.inl v => P.xVec v | Sum.inr _ => 0
      zVec := fun q => match q with | Sum.inl v => P.zVec v | Sum.inr _ => 0 } := by
  ext q <;> cases q <;> simp [deformedOpExt]

/-! ## X-Support and Z-Support Characterization -/

/-- The deformed operator preserves X-support on vertex qubits. -/
theorem deformedOpExt_xSupport_vertex (P : PauliOp V) (γ : G.edgeSet → ZMod 2) (v : V) :
    (deformedOpExt G P γ).xVec (Sum.inl v) ≠ 0 ↔ P.xVec v ≠ 0 := by
  simp [deformedOpExt]

/-- The Z-support of the deformed operator on vertex qubits matches P. -/
theorem deformedOpExt_zSupport_vertex (P : PauliOp V) (γ : G.edgeSet → ZMod 2) (v : V) :
    (deformedOpExt G P γ).zVec (Sum.inl v) ≠ 0 ↔ P.zVec v ≠ 0 := by
  simp [deformedOpExt]

/-- The Z-support of the deformed operator on edge qubits matches γ. -/
theorem deformedOpExt_zSupport_edge (P : PauliOp V) (γ : G.edgeSet → ZMod 2) (e : G.edgeSet) :
    (deformedOpExt G P γ).zVec (Sum.inr e) ≠ 0 ↔ γ e ≠ 0 := by
  simp [deformedOpExt]

/-- The Z-action on edges is exactly γ(e) = 1. -/
theorem deformedOpExt_hasZAction_edge (P : PauliOp V) (γ : G.edgeSet → ZMod 2)
    (e : G.edgeSet) :
    (deformedOpExt G P γ).zVec (Sum.inr e) ≠ 0 ↔ γ e = 1 := by
  simp only [deformedOpExt_zVec_edge, ne_eq]
  exact zmod2_ne_zero_iff' (γ e)

/-! ## Self-Inverse Property -/

/-- The deformed operator is self-inverse: P̃ · P̃ = 1. -/
theorem deformedOpExt_mul_self (P : PauliOp V) (γ : G.edgeSet → ZMod 2) :
    deformedOpExt G P γ * deformedOpExt G P γ = 1 := by
  ext q
  · -- xVec
    cases q with
    | inl v => simp [deformedOpExt, CharTwo.add_self_eq_zero]
    | inr e => simp [deformedOpExt]
  · -- zVec
    cases q with
    | inl v => simp [deformedOpExt, CharTwo.add_self_eq_zero]
    | inr e => simp [deformedOpExt, CharTwo.add_self_eq_zero]

/-! ## Sum of Z-Support Equals Cardinality -/

/-- The sum of the Z-support indicator equals the cardinality of the Z-support finset
    cast to ZMod 2. -/
lemma sum_zSupportOnVertices_eq_card (P : PauliOp V) :
    ∑ v : V, zSupportOnVertices P v =
    (↑(Finset.univ.filter (fun v => P.zVec v ≠ 0)).card : ZMod 2) := by
  simp only [zSupportOnVertices]
  conv_rhs => rw [← Finset.sum_boole]

/-! ## Commutativity Iff Even Z-Support -/

/-- The commutativity condition holds iff the Z-support on V has even cardinality. -/
theorem commutesWithLogical_iff_even_zSupport (P : PauliOp V) :
    CommutesWithLogical P ↔
    Even (Finset.univ.filter (fun v => P.zVec v ≠ 0)).card := by
  unfold CommutesWithLogical
  rw [sum_zSupportOnVertices_eq_card]
  exact ZMod.natCast_eq_zero_iff_even

/-! ## Boundary Condition Implies Commutativity -/

/-- The sum of the boundary map over all vertices is 0, since each edge
    contributes to exactly two vertices. -/
theorem boundary_sum_eq_zero (γ : G.edgeSet → ZMod 2) :
    ∑ v : V, boundaryMap G γ v = 0 := by
  simp only [boundaryMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  have h_sum : ∑ v : V, (if v ∈ (e : Sym2 V) then γ e else 0) =
      (∑ v : V, if v ∈ (e : Sym2 V) then (1 : ZMod 2) else 0) * γ e := by
    rw [Finset.sum_mul]
    congr 1; ext v
    split
    · simp
    · simp
  rw [h_sum]
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      intro h; subst h; exact G.loopless a (G.mem_edgeSet.mp he)
    have h_count : ∑ v : V, (if v ∈ (⟨s(a, b), he⟩ : G.edgeSet).val then (1 : ZMod 2) else 0) =
        ∑ v : V, (if v ∈ s(a, b) then (1 : ZMod 2) else 0) := rfl
    rw [h_count]
    have h_eq : ∀ v : V, (if v ∈ s(a, b) then (1 : ZMod 2) else 0) =
        (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
      intro v
      by_cases hva : v = a
      · subst hva; simp [Sym2.mem_iff, hab]
      · by_cases hvb : v = b
        · subst hvb; simp [Sym2.mem_iff, hva]
        · have : v ∉ s(a, b) := by rw [Sym2.mem_iff]; push_neg; exact ⟨hva, hvb⟩
          simp [this, hva, hvb]
    simp_rw [h_eq]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp [CharTwo.add_self_eq_zero]

/-- If the boundary condition ∂γ = S_Z(P)|_V holds, then the commutativity condition
    holds. This is because Σ_v (∂γ)_v = 0 in ZMod 2, since each edge contributes to
    exactly two vertices. -/
theorem boundaryCondition_implies_commutes (P : PauliOp V) (γ : G.edgeSet → ZMod 2)
    (hbc : BoundaryCondition G P γ) : CommutesWithLogical P := by
  unfold CommutesWithLogical
  unfold BoundaryCondition at hbc
  rw [← hbc]
  exact boundary_sum_eq_zero G γ

/-! ## Commutation with Gauss's Law -/

/-- The deformed operator P̃ commutes with the Gauss's law operator A_v when the
    boundary condition ∂γ = S_Z(P)|_V holds. -/
theorem deformedOpExt_comm_gaussLaw (P : PauliOp V) (γ : G.edgeSet → ZMod 2)
    (hbc : BoundaryCondition G P γ) (v : V) :
    PauliCommute (deformedOpExt G P γ) (gaussLawOp G v) := by
  simp only [PauliCommute, symplecticInner]
  rw [Fintype.sum_sum_type]
  have h_vertex : ∑ w : V,
      ((deformedOpExt G P γ).xVec (Sum.inl w) * (gaussLawOp G v).zVec (Sum.inl w) +
       (deformedOpExt G P γ).zVec (Sum.inl w) * (gaussLawOp G v).xVec (Sum.inl w)) =
      P.zVec v := by
    simp only [deformedOpExt, gaussLawOp, Pi.zero_apply, mul_zero, zero_add]
    conv_lhs =>
      arg 2; ext w; rw [show P.zVec w * (if w = v then 1 else 0) =
        if w = v then P.zVec w else 0 from by split <;> simp_all]
    simp [Finset.sum_ite_eq']
  rw [h_vertex]
  have h_edge : ∑ e : G.edgeSet,
      ((deformedOpExt G P γ).xVec (Sum.inr e) * (gaussLawOp G v).zVec (Sum.inr e) +
       (deformedOpExt G P γ).zVec (Sum.inr e) * (gaussLawOp G v).xVec (Sum.inr e)) =
      ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then γ e else 0) := by
    congr 1; ext e
    simp only [deformedOpExt, gaussLawOp, Pi.zero_apply, mul_zero, zero_add]
    by_cases hve : v ∈ (e : Sym2 V) <;> simp [hve]
  rw [h_edge]
  unfold BoundaryCondition at hbc
  have hbc_v : boundaryMap G γ v = zSupportOnVertices P v := congr_fun hbc v
  simp only [boundaryMap, LinearMap.coe_mk, AddHom.coe_mk] at hbc_v
  rw [hbc_v]
  unfold zSupportOnVertices
  by_cases hzv : P.zVec v = 0
  · simp only [hzv, ne_eq, not_true, ↓reduceIte, add_zero]
  · simp only [ne_eq, hzv, not_false_eq_true, ↓reduceIte]
    have h1 : P.zVec v = 1 := (zmod2_ne_zero_iff' (P.zVec v)).mp hzv
    rw [h1]; exact CharTwo.add_self_eq_zero 1

/-! ## Compatibility with Multiplication -/

/-- Deforming a product of Pauli operators with the sum of edge-paths gives the
    product of deformed operators. -/
theorem deformedOpExt_mul (P Q : PauliOp V) (γ₁ γ₂ : G.edgeSet → ZMod 2) :
    deformedOpExt G P γ₁ * deformedOpExt G Q γ₂ =
    deformedOpExt G (P * Q) (γ₁ + γ₂) := by
  ext q
  · -- xVec
    cases q with
    | inl v => simp [deformedOpExt]
    | inr e => simp [deformedOpExt]
  · -- zVec
    cases q with
    | inl v => simp [deformedOpExt]
    | inr e => simp [deformedOpExt, Pi.add_apply]

/-! ## Boundary Condition Compatible with Multiplication -/

/-- zSupportOnVertices is additive for Pauli multiplication. -/
lemma zSupportOnVertices_mul (P Q : PauliOp V) (v : V) :
    zSupportOnVertices (P * Q) v =
    zSupportOnVertices P v + zSupportOnVertices Q v := by
  simp only [zSupportOnVertices, mul_zVec, Pi.add_apply]
  have hp := zmod2_ne_zero_iff' (P.zVec v)
  have hq := zmod2_ne_zero_iff' (Q.zVec v)
  by_cases hp0 : P.zVec v = 0 <;> by_cases hq0 : Q.zVec v = 0 <;> simp_all [CharTwo.add_self_eq_zero]

/-- The boundary condition is compatible with multiplication. -/
theorem boundaryCondition_mul (P Q : PauliOp V) (γ₁ γ₂ : G.edgeSet → ZMod 2)
    (h₁ : BoundaryCondition G P γ₁) (h₂ : BoundaryCondition G Q γ₂) :
    BoundaryCondition G (P * Q) (γ₁ + γ₂) := by
  unfold BoundaryCondition at *
  have h_add : boundaryMap G (γ₁ + γ₂) = boundaryMap G γ₁ + boundaryMap G γ₂ :=
    map_add (boundaryMap G) γ₁ γ₂
  ext v
  rw [show (boundaryMap G (γ₁ + γ₂)) v = (boundaryMap G γ₁ + boundaryMap G γ₂) v from
    congr_fun h_add v]
  simp only [Pi.add_apply]
  rw [congr_fun h₁ v, congr_fun h₂ v]
  exact (zSupportOnVertices_mul P Q v).symm

/-! ## No Z-Support on V -/

/-- A check P has no Z-support on V if its Z-support on vertices is the zero vector. -/
def HasNoZSupportOnV (P : PauliOp V) : Prop :=
  zSupportOnVertices P = 0

/-- For a check with no Z-support on V, the boundary condition is satisfied by γ = 0. -/
theorem noZSupport_boundary_zero (P : PauliOp V)
    (h : HasNoZSupportOnV P) : BoundaryCondition G P 0 := by
  unfold BoundaryCondition
  simp only [map_zero]
  exact h.symm

/-! ## Anchor Definition: Deformed Operator -/

/-- The deformed operator P̃ = P · ∏_{e ∈ γ} Z_e on the extended qubit system V ⊕ G.edgeSet.
    This is the main definition from Definition 3 of the paper. Given P on V and an edge-path
    γ with ∂γ = S_Z(P)|_V:
    - On vertex qubits: acts as P.
    - On edge qubits: acts as Z_e if γ(e) = 1, identity otherwise.
    Commutes with all Gauss's law operators A_v. -/
def deformedOperator (P : PauliOp V) (γ : G.edgeSet → ZMod 2)
    (_hbc : BoundaryCondition G P γ) : PauliOp (ExtQubit G) :=
  deformedOpExt G P γ

end DeformedOperator
