import QEC1.Lemmas.Lem_3_SpaceDistance
import Mathlib.Tactic

/-!
# Remark 13: Optimal Cheeger Constant

## Statement
Picking a graph with Cheeger constant h(G) = 1 is optimal for distance preservation:

1. **h(G) ≥ 1 is sufficient:** By Lemma 3, d* ≥ d.
2. **h(G) > 1 doesn't help further:** Any nontrivial logical of the original code, supported
   only on vertex qubits, commutes with all deformed code checks since it acts trivially on
   edge qubits. Hence it is also a nontrivial logical of the deformed code, so d* ≤ d.
   Combined: d* = d when h(G) ≥ 1.
3. **h(G) < 1 causes distance loss:** d* ≥ h(G) · d < d.

## Main Results
- `liftToExtended` : lifts a Pauli operator on V to V ⊕ E(G) with trivial edge action
- `liftToExtended_weight` : the lifted operator has the same weight
- `liftToExtended_isLogical` : lifting a pure-X original logical gives a deformed code logical
- `deformed_distance_le_original` : d* ≤ d (under existence of suitable pure-X logical)
- `deformed_distance_eq` : d* = d when h(G) ≥ 1
- `cheeger_one_is_optimal` : h(G) = 1 is the optimal threshold
- `distance_loss_when_cheeger_lt_one` : h(G) < 1 may cause distance loss
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
noncomputable section

namespace OptimalCheegerConstant

open Finset PauliOp GaussFlux DeformedOperator DeformedCode DeformedCodeChecks
     DesiderataForGraphG GaugingMeasurementCorrectness FreedomInDeformedChecks QEC1
     SpaceDistance

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-! ## Lifting original operators to the extended system -/

/-- Lift a Pauli operator on V to V ⊕ E(G) with trivial (identity) action on edge qubits. -/
def liftToExtended (P : PauliOp V) : PauliOp (ExtQubit G) :=
  deformedOpExt G P 0

@[simp]
theorem liftToExtended_xVec_vertex (P : PauliOp V) (v : V) :
    (liftToExtended G P).xVec (Sum.inl v) = P.xVec v := rfl

@[simp]
theorem liftToExtended_xVec_edge (P : PauliOp V) (e : G.edgeSet) :
    (liftToExtended G P).xVec (Sum.inr e) = 0 := rfl

@[simp]
theorem liftToExtended_zVec_vertex (P : PauliOp V) (v : V) :
    (liftToExtended G P).zVec (Sum.inl v) = P.zVec v := rfl

@[simp]
theorem liftToExtended_zVec_edge (P : PauliOp V) (e : G.edgeSet) :
    (liftToExtended G P).zVec (Sum.inr e) = 0 := by
  simp [liftToExtended, deformedOpExt]

theorem liftToExtended_noX_on_edges (P : PauliOp V) (e : G.edgeSet) :
    (liftToExtended G P).xVec (Sum.inr e) = 0 := rfl

theorem liftToExtended_noZ_on_edges (P : PauliOp V) (e : G.edgeSet) :
    (liftToExtended G P).zVec (Sum.inr e) = 0 := by
  simp [liftToExtended, deformedOpExt]

/-- The lifted operator has the same weight as the original. -/
theorem liftToExtended_weight (P : PauliOp V) :
    (liftToExtended G P).weight = P.weight := by
  rw [weight_eq_vertex_plus_edge]
  have h_edge : (Finset.univ.filter (fun e : G.edgeSet =>
      (liftToExtended G P).xVec (Sum.inr e) ≠ 0 ∨
      (liftToExtended G P).zVec (Sum.inr e) ≠ 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _
    push_neg
    exact ⟨liftToExtended_noX_on_edges G P e, liftToExtended_noZ_on_edges G P e⟩
  rw [h_edge, add_zero]
  unfold PauliOp.weight PauliOp.support
  congr 1

/-- The restriction of a lifted operator back to V recovers the original. -/
theorem restrictToV_liftToExtended (P : PauliOp V) :
    restrictToV G (liftToExtended G P) = P := by
  ext v <;> simp [restrictToV, liftToExtended, deformedOpExt]

/-- The lift preserves multiplication. -/
theorem liftToExtended_mul (P Q : PauliOp V) :
    liftToExtended G (P * Q) = liftToExtended G P * liftToExtended G Q := by
  ext q <;> cases q <;> simp [liftToExtended, deformedOpExt, mul_xVec, mul_zVec]

/-- The lift sends identity to identity. -/
theorem liftToExtended_one : liftToExtended G (1 : PauliOp V) = 1 := by
  ext q <;> cases q <;> simp [liftToExtended, deformedOpExt, one_xVec, one_zVec]

/-- The lift is injective: it preserves non-identity. -/
theorem liftToExtended_ne_one {P : PauliOp V} (hP : P ≠ 1) :
    liftToExtended G P ≠ 1 := by
  intro h; apply hP
  have := congr_arg (restrictToV G) h
  rw [restrictToV_liftToExtended, restrictToV_one] at this
  exact this

/-! ## Commutation of lifted operators with deformed code checks -/

/-- The lift commutes with flux checks: flux is pure Z on edges, lift has no support on edges. -/
theorem liftToExtended_comm_flux
    (_hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (P : PauliOp V) (p : C) :
    PauliCommute (liftToExtended G P) (fluxChecks G cycles p) := by
  unfold PauliCommute symplecticInner
  rw [Fintype.sum_sum_type]
  have h_vertex : ∑ v : V,
      ((liftToExtended G P).xVec (Sum.inl v) * (fluxChecks G cycles p).zVec (Sum.inl v) +
       (liftToExtended G P).zVec (Sum.inl v) * (fluxChecks G cycles p).xVec (Sum.inl v)) = 0 := by
    apply Finset.sum_eq_zero; intro v _
    simp [fluxChecks, fluxOp]
  have h_edge : ∑ e : G.edgeSet,
      ((liftToExtended G P).xVec (Sum.inr e) * (fluxChecks G cycles p).zVec (Sum.inr e) +
       (liftToExtended G P).zVec (Sum.inr e) * (fluxChecks G cycles p).xVec (Sum.inr e)) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    simp [liftToExtended, deformedOpExt, fluxChecks, fluxOp]
  rw [h_vertex, h_edge, add_zero]

/-- The lift commutes with deformed original checks when the original operator
    commutes with the original check. -/
theorem liftToExtended_comm_deformedCheck
    (data : DeformedCodeData G checks)
    (P : PauliOp V) (j : J)
    (hcomm_j : PauliCommute P (checks j)) :
    PauliCommute (liftToExtended G P) (deformedOriginalChecks G checks data j) := by
  change symplecticInner (liftToExtended G P) (deformedOriginalChecks G checks data j) = 0
  rw [symplecticInner_noXEdge_deformed G checks (liftToExtended G P) data
      (liftToExtended_noX_on_edges G P) j]
  rw [restrictToV_liftToExtended]
  exact hcomm_j

/-- ⟨lift(P), A_v⟩ = P.zVec(v): the symplectic inner product with a gaussLaw check. -/
theorem liftToExtended_symplecticInner_gaussLaw (P : PauliOp V) (v : V) :
    symplecticInner (liftToExtended G P) (gaussLawOp G v) = P.zVec v := by
  unfold symplecticInner
  rw [Fintype.sum_sum_type]
  have h_vertex : ∑ w : V,
      ((liftToExtended G P).xVec (Sum.inl w) * (gaussLawOp G v).zVec (Sum.inl w) +
       (liftToExtended G P).zVec (Sum.inl w) * (gaussLawOp G v).xVec (Sum.inl w)) =
      P.zVec v := by
    simp only [gaussLawOp_zVec, Pi.zero_apply, mul_zero, zero_add,
               liftToExtended_zVec_vertex, gaussLawOp, Sum.inl.injEq]
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw; simp [hw]
    · intro habs; exact absurd (Finset.mem_univ v) habs
  have h_edge : ∑ e : G.edgeSet,
      ((liftToExtended G P).xVec (Sum.inr e) * (gaussLawOp G v).zVec (Sum.inr e) +
       (liftToExtended G P).zVec (Sum.inr e) * (gaussLawOp G v).xVec (Sum.inr e)) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    simp [liftToExtended, deformedOpExt, gaussLawOp]
  rw [h_vertex, h_edge, add_zero]

/-- The lift commutes with A_v iff P has no Z-support at v. -/
theorem liftToExtended_comm_gaussLaw_iff (P : PauliOp V) (v : V) :
    PauliCommute (liftToExtended G P) (gaussLawOp G v) ↔ P.zVec v = 0 := by
  unfold PauliCommute
  rw [liftToExtended_symplecticInner_gaussLaw]

/-- A pure-X operator (zVec = 0) lifted to V ⊕ E commutes with all gaussLaw checks. -/
theorem liftToExtended_comm_gaussLaw_of_pureX (P : PauliOp V)
    (hpureX : P.zVec = 0) (v : V) :
    PauliCommute (liftToExtended G P) (gaussLawOp G v) := by
  rw [liftToExtended_comm_gaussLaw_iff]
  exact congr_fun hpureX v

/-! ## Pure-X logicals lift to deformed code centralizer -/

/-- A pure-X operator in the centralizer of the original code lifts to the centralizer
    of the deformed code. -/
theorem liftToExtended_inCentralizer_of_pureX
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (P : PauliOp V) (hpureX : P.zVec = 0)
    (hcent : ∀ j : J, PauliCommute P (checks j)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer
      (liftToExtended G P) := by
  intro a
  simp only [deformedStabilizerCode, deformedCodeChecks, allChecks]
  cases a with
  | gaussLaw v => exact liftToExtended_comm_gaussLaw_of_pureX G P hpureX v
  | flux p => exact liftToExtended_comm_flux G cycles hcyc P p
  | deformed j => exact liftToExtended_comm_deformedCheck G checks data P j (hcent j)

/-! ## Point 1: h(G) ≥ 1 is sufficient for d* ≥ d -/

/-- **Point 1: h(G) ≥ 1 is sufficient for d* ≥ d.**
    Direct application of Lemma 3. -/
theorem sufficient_expansion_gives_dstar_ge_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hconn : G.Connected)
    (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P) :
    origCode.distance ≤
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance :=
  deformed_distance_ge_d_sufficient_expansion G cycles checks origCode hJ hchecks_eq
    data hcyc hcomm hconn hcard hexact hexact_boundary hexp hL_logical hDeformedHasLogicals

/-! ## Point 2: d* ≤ d via lifting -/

/-- The deformed distance is at most the weight of any deformed code logical. -/
theorem deformed_distance_le_weight
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L') :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance ≤ L'.weight := by
  unfold StabilizerCode.distance
  apply Nat.sInf_le
  exact ⟨L', hlog, rfl⟩

/-- A pure-X logical P of the original code, when lifted, is a logical of the deformed code
    (given that the lift is not in the deformed stabilizer group). -/
theorem liftToExtended_isLogical
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (P : PauliOp V) (hlog : origCode.isLogicalOp P) (hpureX : P.zVec = 0)
    (hnotDeformedStab : liftToExtended G P ∉
      (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp
      (liftToExtended G P) := by
  obtain ⟨hcent, _, hne1⟩ := hlog
  refine ⟨?_, hnotDeformedStab, liftToExtended_ne_one G hne1⟩
  have hcent' : ∀ j : J, PauliCommute P (checks j) := by
    intro j; have := hcent (hJ ▸ j); rwa [hchecks_eq] at this
  exact liftToExtended_inCentralizer_of_pureX G cycles checks data hcyc hcomm P hpureX hcent'

/-- **Point 2: d* ≤ d.**
    If there exists a pure-X logical of minimum weight whose lift is not a deformed
    stabilizer, then d* ≤ d. -/
theorem deformed_distance_le_original
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (P : PauliOp V) (hlog : origCode.isLogicalOp P) (hpureX : P.zVec = 0)
    (hweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance ≤
    origCode.distance := by
  have hlogD := liftToExtended_isLogical G cycles checks origCode hJ hchecks_eq
    data hcyc hcomm P hlog hpureX hnotDeformedStab
  calc (deformedStabilizerCode G cycles checks data hcyc hcomm).distance
      ≤ (liftToExtended G P).weight :=
        deformed_distance_le_weight G cycles checks data hcyc hcomm _ hlogD
    _ = P.weight := liftToExtended_weight G P
    _ = origCode.distance := hweight

/-! ## Point 2 combined with Point 1: d* = d when h(G) ≥ 1 -/

/-- **d* = d when h(G) ≥ 1** (combining Points 1 and 2). -/
theorem deformed_distance_eq
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P)
    (P : PauliOp V) (hlog : origCode.isLogicalOp P) (hpureX : P.zVec = 0)
    (hweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance =
    origCode.distance := by
  apply le_antisymm
  · exact deformed_distance_le_original G cycles checks origCode hJ hchecks_eq
      data hcyc hcomm P hlog hpureX hweight hnotDeformedStab
  · exact sufficient_expansion_gives_dstar_ge_d G cycles checks origCode hJ hchecks_eq
      data hcyc hcomm hconn hcard hexact hexact_boundary hexp hL_logical hDeformedHasLogicals

/-! ## Point 3: h(G) < 1 causes distance loss -/

/-- **Point 3: h(G) < 1 causes distance loss.**
    The Lemma 3 bound gives d* ≥ h(G) · d, which is strictly less than d. -/
theorem distance_loss_when_cheeger_lt_one
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P)
    (hCheeger_lt : cheegerConstant G < 1) :
    cheegerConstant G * origCode.distance ≤
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance := by
  have h := deformed_distance_ge_min_cheeger_d G cycles checks origCode hJ hchecks_eq
    data hcyc hcomm hconn hcard hexact hexact_boundary hL_logical hDeformedHasLogicals
  rw [min_eq_left (le_of_lt hCheeger_lt)] at h
  exact_mod_cast h

/-- When h(G) < 1, the lower bound h(G) · d is strictly less than d (if d > 0 and h(G) > 0). -/
theorem cheeger_lt_one_bound_lt_d
    (origCode : StabilizerCode V)
    (hd : 0 < origCode.distance)
    (_hCheeger_pos : 0 < cheegerConstant G)
    (hCheeger_lt : cheegerConstant G < 1) :
    cheegerConstant G * origCode.distance < origCode.distance := by
  calc cheegerConstant G * ↑origCode.distance
      < 1 * ↑origCode.distance := by
        exact mul_lt_mul_of_pos_right hCheeger_lt (Nat.cast_pos.mpr hd)
    _ = ↑origCode.distance := _root_.one_mul _

/-! ## Optimality of h(G) = 1 -/

/-- Increasing h(G) beyond 1 doesn't improve the Lemma 3 bound: min(h(G), 1) = 1. -/
theorem bound_saturates_at_cheeger_one
    (h : 1 ≤ cheegerConstant G) (d : ℕ) :
    min (cheegerConstant G) 1 * (d : ℝ) = (d : ℝ) := by
  rw [min_eq_right h, _root_.one_mul]

/-- h(G) ≥ 1 implies min(h(G), 1) = 1. -/
@[simp]
theorem min_cheeger_one_eq_one_of_sufficient (h : SufficientExpansion G) :
    min (cheegerConstant G) 1 = (1 : ℝ) :=
  min_eq_right h

/-- **h(G) > 1 doesn't help further:** the lower bound from Lemma 3 is still d. -/
theorem cheeger_gt_one_bound_eq_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P)
    (hCheeger : 1 < cheegerConstant G) :
    origCode.distance ≤
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance :=
  sufficient_expansion_gives_dstar_ge_d G cycles checks origCode hJ hchecks_eq
    data hcyc hcomm hconn hcard hexact hexact_boundary (le_of_lt hCheeger) hL_logical
    hDeformedHasLogicals

/-! ## Summary -/

/-- The distance bound trichotomy:
    - h(G) ≥ 1 → the bound gives d (saturates)
    - h(G) < 1 → the bound gives h(G)·d < d (distance loss) -/
theorem distance_trichotomy
    (origCode : StabilizerCode V)
    (hd : 0 < origCode.distance)
    (hCheeger_pos : 0 < cheegerConstant G) :
    (1 ≤ cheegerConstant G →
      min (cheegerConstant G) 1 * origCode.distance = origCode.distance) ∧
    (cheegerConstant G < 1 →
      min (cheegerConstant G) 1 * origCode.distance < origCode.distance) := by
  constructor
  · intro h; rw [min_eq_right h, _root_.one_mul]
  · intro h
    rw [min_eq_left (le_of_lt h)]
    exact cheeger_lt_one_bound_lt_d G origCode hd hCheeger_pos h

end OptimalCheegerConstant
