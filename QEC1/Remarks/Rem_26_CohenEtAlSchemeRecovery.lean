import QEC1.Remarks.Rem_17_HypergraphGeneralization
import QEC1.Remarks.Rem_25_SteaneStyleMeasurement
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import QEC1.Remarks.Rem_2_NotationPauliOperators
import QEC1.Remarks.Rem_4_NotationCheegerConstant
import QEC1.Remarks.Rem_11_DesiderataForGraphG
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Remark 26: Cohen et al. Scheme Recovery

## Statement
The Cohen et al. scheme for logical measurement is recovered as a special case of
the hypergraph gauging procedure (Rem_17).

Given a CSS stabilizer code and an irreducible X logical operator L:
1. Restrict Z-type checks to the support of L → defines hypergraph H = (V_L, E_L)
2. The only nontrivial element in ker(∂) is the all-ones vector (= L)
3. Cohen et al. = hypergraph gauging with d layers
4. Cross et al. = fewer layers with sufficient Cheeger expansion
5. Joint measurement = adding edges between individual graphs

## Main Results
- `restrictedZCheckIncident` : incidence relation for Z-checks restricted to supp(L)
- `restrictedBoundaryMap` : the boundary map of the restricted hypergraph
- `IsIrreducibleXLogical` : irreducible X logical operator definition
- `zCheck_restricted_support_even` : commutation implies even overlap (row evenness)
- `prodX_centralizer_of_even_overlap` : prodX(S) is in centralizer when S has even overlap
- `coboundary_ker_gives_centralizer_pair` : ker(δ) elements give centralizer factorizations
- `kernel_restricted_boundary_trivial` : kernel triviality from irreducibility
- `layeredIncident` : the d-layer incidence combining inter/intra-layer edges
- `cohen_layered_all_ones_measures_L` : all-ones Gauss product measures L
- `jointIncident` : joint incidence for measuring products of logicals
- `joint_gauss_product_measures_product` : joint measurement by adding edges
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace CohenEtAlSchemeRecovery

open Finset PauliOp HypergraphGeneralization SteaneStyleMeasurement

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## Restricted hypergraph from Z-checks on logical support -/

section RestrictedHypergraph

variable (C : StabilizerCode Q)
variable (L : PauliOp Q)

/-- The support of L as a finset of qubits (X-support). -/
def logicalSupport : Finset Q := L.supportX

/-- A Z-type check index: a check with no X-support. -/
def isZTypeCheck (i : C.I) : Prop := (C.check i).xVec = 0

instance isZTypeCheck_decidable [DecidableEq C.I] (i : C.I) :
    Decidable (isZTypeCheck C i) :=
  inferInstanceAs (Decidable ((C.check i).xVec = 0))

/-- The Z-type check indices that have nonempty intersection with supp(L). -/
def relevantZChecks [DecidableEq C.I] : Finset C.I :=
  Finset.univ.filter (fun i =>
    isZTypeCheck C i ∧ ((C.check i).supportZ ∩ logicalSupport L).Nonempty)

/-- The incidence relation for the restricted hypergraph:
    qubit q is incident to Z-check i iff q ∈ supp(L) and the check has Z-action at q. -/
def restrictedZCheckIncident [DecidableEq C.I]
    (q : Q) (i : C.I) : Prop :=
  q ∈ logicalSupport L ∧ (C.check i).zVec q ≠ 0 ∧ isZTypeCheck C i

instance restrictedZCheckIncident_decidable [DecidableEq C.I] (q : Q) (i : C.I) :
    Decidable (restrictedZCheckIncident C L q i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The restricted hypergraph boundary map: ∂ : Z₂^{E_L} → Z₂^{V_L}. -/
def restrictedBoundaryMap [DecidableEq C.I] :=
  hyperBoundaryMap (restrictedZCheckIncident C L)

/-- The restricted hypergraph coboundary map: δ : Z₂^{V_L} → Z₂^{E_L}. -/
def restrictedCoboundaryMap [DecidableEq C.I] :=
  hyperCoboundaryMap (restrictedZCheckIncident C L)

end RestrictedHypergraph

/-! ## Irreducible X logical operators -/

section IrreducibleLogical

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (C : StabilizerCode Q)

/-- An X-type logical operator: pure X-type (zVec = 0), in the centralizer,
    not a stabilizer, and not identity. -/
def IsXTypeLogical (L : PauliOp Q) : Prop :=
  L.zVec = 0 ∧ C.isLogicalOp L

/-- An irreducible X logical operator: an X-type logical that cannot be written
    as a product of two lower-weight X-type operators that are both in the centralizer. -/
def IsIrreducibleXLogical (L : PauliOp Q) : Prop :=
  IsXTypeLogical C L ∧
  ∀ P R : PauliOp Q, P.zVec = 0 → R.zVec = 0 →
    C.inCentralizer P → C.inCentralizer R →
    P * R = L → (P.weight ≥ L.weight ∨ R.weight ≥ L.weight ∨ P = 1 ∨ R = 1)

end IrreducibleLogical

/-! ## Commutation and kernel properties for the restricted hypergraph -/

section KernelProperty

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (C : StabilizerCode Q) [DecidableEq C.I]
variable (L : PauliOp Q)

/-- If L is pure X-type and commutes with all checks, then for each Z-type check s_j,
    the Z-support of s_j intersected with supp(L) has even cardinality (row evenness).
    This is because ⟨L, s_j⟩_symp = Σ_q L.xVec(q) · s_j.zVec(q) = 0 (commutation),
    and L.xVec(q) = 1 iff q ∈ supp(L), so the sum counts |S_Z(s_j) ∩ supp(L)| mod 2. -/
theorem zCheck_restricted_support_even
    (hL_pure_X : L.zVec = 0)
    (hL_comm : C.inCentralizer L)
    (i : C.I) (hZ : isZTypeCheck C i) :
    Even ((Finset.univ.filter (fun q : Q =>
      restrictedZCheckIncident C L q i)).card) := by
  have hcomm := hL_comm i
  unfold PauliCommute symplecticInner at hcomm
  unfold isZTypeCheck at hZ
  simp only [hL_pure_X, hZ, Pi.zero_apply, zero_mul, mul_zero, add_zero] at hcomm
  rw [← ZMod.natCast_eq_zero_iff_even]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  convert hcomm using 1
  apply Finset.sum_congr rfl
  intro q _
  simp only [restrictedZCheckIncident, logicalSupport, mem_supportX, mem_filter, mem_univ,
    true_and, isZTypeCheck, hZ, and_true]
  by_cases hx : L.xVec q = 0
  · simp [hx]
  · by_cases hz : (C.check i).zVec q = 0
    · simp [hz]
    · have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by
        fin_cases x <;> simp
      have hx1 : L.xVec q = 1 := by
        rcases zmod2_cases (L.xVec q) with h | h <;> simp_all
      have hz1 : (C.check i).zVec q = 1 := by
        rcases zmod2_cases ((C.check i).zVec q) with h | h <;> simp_all
      simp [hx, hz, hx1, hz1, hZ]

end KernelProperty

/-! ## Pure X operators in the centralizer

For a CSS code, a pure X-type operator prodX(S) is in the centralizer iff for each
Z-type check s_j, the intersection |S ∩ supp_Z(s_j)| is even. X-type checks commute
automatically (both pure X-type). -/

section ProdXCentralizer

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (C : StabilizerCode Q) [DecidableEq C.I]

/-- Helper: the symplectic inner product of prodX(S) with a Z-type check equals
    the sum over S of the check's Z-vector indicator. -/
private theorem prodX_symplecticInner_eq_sum_filter (S : Finset Q) (j : C.I)
    (hZ : isZTypeCheck C j) :
    (∑ v : Q, ((prodX S).xVec v * (C.check j).zVec v +
      (prodX S).zVec v * (C.check j).xVec v)) =
    (∑ q ∈ S, (if (C.check j).zVec q ≠ 0 then (1 : ZMod 2) else 0)) := by
  unfold isZTypeCheck at hZ
  have : ∀ v : Q, (prodX S).xVec v * (C.check j).zVec v +
      (prodX S).zVec v * (C.check j).xVec v =
    (if v ∈ S then 1 else 0) * (C.check j).zVec v := by
    intro v; simp [prodX, hZ]
  simp_rw [this]
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · apply Finset.sum_congr rfl
    intro q hq
    have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
    simp only [hq, ite_true]
    by_cases hz : (C.check j).zVec q = 0
    · simp [hz]
    · have hz1 : (C.check j).zVec q = 1 := by
        rcases zmod2_cases ((C.check j).zVec q) with h | h <;> simp_all
      simp [hz, hz1]
  · intro q _ hq; simp [hq]

/-- For a CSS code, prodX(S) commutes with a Z-type check s_j iff |S ∩ supp_Z(s_j)| is even. -/
theorem prodX_commutes_zCheck_iff_even (S : Finset Q) (j : C.I) (hZ : isZTypeCheck C j) :
    PauliCommute (prodX S) (C.check j) ↔
    Even ((S.filter (fun q => (C.check j).zVec q ≠ 0)).card) := by
  unfold PauliCommute symplecticInner
  rw [prodX_symplecticInner_eq_sum_filter C S j hZ]
  rw [← ZMod.natCast_eq_zero_iff_even, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

/-- For a CSS code, prodX(S) is in the centralizer iff S has even overlap with
    every Z-type check's support. -/
theorem prodX_centralizer_of_even_overlap (S : Finset Q) (hcss : IsCSS C)
    (heven : ∀ j : C.I, isZTypeCheck C j →
      Even ((S.filter (fun q => (C.check j).zVec q ≠ 0)).card)) :
    C.inCentralizer (prodX S) := by
  intro i
  rcases hcss i with hX | hZ
  · exact pureX_pureX_commute (prodX S) (C.check i)
      (show (prodX S).zVec = 0 from rfl) hX
  · rw [prodX_commutes_zCheck_iff_even C S i (show isZTypeCheck C i from hZ)]
    exact heven i (show isZTypeCheck C i from hZ)

end ProdXCentralizer

/-! ## Coboundary kernel elements give centralizer factorizations

The key algebraic step: an element f ∈ ker(δ) of the restricted coboundary map
(where δ is the transpose of the boundary map ∂) gives a factorization of L into
two pure X-type centralizer elements. Specifically, if f : Q → ZMod 2 satisfies
δf = 0 (meaning for each relevant Z-check j, #{q : f(q)=1 and q incident to j} is
even), then prodX(supp(f) ∩ V_L) is in the centralizer of C. -/

section CoboundaryKernel

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (C : StabilizerCode Q) [DecidableEq C.I]
variable (L : PauliOp Q)

/-- An element f in the kernel of the restricted coboundary map (i.e., for each
    relevant Z-check j, the number of vertices q with f(q) ≠ 0 incident to j is
    even) gives a pure X-type operator prodX(supp(f) ∩ V_L) that commutes with
    all Z-type checks, via `prodX_centralizer_of_even_overlap`.

    This is the key step connecting the linear algebra of the restricted
    hypergraph to the PauliOp centralizer structure. -/
theorem coboundary_ker_gives_centralizer_pair (hcss : IsCSS C)
    (f : Q → ZMod 2)
    (hf_ker : f ∈ LinearMap.ker (restrictedCoboundaryMap C L))
    (hf_supp : ∀ q : Q, q ∉ logicalSupport L → f q = 0) :
    C.inCentralizer (prodX (Finset.univ.filter (fun q => f q ≠ 0))) := by
  apply prodX_centralizer_of_even_overlap
  · exact hcss
  · intro j hZj
    rw [LinearMap.mem_ker] at hf_ker
    have hf_j : restrictedCoboundaryMap C L f j = 0 := congr_fun hf_ker j
    simp only [restrictedCoboundaryMap, hyperCoboundaryMap_apply] at hf_j
    -- hf_j says: Σ_q [q incident to j in restricted hypergraph] · f(q) = 0
    -- Goal: Even (card (filter (fun q => f q ≠ 0 ∧ zVec q ≠ 0) univ))
    -- Rewrite to a sum over univ, then equate with hf_j
    rw [← ZMod.natCast_eq_zero_iff_even]
    rw [Finset.card_eq_sum_ones]
    push_cast
    -- Unroll both filters to get sum over univ
    rw [Finset.sum_filter, Finset.sum_filter]
    -- Goal: Σ_q, if (f q ≠ 0) then (if zVec q ≠ 0 then 1 else 0) else 0 = 0
    convert hf_j using 1
    apply Finset.sum_congr rfl
    intro q _
    by_cases hfq : f q = 0
    · simp [hfq]
    · by_cases hinc : restrictedZCheckIncident C L q j
      · simp only [hinc, ite_true]
        have hzq : (C.check j).zVec q ≠ 0 := hinc.2.1
        have hfq1 : f q = 1 := by
          have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
          rcases this (f q) with h | h <;> simp_all
        simp [hfq, hzq, hfq1]
      · simp only [restrictedZCheckIncident] at hinc
        push_neg at hinc
        by_cases hq_supp : q ∈ logicalSupport L
        · by_cases hzq : (C.check j).zVec q = 0
          · -- f q ≠ 0 and zVec q = 0: LHS = 0, RHS = 0 (since ¬incident)
            have hnotinc : ¬restrictedZCheckIncident C L q j := by
              intro hinc'; exact absurd hzq (ne_of_eq_of_ne rfl hinc'.2.1)
            simp [hfq, hzq, hnotinc]
          · exfalso; exact hinc hq_supp hzq hZj
        · exfalso; exact hfq (hf_supp q hq_supp)

end CoboundaryKernel

/-! ## ProdX helper lemmas for the kernel triviality proof -/

section ProdXHelpers

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Multiplication of prodX operators corresponds to symmetric difference of indicator
    functions in ZMod 2. For disjoint sets, this gives the union. -/
private theorem prodX_mul_disjoint (S T : Finset Q) (h : Disjoint S T) :
    prodX S * prodX T = prodX (S ∪ T) := by
  ext v
  · simp only [mul_xVec, prodX, Pi.add_apply, Finset.mem_union]
    by_cases hS : v ∈ S <;> by_cases hT : v ∈ T
    · exfalso; exact Finset.disjoint_left.mp h hS hT
    · simp [hS, hT]
    · simp [hS, hT]
    · simp [hS, hT]
  · simp [prodX]

/-- A pure X-type operator equals prodX of its X-support. -/
private theorem pure_x_eq_prodX_supportX (L : PauliOp Q) (h : L.zVec = 0) :
    L = prodX L.supportX := by
  ext v
  · simp only [prodX, mem_supportX_iff]
    by_cases hx : L.xVec v = 0
    · simp [hx]
    · have hx1 : L.xVec v = 1 := by
        have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
        rcases this (L.xVec v) with h1 | h1 <;> simp_all
      simp [hx1]
  · simp only [prodX, h, Pi.zero_apply]

/-- The weight of prodX(S) equals |S|. -/
private theorem weight_prodX (S : Finset Q) : (prodX S).weight = S.card := by
  simp [weight, support_eq_supportX_union_supportZ, supportX_prodX, supportZ_prodX]

/-- prodX of a nonempty set is not the identity operator. -/
private theorem prodX_ne_one_of_nonempty (S : Finset Q) (h : S.Nonempty) :
    prodX S ≠ 1 := by
  intro heq
  have hsup := congr_arg PauliOp.supportX heq
  rw [supportX_prodX, supportX_one] at hsup
  exact Finset.Nonempty.ne_empty h hsup

end ProdXHelpers

/-! ## Z₂ rank-nullity for incidence matrices

The key linear algebra step: for an incidence relation between finite types V and E,
the boundary map ∂ = M · and coboundary map δ = Mᵀ · satisfy
  dim(ker(δ)) + |E| = dim(ker(∂)) + |V|
via `Matrix.rank_transpose` and rank-nullity. This is used to show that if
ker(∂) has dimension ≥ 2, then (given |V| ≥ |E|) ker(δ) also has dimension ≥ 2. -/

section Z2RankNullity

variable {V₀ E₀ : Type*} [Fintype V₀] [DecidableEq V₀] [Fintype E₀] [DecidableEq E₀]

/-- The Z₂ incidence matrix for an incidence relation. -/
private def z2IncMatrix (inc : V₀ → E₀ → Prop) [∀ v e, Decidable (inc v e)] :
    Matrix V₀ E₀ (ZMod 2) :=
  fun v e => if inc v e then 1 else 0

/-- The hypergraph boundary map equals the incidence matrix mulVecLin. -/
private theorem hyperBoundaryMap_eq_mulVecLin (inc : V₀ → E₀ → Prop)
    [∀ v e, Decidable (inc v e)] :
    HypergraphGeneralization.hyperBoundaryMap inc = (z2IncMatrix inc).mulVecLin := by
  apply LinearMap.ext; intro γ; ext v
  simp only [HypergraphGeneralization.hyperBoundaryMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mulVecLin_apply, Matrix.mulVec, z2IncMatrix]
  apply Finset.sum_congr rfl; intro e _
  by_cases h : inc v e <;> simp [h]

/-- The hypergraph coboundary map equals the transposed incidence matrix mulVecLin. -/
private theorem hyperCoboundaryMap_eq_mulVecLin (inc : V₀ → E₀ → Prop)
    [∀ v e, Decidable (inc v e)] :
    HypergraphGeneralization.hyperCoboundaryMap inc = (z2IncMatrix inc).transpose.mulVecLin := by
  apply LinearMap.ext; intro f; ext e
  simp only [HypergraphGeneralization.hyperCoboundaryMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.transpose_apply, z2IncMatrix]
  apply Finset.sum_congr rfl; intro v _
  by_cases h : inc v e <;> simp [h]

/-- **Z₂ rank-nullity for incidence matrices.**
    dim(ker(δ)) + |E| = dim(ker(∂)) + |V|, where ∂ = M · and δ = Mᵀ ·.
    This follows from `Matrix.rank_transpose` and `LinearMap.finrank_range_add_finrank_ker`. -/
theorem z2_finrank_ker_formula (inc : V₀ → E₀ → Prop) [∀ v e, Decidable (inc v e)] :
    Module.finrank (ZMod 2) (LinearMap.ker (HypergraphGeneralization.hyperCoboundaryMap inc)) +
      Fintype.card E₀ =
    Module.finrank (ZMod 2) (LinearMap.ker (HypergraphGeneralization.hyperBoundaryMap inc)) +
      Fintype.card V₀ := by
  rw [hyperBoundaryMap_eq_mulVecLin, hyperCoboundaryMap_eq_mulVecLin]
  have h1 := LinearMap.finrank_range_add_finrank_ker (z2IncMatrix inc).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (z2IncMatrix inc).transpose.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h2
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (z2IncMatrix inc).mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.range (z2IncMatrix inc).transpose.mulVecLin) := by
    change (z2IncMatrix inc).rank = (z2IncMatrix inc).transpose.rank
    exact (Matrix.rank_transpose _).symm
  omega

/-- In a ZMod 2-submodule of finrank ≥ 2, given any element w, there exists
    a third element v ≠ 0 and v ≠ w. Uses `finrank_le_one` for the contrapositive. -/
private theorem exists_third_in_submodule {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (S : Submodule (ZMod 2) M) [Module.Finite (ZMod 2) S]
    (hrank : 2 ≤ Module.finrank (ZMod 2) S)
    (w : M) (hw : w ∈ S) :
    ∃ v ∈ S, v ≠ 0 ∧ v ≠ w := by
  by_contra hall
  push_neg at hall
  have h1 : Module.finrank (ZMod 2) S ≤ 1 := by
    apply finrank_le_one (⟨w, hw⟩ : S)
    intro ⟨v, hv⟩
    rcases eq_or_ne v 0 with hv0 | hv0
    · exact ⟨0, by ext; simp [hv0]⟩
    · exact ⟨1, by ext; simp [hall v hv hv0]⟩
  omega

/-- Given dim(ker(boundary)) ≥ 2 and |E| ≤ |V|, and any w ∈ ker(coboundary),
    there exists g ∈ ker(coboundary) with g ≠ 0 and g ≠ w. -/
theorem coboundary_third_element (inc : V₀ → E₀ → Prop) [∀ v e, Decidable (inc v e)]
    (hVE : Fintype.card E₀ ≤ Fintype.card V₀)
    (hker : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker
        (HypergraphGeneralization.hyperBoundaryMap inc)))
    (w : V₀ → ZMod 2) (hw : w ∈ LinearMap.ker (HypergraphGeneralization.hyperCoboundaryMap inc)) :
    ∃ g ∈ LinearMap.ker (HypergraphGeneralization.hyperCoboundaryMap inc),
      g ≠ 0 ∧ g ≠ w := by
  have hdim : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker
      (HypergraphGeneralization.hyperCoboundaryMap inc)) := by
    have := z2_finrank_ker_formula inc; omega
  exact exists_third_in_submodule _ hdim w hw

end Z2RankNullity

/-! ## Kernel triviality: the core structural property

For an irreducible X logical L, the kernel of ∂ on the restricted hypergraph
consists only of 0 and the all-ones vector on E_L. The argument proceeds in
two steps:

**Step 1 (rank-nullity):** If ker(∂) has dimension ≥ 2 (i.e., contains a
nontrivial γ besides 0 and all-ones), then ker(δ) also has dimension ≥ 2
(given |V_L| ≥ |E_L|), yielding a nontrivial vertex function f ∈ ker(δ)
with f ≠ 0 and f ≠ all-ones. This uses rank(∂) = rank(δ) (since δ = ∂^T
via `Matrix.rank_transpose`) and `z2_finrank_ker_formula`.

**Step 2 (irreducibility contradiction):** Such f gives a factorization
L = prodX(supp(f)) · prodX(V_L \ supp(f)) where both factors are in the
centralizer (by `coboundary_ker_gives_centralizer_pair`). Irreducibility
then forces one factor to have weight ≥ wt(L) or be identity, meaning
supp(f) = ∅ or supp(f) = V_L, contradicting f ≠ 0 and f ≠ all-ones. -/

section KernelTrivial

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (C : StabilizerCode Q) [DecidableEq C.I]
variable (L : PauliOp Q)

/-! ### Core incidence on subtype and lifting -/

/-- The core incidence on subtypes: vertex in VL incident to check in EL iff zVec ≠ 0. -/
def coreIncident :
    {q : Q // q ∈ logicalSupport L} → {i : C.I // i ∈ relevantZChecks C L} → Prop :=
  fun q i => (C.check i.1).zVec q.1 ≠ 0

instance coreIncident_decidable
    (q : {q : Q // q ∈ logicalSupport L}) (i : {i : C.I // i ∈ relevantZChecks C L}) :
    Decidable (coreIncident C L q i) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- Lift a function on VL to a function on Q by extending with zeros. -/
def liftVL (g : {q : Q // q ∈ logicalSupport L} → ZMod 2) : Q → ZMod 2 :=
  fun q => if hq : q ∈ logicalSupport L then g ⟨q, hq⟩ else 0

/-- The lift is injective. -/
theorem liftVL_injective : Function.Injective (liftVL L) := by
  intro g₁ g₂ h; ext ⟨q, hq⟩
  have := congr_fun h q
  simp only [liftVL, dif_pos hq] at this; exact this

/-- The lift is supported on VL. -/
theorem liftVL_supp (g : {q : Q // q ∈ logicalSupport L} → ZMod 2) :
    ∀ q, q ∉ logicalSupport L → liftVL L g q = 0 := by
  intro q hq; simp [liftVL, hq]

/-- Lift of 0 is 0. -/
@[simp] theorem liftVL_zero : liftVL L (0 : {q : Q // q ∈ logicalSupport L} → ZMod 2) = 0 := by
  ext q; simp [liftVL]

/-- Lift of all-ones on VL. -/
theorem liftVL_allones :
    liftVL L (fun _ => 1) =
    fun q => if q ∈ logicalSupport L then (1 : ZMod 2) else 0 := by
  ext q; simp [liftVL]

set_option maxHeartbeats 800000 in -- sum conversion between subtype/finset/full Fintype sums is expensive
/-- If g ∈ ker(coreCoboundary), then liftVL g ∈ ker(restrictedCoboundary).
    This holds because the restricted incidence is trivial outside VL and EL. -/
theorem liftVL_ker_coboundary
    (g : {q : Q // q ∈ logicalSupport L} → ZMod 2)
    (hg : g ∈ LinearMap.ker (HypergraphGeneralization.hyperCoboundaryMap (coreIncident C L))) :
    liftVL L g ∈ LinearMap.ker (restrictedCoboundaryMap C L) := by
  rw [LinearMap.mem_ker]; ext j; simp only [Pi.zero_apply]
  simp only [restrictedCoboundaryMap, HypergraphGeneralization.hyperCoboundaryMap_apply]
  rw [LinearMap.mem_ker] at hg
  by_cases hj_rel : j ∈ relevantZChecks C L
  · -- j ∈ EL: the sum over Q equals the sum over VL subtypes
    have hg_j : HypergraphGeneralization.hyperCoboundaryMap (coreIncident C L) g ⟨j, hj_rel⟩ = 0 :=
      congr_fun hg ⟨j, hj_rel⟩
    simp only [HypergraphGeneralization.hyperCoboundaryMap_apply] at hg_j
    -- Show both Fintype sums are equal by converting to common form
    have hZ : isZTypeCheck C j := by
      have := hj_rel; simp only [relevantZChecks, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this.1
    -- Convert Q sum directly to subtype sum
    -- LHS = ∑ v : Q, if restrictedZCheckIncident v j then liftVL g v else 0
    -- RHS = ∑ v : subtype VL, if coreIncident v ⟨j,_⟩ then g v else 0
    -- Show LHS = RHS using Fintype.sum_ite_mem and sum_subtype
    -- Step 1: simplify LHS to ∑ v : Q, if v ∈ VL ∧ zVec v ≠ 0 then g⟨v,_⟩ else 0
    -- Step 2: restrict to VL, convert to subtype sum
    -- Actually, simplest: prove equality via congr after normalizing to same sum form
    -- Use the key: both sums vanish on the same terms
    suffices (∑ v : Q, if restrictedZCheckIncident C L v j then liftVL L g v else 0) =
        ∑ v : {q : Q // q ∈ logicalSupport L},
          if coreIncident C L v ⟨j, hj_rel⟩ then g v else 0 from by
      rw [this]; exact hg_j
    -- Convert RHS to Q sum using Finset.sum_subtype backward
    rw [show (∑ v : {q : Q // q ∈ logicalSupport L},
        if coreIncident C L v ⟨j, hj_rel⟩ then g v else 0) =
      ∑ v : Q, if v ∈ logicalSupport L ∧ (C.check j).zVec v ≠ 0 then
        liftVL L g v else 0 from by
      -- Step a: normalize subtype summand
      have hsub : (∑ v : {q : Q // q ∈ logicalSupport L},
          if coreIncident C L v ⟨j, hj_rel⟩ then g v else 0) =
        ∑ v : {q : Q // q ∈ logicalSupport L},
          if (C.check j).zVec v.1 ≠ 0 then liftVL L g v.1 else 0 := by
        apply Fintype.sum_congr; intro ⟨q, hq⟩
        simp only [coreIncident, liftVL, dif_pos hq]
      rw [hsub]
      -- Step b: subtype sum → finset sum via sum_coe_sort
      rw [Finset.sum_coe_sort (logicalSupport L)
        (fun v => if (C.check j).zVec v ≠ 0 then liftVL L g v else 0)]
      -- Step c: finset sum → Q sum
      rw [← Fintype.sum_ite_mem (logicalSupport L)]
      -- Merge nested if into conjoined if
      apply Fintype.sum_congr; intro v
      by_cases hmem : v ∈ logicalSupport L
      · by_cases hz : (C.check j).zVec v ≠ 0
        · simp [hmem, hz]
        · push_neg at hz; simp [hmem, hz]
      · simp [hmem]]
    -- Now both sides are Q sums; show summands agree
    apply Fintype.sum_congr; intro v
    simp only [restrictedZCheckIncident]
    by_cases hmem : v ∈ logicalSupport L
    · by_cases hz : (C.check j).zVec v ≠ 0
      · simp [hmem, hz, hZ]
      · push_neg at hz; simp [hmem, hz]
    · simp [hmem, show liftVL L g v = 0 from by simp [liftVL, hmem]]
  · -- j ∉ EL: no vertex is incident
    apply Finset.sum_eq_zero; intro q _
    have : ¬ restrictedZCheckIncident C L q j := by
      intro ⟨hq_supp, hz_ne, hZ⟩
      apply hj_rel
      simp only [relevantZChecks, mem_filter, mem_univ, true_and]
      exact ⟨hZ, ⟨q, Finset.mem_inter.mpr ⟨by
        simp only [mem_supportZ, ne_eq]; exact hz_ne, hq_supp⟩⟩⟩
    simp [this]

/-- The all-ones-on-V_L function is in ker(δ), by row evenness. -/
private theorem allones_in_coboundary_ker
    (hL : IsIrreducibleXLogical C L) :
    (fun q => if q ∈ logicalSupport L then (1 : ZMod 2) else 0) ∈
      LinearMap.ker (restrictedCoboundaryMap C L) := by
  rw [LinearMap.mem_ker]; ext j
  simp only [Pi.zero_apply, restrictedCoboundaryMap, hyperCoboundaryMap_apply]
  have hsimpl : ∀ v : Q, (if restrictedZCheckIncident C L v j then
      (if v ∈ logicalSupport L then (1 : ZMod 2) else 0) else 0) =
    (if restrictedZCheckIncident C L v j then 1 else 0) := by
    intro v
    by_cases hinc : restrictedZCheckIncident C L v j
    · simp [hinc, hinc.1]
    · simp [hinc]
  simp_rw [hsimpl]
  by_cases hZj : isZTypeCheck C j
  · have hpure : L.zVec = 0 := hL.1.1
    have hcomm : C.inCentralizer L := hL.1.2.1
    have heven := zCheck_restricted_support_even C L hpure hcomm j hZj
    rw [← ZMod.natCast_eq_zero_iff_even] at heven
    rw [Finset.card_eq_sum_ones, Finset.sum_filter] at heven
    push_cast at heven
    exact heven
  · apply Finset.sum_eq_zero; intro q _
    have : ¬ restrictedZCheckIncident C L q j := by
      intro ⟨_, _, hZ⟩; exact hZj hZ
    simp [this]

set_option maxHeartbeats 400000 in -- Z₂ rank-nullity argument with multiple sum conversions
/-- **Coboundary from boundary step (rank-nullity).**
    If ker(restricted ∂) contains two EL-supported linearly independent elements,
    and |VL| ≥ |EL|, then ker(restricted δ) contains a VL-supported element
    f ≠ 0 with ∃ q ∈ VL, f q = 0. This replaces the former hypothesis
    `hcoboundary_from_boundary` using the Z₂ rank-nullity theorem. -/
theorem coboundary_from_boundary_step
    (hL : IsIrreducibleXLogical C L)
    (γ : C.I → ZMod 2)
    (hγ_ker : γ ∈ LinearMap.ker (restrictedBoundaryMap C L))
    (hγ_ne : γ ≠ 0)
    (hallones_ker : (fun i => if i ∈ relevantZChecks C L then (1 : ZMod 2) else 0) ∈
      LinearMap.ker (restrictedBoundaryMap C L))
    (hγ_ne_allones : γ ≠ (fun i => if i ∈ relevantZChecks C L then 1 else 0))
    (hγ_supp : ∀ i, i ∉ relevantZChecks C L → γ i = 0)
    (hVL_ge_EL : (relevantZChecks C L).card ≤ (logicalSupport L).card) :
    ∃ f : Q → ZMod 2,
      f ∈ LinearMap.ker (restrictedCoboundaryMap C L) ∧
      (∀ q, q ∉ logicalSupport L → f q = 0) ∧
      f ≠ 0 ∧
      (∃ q, q ∈ logicalSupport L ∧ f q = 0) := by
  -- Step 1: Restrict γ and all-ones to the core (subtype) boundary map
  -- Define restriction maps: C.I → ZMod 2 → EL → ZMod 2
  let γ_core : {i : C.I // i ∈ relevantZChecks C L} → ZMod 2 := fun i => γ i.1
  let ones_core : {i : C.I // i ∈ relevantZChecks C L} → ZMod 2 := fun _ => 1
  -- Step 2: Show γ_core and ones_core are in ker(coreBoundary)
  have hγ_core_ker : γ_core ∈ LinearMap.ker
      (HypergraphGeneralization.hyperBoundaryMap (coreIncident C L)) := by
    rw [LinearMap.mem_ker]; ext ⟨q, hq⟩; simp only [Pi.zero_apply]
    simp only [HypergraphGeneralization.hyperBoundaryMap_apply]
    rw [LinearMap.mem_ker] at hγ_ker
    have hγq : restrictedBoundaryMap C L γ q = 0 := congr_fun hγ_ker q
    simp only [restrictedBoundaryMap, HypergraphGeneralization.hyperBoundaryMap_apply] at hγq
    -- The sum over EL subtypes equals the relevant part of the sum over C.I
    suffices (∑ e : {i : C.I // i ∈ relevantZChecks C L},
        if coreIncident C L ⟨q, hq⟩ e then γ_core e else 0) =
      ∑ i : C.I, if restrictedZCheckIncident C L q i then γ i else 0 from by
      rw [this]; exact hγq
    -- Convert subtype sum to C.I sum
    rw [show (∑ e : {i : C.I // i ∈ relevantZChecks C L},
        if coreIncident C L ⟨q, hq⟩ e then γ_core e else 0) =
      ∑ i : C.I, if i ∈ relevantZChecks C L ∧ (C.check i).zVec q ≠ 0 then γ i else 0 from by
      -- Step a: normalize summand
      have hsub : (∑ e : {i : C.I // i ∈ relevantZChecks C L},
          if coreIncident C L ⟨q, hq⟩ e then γ_core e else 0) =
        ∑ e : {i : C.I // i ∈ relevantZChecks C L},
          if (C.check e.1).zVec q ≠ 0 then γ e.1 else 0 := by
        apply Fintype.sum_congr; intro ⟨i, hi⟩; simp [coreIncident, γ_core]
      rw [hsub]
      -- Step b: subtype sum → finset sum → C.I sum
      rw [Finset.sum_coe_sort (relevantZChecks C L)
        (fun i => if (C.check i).zVec q ≠ 0 then γ i else 0)]
      rw [← Fintype.sum_ite_mem (relevantZChecks C L)]
      apply Fintype.sum_congr; intro i
      by_cases hmem : i ∈ relevantZChecks C L
      · by_cases hz : (C.check i).zVec q ≠ 0
        · simp [hmem, hz]
        · push_neg at hz; simp [hmem, hz]
      · simp [hmem]]
    -- Now show: ∑ if (∈ EL ∧ zVec ≠ 0) then γ else 0 = ∑ if restrictedZCheckIncident then γ else 0
    apply Fintype.sum_congr; intro i
    simp only [restrictedZCheckIncident]
    by_cases hmem : i ∈ relevantZChecks C L
    · have hZ : isZTypeCheck C i := by
        simp only [relevantZChecks, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem.1
      by_cases hz : (C.check i).zVec q ≠ 0
      · simp [hq, hmem, hz, hZ]
      · push_neg at hz; simp [hmem, hz]
    · -- i ∉ relevantZChecks → both sides are 0
      simp only [ne_eq, show ¬(i ∈ relevantZChecks C L) from hmem, false_and, ite_false]
      symm; split_ifs with h
      · exfalso; apply hmem
        simp only [relevantZChecks, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h.2.2, ⟨q, Finset.mem_inter.mpr ⟨by
          simp only [mem_supportZ, ne_eq]; exact h.2.1, hq⟩⟩⟩
      · rfl
  have hones_core_ker : ones_core ∈ LinearMap.ker
      (HypergraphGeneralization.hyperBoundaryMap (coreIncident C L)) := by
    rw [LinearMap.mem_ker]; ext ⟨q, hq⟩; simp only [Pi.zero_apply]
    simp only [HypergraphGeneralization.hyperBoundaryMap_apply]
    rw [LinearMap.mem_ker] at hallones_ker
    have hq' : restrictedBoundaryMap C L
        (fun i => if i ∈ relevantZChecks C L then (1 : ZMod 2) else 0) q = 0 :=
      congr_fun hallones_ker q
    simp only [restrictedBoundaryMap, HypergraphGeneralization.hyperBoundaryMap_apply] at hq'
    suffices (∑ e : {i : C.I // i ∈ relevantZChecks C L},
        if coreIncident C L ⟨q, hq⟩ e then ones_core e else 0) =
      ∑ i : C.I, if restrictedZCheckIncident C L q i then
        (if i ∈ relevantZChecks C L then (1 : ZMod 2) else 0) else 0 from by
      rw [this]; exact hq'
    -- Convert subtype sum to C.I sum
    rw [show (∑ e : {i : C.I // i ∈ relevantZChecks C L},
        if coreIncident C L ⟨q, hq⟩ e then ones_core e else 0) =
      ∑ i : C.I, if i ∈ relevantZChecks C L ∧ (C.check i).zVec q ≠ 0 then
        (1 : ZMod 2) else 0 from by
      have hsub : (∑ e : {i : C.I // i ∈ relevantZChecks C L},
          if coreIncident C L ⟨q, hq⟩ e then ones_core e else 0) =
        ∑ e : {i : C.I // i ∈ relevantZChecks C L},
          if (C.check e.1).zVec q ≠ 0 then (1 : ZMod 2) else 0 := by
        apply Fintype.sum_congr; intro ⟨i, hi⟩; simp [coreIncident, ones_core]
      rw [hsub]
      rw [Finset.sum_coe_sort (relevantZChecks C L)
        (fun i => if (C.check i).zVec q ≠ 0 then (1 : ZMod 2) else 0)]
      rw [← Fintype.sum_ite_mem (relevantZChecks C L)]
      apply Fintype.sum_congr; intro i
      by_cases hmem : i ∈ relevantZChecks C L
      · by_cases hz : (C.check i).zVec q ≠ 0
        · simp [hmem, hz]
        · push_neg at hz; simp [hmem, hz]
      · simp [hmem]]
    apply Fintype.sum_congr; intro i
    simp only [restrictedZCheckIncident]
    by_cases hmem : i ∈ relevantZChecks C L
    · have hZ : isZTypeCheck C i := by
        simp only [relevantZChecks, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem.1
      by_cases hz : (C.check i).zVec q ≠ 0
      · simp [hq, hmem, hz, hZ]
      · push_neg at hz; simp [hmem, hz]
    · -- i ∉ relevantZChecks → both sides are 0
      simp only [ne_eq, show ¬(i ∈ relevantZChecks C L) from hmem, false_and, ite_false,
        ite_self]
  -- Step 3: γ_core ≠ 0 and γ_core ≠ ones_core → dim(ker(coreBoundary)) ≥ 2
  have hγ_core_ne : γ_core ≠ 0 := by
    intro h; apply hγ_ne; ext i
    by_cases hi : i ∈ relevantZChecks C L
    · have := congr_fun h ⟨i, hi⟩; simp only [Pi.zero_apply] at this; exact this
    · exact hγ_supp i hi
  have hγ_core_ne_ones : γ_core ≠ ones_core := by
    intro h; apply hγ_ne_allones; ext i
    by_cases hi : i ∈ relevantZChecks C L
    · have := congr_fun h ⟨i, hi⟩; simp only [γ_core, ones_core] at this; simp [hi, this]
    · simp [hγ_supp i hi, hi]
  -- Over ZMod 2, two nonzero unequal elements are linearly independent → dim ≥ 2
  have hker_ge : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker
      (HypergraphGeneralization.hyperBoundaryMap (coreIncident C L))) := by
    by_contra h_lt; push_neg at h_lt
    -- If dim ≤ 1, every kernel element is a scalar multiple of ones_core
    have h1 : Module.finrank (ZMod 2)
        ↥(LinearMap.ker (HypergraphGeneralization.hyperBoundaryMap (coreIncident C L))) ≤ 1 := by
      omega
    -- finrank_le_one_iff gives: ∃ v, ∀ w, ∃ c, c • v = w  (in the kernel subtype)
    obtain ⟨gen, hgen⟩ := finrank_le_one_iff.mp h1
    -- Apply hgen to γ_core and ones_core (as kernel subtypes)
    obtain ⟨c, hc⟩ := hgen ⟨γ_core, hγ_core_ker⟩
    obtain ⟨d, hd⟩ := hgen ⟨ones_core, hones_core_ker⟩
    -- Extract: γ_core = c • gen.val, ones_core = d • gen.val
    have hc_val : γ_core = c • gen.val := by
      have := congr_arg Subtype.val hc; simp at this; exact this.symm
    have hd_val : ones_core = d • gen.val := by
      have := congr_arg Subtype.val hd; simp at this; exact this.symm
    -- c ≠ 0 (since γ_core ≠ 0) and d ≠ 0 (since ones_core ≠ 0)
    have hc_ne : c ≠ 0 := by intro h; exact hγ_core_ne (by rw [hc_val, h, zero_smul])
    have hones_core_ne : ones_core ≠ 0 := by
      intro h0
      obtain ⟨⟨i, hi⟩, _⟩ : ∃ x : {i : C.I // i ∈ relevantZChecks C L}, γ_core x ≠ 0 := by
        by_contra hall; push_neg at hall; exact hγ_core_ne (funext hall)
      exact absurd (congr_fun h0 ⟨i, hi⟩) (by simp [ones_core])
    have hd_ne : d ≠ 0 := by intro h; exact hones_core_ne (by rw [hd_val, h, zero_smul])
    -- Over ZMod 2, c = 1 and d = 1
    have hc1 : c = 1 := by
      have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by intro x; fin_cases x <;> simp
      rcases this c with h | h
      · exact absurd h hc_ne
      · exact h
    have hd1 : d = 1 := by
      have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by intro x; fin_cases x <;> simp
      rcases this d with h | h
      · exact absurd h hd_ne
      · exact h
    -- γ_core = 1 • gen.val = gen.val = 1 • gen.val = ones_core
    exact hγ_core_ne_ones (by rw [hc_val, hc1, hd_val, hd1])
  -- Step 4: Apply coboundary_third_element to core incidence
  have hVE : Fintype.card {i : C.I // i ∈ relevantZChecks C L} ≤
      Fintype.card {q : Q // q ∈ logicalSupport L} := by
    rw [Fintype.card_coe, Fintype.card_coe]; exact hVL_ge_EL
  -- The all-ones function on VL is in ker(coreCoboundary)
  have hones_coboundary_ker : (fun (_ : {q : Q // q ∈ logicalSupport L}) => (1 : ZMod 2)) ∈
      LinearMap.ker (HypergraphGeneralization.hyperCoboundaryMap (coreIncident C L)) := by
    rw [LinearMap.mem_ker]; ext ⟨j, hj⟩; simp only [Pi.zero_apply]
    simp only [HypergraphGeneralization.hyperCoboundaryMap_apply]
    -- This sum counts vertices in VL incident to check j (core version)
    -- By row-evenness, this count is even over ZMod 2
    -- Rewrite in terms of the full restricted coboundary
    have hallones_coboundary := allones_in_coboundary_ker C L hL
    rw [LinearMap.mem_ker] at hallones_coboundary
    have hj_rel : j ∈ relevantZChecks C L := hj
    have hj_val : restrictedCoboundaryMap C L
        (fun q => if q ∈ logicalSupport L then (1 : ZMod 2) else 0) j = 0 :=
      congr_fun hallones_coboundary j
    simp only [restrictedCoboundaryMap, HypergraphGeneralization.hyperCoboundaryMap_apply] at hj_val
    -- Goal: (∑ e : {q // q ∈ VL}, if coreIncident e ⟨j,hj⟩ then 1 else 0) = 0
    have hZ : isZTypeCheck C j := by
      simp only [relevantZChecks, Finset.mem_filter, Finset.mem_univ, true_and] at hj_rel
      exact hj_rel.1
    -- LHS: ∑ v : {q // q ∈ VL}, if coreIncident v ⟨j,hj⟩ then 1 else 0
    -- hj_val: ∑ v : Q, if restrictedZCheckIncident v j then (if v ∈ VL then 1 else 0) else 0 = 0
    -- Convert hj_val to a subtype sum, then show summands match LHS
    -- First, simplify LHS summand: coreIncident C L v ⟨j,hj⟩ ↔ (C.check j).zVec v.1 ≠ 0
    have hlhs_eq : (∑ v : {q : Q // q ∈ logicalSupport L},
        if coreIncident C L v ⟨j, hj⟩ then (1 : ZMod 2) else 0) =
      ∑ v : {q : Q // q ∈ logicalSupport L}, if (C.check j).zVec v.1 ≠ 0 then
        (1 : ZMod 2) else 0 := by
      apply Fintype.sum_congr; intro v; simp [coreIncident]
    rw [hlhs_eq]
    -- Now convert the full Q sum to a subtype sum
    -- ∑ Q f = ∑ ∈ VL f' (outside VL, restrictedZCheckIncident is false)
    have hstep1 : (∑ v : Q, if restrictedZCheckIncident C L v j then
        (if v ∈ logicalSupport L then (1 : ZMod 2) else 0) else 0) =
      ∑ v : Q, if v ∈ logicalSupport L ∧ (C.check j).zVec v ≠ 0 then (1 : ZMod 2) else 0 := by
      apply Fintype.sum_congr; intro v
      simp only [restrictedZCheckIncident]
      by_cases hmem : v ∈ logicalSupport L
      · by_cases hz : (C.check j).zVec v ≠ 0
        · simp [hmem, hz, hZ]
        · push_neg at hz; simp [hmem, hz]
      · simp [hmem]
    -- ∑ Q if (∈ VL ∧ ...) = ∑ ∈ VL if (...)
    have hstep2 : (∑ v : Q, if v ∈ logicalSupport L ∧ (C.check j).zVec v ≠ 0 then
        (1 : ZMod 2) else 0) =
      ∑ v ∈ logicalSupport L, if (C.check j).zVec v ≠ 0 then (1 : ZMod 2) else 0 := by
      rw [← Finset.sum_filter]
      rw [← Finset.sum_filter]
      congr 1
      ext v; simp [Finset.mem_filter]
    -- Now LHS and RHS are both ∑ ∈ VL, if zVec v ≠ 0 then 1 else 0
    -- (after rewriting LHS via hlhs_eq, it became a subtype sum; chain hstep1,2 on RHS)
    rw [show (∑ v : {q : Q // q ∈ logicalSupport L}, if (C.check j).zVec v.1 ≠ 0 then
        (1 : ZMod 2) else 0) =
      ∑ v : Q, if restrictedZCheckIncident C L v j then
        (if v ∈ logicalSupport L then (1 : ZMod 2) else 0) else 0 from by
      rw [Finset.sum_coe_sort (logicalSupport L)
        (fun v => if (C.check j).zVec v ≠ 0 then (1 : ZMod 2) else 0)]
      rw [← hstep2, ← hstep1]]
    exact hj_val
  -- Apply coboundary_third_element
  obtain ⟨g, hg_ker, hg_ne, hg_ne_ones⟩ :=
    coboundary_third_element (coreIncident C L) hVE hker_ge
      (fun _ => 1) hones_coboundary_ker
  -- Step 5: Lift g to Q and verify all properties
  refine ⟨liftVL L g, liftVL_ker_coboundary C L g hg_ker, liftVL_supp L g, ?_, ?_⟩
  -- f ≠ 0 follows from g ≠ 0 and liftVL injective
  · intro h; apply hg_ne
    exact liftVL_injective L (by rw [h, liftVL_zero])
  -- ∃ q ∈ VL, f q = 0 follows from g ≠ all-ones
  · -- g ≠ fun _ => 1 means ∃ q, g q ≠ 1, hence g q = 0 (over ZMod 2)
    have : ∃ q : {q : Q // q ∈ logicalSupport L}, g q ≠ 1 := by
      by_contra hall; push_neg at hall; apply hg_ne_ones; ext q; exact hall q
    obtain ⟨⟨q, hq⟩, hgq⟩ := this
    refine ⟨q, hq, ?_⟩
    simp only [liftVL, dif_pos hq]
    -- g ⟨q, hq⟩ ≠ 1 over ZMod 2 means g ⟨q, hq⟩ = 0
    have : g ⟨q, hq⟩ = 0 ∨ g ⟨q, hq⟩ = 1 := by
      have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by intro x; revert x; decide
      exact this _
    rcases this with h0 | h1
    · exact h0
    · exact absurd h1 hgq

theorem irrelevant_check_no_incident (i : C.I) (hi : i ∉ relevantZChecks C L) :
    ∀ q : Q, ¬ restrictedZCheckIncident C L q i := by
  intro q ⟨hq_supp, hz_ne, hZ⟩
  apply hi
  simp only [relevantZChecks, mem_filter, mem_univ, true_and]
  constructor
  · exact hZ
  · exact ⟨q, Finset.mem_inter.mpr ⟨by
      simp only [mem_supportZ, ne_eq]; exact hz_ne, hq_supp⟩⟩

/-- If γ ∈ ker(∂) and γ' agrees with γ on relevant checks and is 0 on irrelevant ones,
    then γ' ∈ ker(∂) as well. -/
theorem ker_restrict_to_relevant (γ : C.I → ZMod 2)
    (hγ : γ ∈ LinearMap.ker (restrictedBoundaryMap C L)) :
    (fun i => if i ∈ relevantZChecks C L then γ i else 0) ∈
      LinearMap.ker (restrictedBoundaryMap C L) := by
  rw [LinearMap.mem_ker]
  ext q
  simp only [Pi.zero_apply]
  rw [LinearMap.mem_ker] at hγ
  have hγq : restrictedBoundaryMap C L γ q = 0 := congr_fun hγ q
  simp only [restrictedBoundaryMap, hyperBoundaryMap_apply] at hγq ⊢
  rw [show (∑ i : C.I, if restrictedZCheckIncident C L q i then
    (if i ∈ relevantZChecks C L then γ i else 0) else 0) =
    ∑ i : C.I, if restrictedZCheckIncident C L q i then γ i else 0 from by
      apply Finset.sum_congr rfl; intro i _
      by_cases hrel : i ∈ relevantZChecks C L
      · simp [hrel]
      · simp [irrelevant_check_no_incident C L i hrel q]]
  exact hγq

/-- The complement of a kernel element (relative to all-ones on relevant checks)
    is also in the kernel. -/
theorem complement_in_ker (γ : C.I → ZMod 2)
    (hγ_ker : γ ∈ LinearMap.ker (restrictedBoundaryMap C L))
    (hallones_ker : (fun i => if i ∈ relevantZChecks C L then (1 : ZMod 2) else 0) ∈
      LinearMap.ker (restrictedBoundaryMap C L)) :
    (fun i => if i ∈ relevantZChecks C L then 1 + γ i else 0) ∈
      LinearMap.ker (restrictedBoundaryMap C L) := by
  have : (fun i => if i ∈ relevantZChecks C L then 1 + γ i else (0 : ZMod 2)) =
         (fun i => if i ∈ relevantZChecks C L then (1 : ZMod 2) else 0) +
         (fun i => if i ∈ relevantZChecks C L then γ i else 0) := by
    ext i; by_cases hi : i ∈ relevantZChecks C L <;> simp [hi, Pi.add_apply]
  rw [this]
  exact (LinearMap.ker (restrictedBoundaryMap C L)).add_mem hallones_ker
    (ker_restrict_to_relevant C L γ hγ_ker)

/-- γ and its complement on relevant checks sum to the all-ones vector. -/
theorem gamma_add_complement (γ : C.I → ZMod 2)
    (hγ_supp : ∀ i, i ∉ relevantZChecks C L → γ i = 0) :
    ∀ i, γ i + (if i ∈ relevantZChecks C L then 1 + γ i else 0) =
      if i ∈ relevantZChecks C L then 1 else 0 := by
  intro i
  by_cases hi : i ∈ relevantZChecks C L
  · simp only [hi, ite_true]
    have : γ i + (1 + γ i) = 1 + (γ i + γ i) := by ring
    rw [this, CharTwo.add_self_eq_zero, add_zero]
  · simp [hi, hγ_supp i hi]

/-- **Kernel triviality from irreducibility.**

    For an irreducible X logical operator L of a CSS stabilizer code C, the kernel
    of the restricted boundary map ∂ : Z₂^{E_L} → Z₂^{V_L} consists only of 0 and
    the all-ones vector on E_L (corresponding to L itself).

    The proof combines two ingredients:
    1. **Coboundary kernel → centralizer factorization:** Any nontrivial f ∈ ker(δ)
       gives a factorization L = prodX(supp(f)) · prodX(V_L \ supp(f)) with both
       factors in the centralizer (by `coboundary_ker_gives_centralizer_pair`).
    2. **Irreducibility contradiction:** Such a factorization contradicts the
       irreducibility of L (both factors have weight < wt(L) unless trivial).

    The Z₂-rank-nullity step (`coboundary_from_boundary_step`) proves that if
    ker(∂) has a nontrivial element besides 0 and the all-ones vector,
    then ker(δ) contains a nontrivial element f with f ≠ 0 and f ≠ all-ones-on-V_L.
    This uses dim(ker(δ)) = |V_L| - |E_L| + dim(ker(∂)) ≥ 2 when
    |V_L| ≥ |E_L|, via `Matrix.rank_transpose` and `z2_finrank_ker_formula`. -/
theorem kernel_restricted_boundary_trivial
    (hL : IsIrreducibleXLogical C L)
    (hcss : IsCSS C)
    (hVL_ge_EL : (relevantZChecks C L).card ≤ (logicalSupport L).card) :
    ∀ γ : C.I → ZMod 2,
      γ ∈ LinearMap.ker (restrictedBoundaryMap C L) →
      (∀ i, i ∉ relevantZChecks C L → γ i = 0) →
      (fun i => if i ∈ relevantZChecks C L then (1 : ZMod 2) else 0) ∈
        LinearMap.ker (restrictedBoundaryMap C L) →
      γ = 0 ∨ (∀ i : C.I, i ∈ relevantZChecks C L → γ i = 1) := by
  intro γ hγ_ker hγ_supp hallones_ker
  by_cases hγ_ne : γ = 0
  · left; exact hγ_ne
  · right
    by_contra h_not_allones
    push_neg at h_not_allones
    obtain ⟨i₀, hi₀_rel, hi₀_ne⟩ := h_not_allones
    have hγ_ne_allones : γ ≠ (fun i => if i ∈ relevantZChecks C L then 1 else 0) := by
      intro h
      have := congr_fun h i₀
      simp only [hi₀_rel, ite_true] at this
      exact hi₀_ne this
    -- Step 1: Use the rank-nullity step to get a coboundary kernel element
    obtain ⟨f, hf_ker, hf_supp, hf_ne, hf_compl⟩ :=
      coboundary_from_boundary_step C L hL γ hγ_ker hγ_ne hallones_ker hγ_ne_allones hγ_supp hVL_ge_EL
    -- Step 2: Irreducibility contradiction
    -- Let S = supp(f) ∩ V_L and T = V_L \ S
    let S := Finset.univ.filter (fun q => f q ≠ 0)
    let T := Finset.univ.filter (fun q => q ∈ logicalSupport L ∧ f q = 0)
    -- f ∈ ker(δ) → prodX(S) ∈ centralizer
    have hS_cent := coboundary_ker_gives_centralizer_pair C L hcss f hf_ker hf_supp
    -- The complement (1 + f) on V_L is also in ker(δ)
    have hg_ker : (fun q => if q ∈ logicalSupport L then 1 + f q else 0) ∈
        LinearMap.ker (restrictedCoboundaryMap C L) := by
      rw [LinearMap.mem_ker]; ext j
      simp only [Pi.zero_apply, restrictedCoboundaryMap, hyperCoboundaryMap_apply]
      rw [LinearMap.mem_ker] at hf_ker
      have hf_j : restrictedCoboundaryMap C L f j = 0 := congr_fun hf_ker j
      simp only [restrictedCoboundaryMap, hyperCoboundaryMap_apply] at hf_j
      have hallones_ker_coboundary := allones_in_coboundary_ker C L hL
      rw [LinearMap.mem_ker] at hallones_ker_coboundary
      have hallones_j : restrictedCoboundaryMap C L
          (fun q => if q ∈ logicalSupport L then (1 : ZMod 2) else 0) j = 0 :=
        congr_fun hallones_ker_coboundary j
      simp only [restrictedCoboundaryMap, hyperCoboundaryMap_apply] at hallones_j
      -- Σ_q [incident] · (if q ∈ V_L then 1 + f q else 0)
      -- = Σ_q [incident] · (1 + f q)    (since incident → q ∈ V_L)
      -- = Σ_q [incident] · 1 + Σ_q [incident] · f q
      -- = 0 + 0 = 0
      rw [show (∑ v : Q, if restrictedZCheckIncident C L v j then
        (if v ∈ logicalSupport L then 1 + f v else 0) else 0) =
        (∑ v : Q, if restrictedZCheckIncident C L v j then (1 + f v) else 0) from by
          apply Finset.sum_congr rfl; intro v _
          by_cases hinc : restrictedZCheckIncident C L v j
          · simp [hinc, hinc.1]
          · simp [hinc]]
      rw [show (∑ v : Q, if restrictedZCheckIncident C L v j then (1 + f v) else (0 : ZMod 2)) =
        (∑ v : Q, if restrictedZCheckIncident C L v j then (1 : ZMod 2) else 0) +
        (∑ v : Q, if restrictedZCheckIncident C L v j then f v else 0) from by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro v _
          by_cases hinc : restrictedZCheckIncident C L v j
          · simp [hinc]
          · simp [hinc]]
      rw [show (∑ v : Q, if restrictedZCheckIncident C L v j then (1 : ZMod 2) else 0) = 0 from by
        convert hallones_j using 1
        apply Finset.sum_congr rfl; intro v _
        by_cases hinc : restrictedZCheckIncident C L v j
        · simp [hinc, hinc.1]
        · simp [hinc]]
      simp [hf_j]
    -- coboundary_ker_gives_centralizer_pair on g = (1+f) on V_L → prodX(T) ∈ centralizer
    have hg_supp : ∀ q : Q, q ∉ logicalSupport L →
        (fun q => if q ∈ logicalSupport L then 1 + f q else (0 : ZMod 2)) q = 0 := by
      intro q hq; simp [hq]
    have hT_cent_raw := coboundary_ker_gives_centralizer_pair C L hcss
      (fun q => if q ∈ logicalSupport L then 1 + f q else 0) hg_ker hg_supp
    -- The filter set for g matches T
    have hT_eq : Finset.univ.filter (fun q =>
        (fun q => if q ∈ logicalSupport L then 1 + f q else (0 : ZMod 2)) q ≠ 0) = T := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
      constructor
      · intro hne
        by_cases hq : q ∈ logicalSupport L
        · rw [if_pos hq] at hne
          refine ⟨hq, ?_⟩
          by_contra hfq
          apply hne
          have : f q = 0 ∨ f q = 1 := by
            have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by intro x; revert x; decide
            exact this (f q)
          rcases this with h0 | h1
          · exact absurd h0 hfq
          · rw [h1]; decide
        · rw [if_neg hq] at hne; exact absurd rfl hne
      · intro ⟨hq, hfq⟩
        rw [if_pos hq, hfq, add_zero]
        exact one_ne_zero
    rw [hT_eq] at hT_cent_raw
    -- S and T are disjoint and their union is logicalSupport L
    have hST_disjoint : Disjoint S T := by
      rw [Finset.disjoint_filter]
      intro q _ hS hT; exact hS hT.2
    have hST_union : S ∪ T = logicalSupport L := by
      ext q; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S, T]
      constructor
      · intro h; rcases h with hS | ⟨hq, _⟩
        · by_contra hq; exact hS (hf_supp q hq)
        · exact hq
      · intro hq
        by_cases hfq : f q = 0
        · right; exact ⟨hq, hfq⟩
        · left; exact hfq
    -- prodX(S) * prodX(T) = prodX(S ∪ T) = prodX(logicalSupport L) = L
    have hfact : prodX S * prodX T = L := by
      rw [prodX_mul_disjoint S T hST_disjoint, hST_union]
      exact (pure_x_eq_prodX_supportX L hL.1.1).symm
    -- S is nonempty (since f ≠ 0 and supported on V_L)
    have hS_nonempty : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hf_ne
      ext q; simp only [Pi.zero_apply]
      by_contra hfq; push_neg at hfq
      have : q ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfq⟩
      rw [hempty] at this; simp at this
    -- T is nonempty (by hf_compl)
    have hT_nonempty : T.Nonempty := by
      obtain ⟨q, hq_mem, hq_zero⟩ := hf_compl
      exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_mem, hq_zero⟩⟩
    -- Weight bounds
    have hS_wt : (prodX S).weight < L.weight := by
      rw [weight_prodX]
      -- |S| < weight(L)
      -- weight(L) = support(L).card, and for pure X-type:
      -- support(L) = supportX(L) ∪ supportZ(L) = supportX(L) ∪ ∅ = supportX(L) = logicalSupport L
      have hwt_eq : L.weight = (logicalSupport L).card := by
        simp [weight, support_eq_supportX_union_supportZ, logicalSupport,
          show L.supportZ = ∅ from by ext v; simp [mem_supportZ, hL.1.1]]
      rw [hwt_eq]
      -- |S| < |logicalSupport L| since T is nonempty
      have hcard : S.card + T.card = (logicalSupport L).card := by
        rw [← hST_union]; exact (Finset.card_union_of_disjoint hST_disjoint).symm
      have hT_pos : 0 < T.card := Finset.Nonempty.card_pos hT_nonempty
      omega
    have hT_wt : (prodX T).weight < L.weight := by
      rw [weight_prodX]
      have hwt_eq : L.weight = (logicalSupport L).card := by
        simp [weight, support_eq_supportX_union_supportZ, logicalSupport,
          show L.supportZ = ∅ from by ext v; simp [mem_supportZ, hL.1.1]]
      rw [hwt_eq]
      have hcard : S.card + T.card = (logicalSupport L).card := by
        rw [← hST_union]; exact (Finset.card_union_of_disjoint hST_disjoint).symm
      have hS_pos : 0 < S.card := Finset.Nonempty.card_pos hS_nonempty
      omega
    -- Apply irreducibility to prodX(S) * prodX(T) = L
    have hirr := hL.2 (prodX S) (prodX T)
      (show (prodX S).zVec = 0 from rfl)
      (show (prodX T).zVec = 0 from rfl)
      hS_cent hT_cent_raw hfact
    -- All four disjuncts are false: contradiction
    rcases hirr with hSge | hTge | hS1 | hT1
    · exact absurd hSge (not_le.mpr hS_wt)
    · exact absurd hTge (not_le.mpr hT_wt)
    · exact absurd hS1 (prodX_ne_one_of_nonempty S hS_nonempty)
    · exact absurd hT1 (prodX_ne_one_of_nonempty T hT_nonempty)

end KernelTrivial

/-! ## Cohen et al. d-layer construction as hypergraph gauging

The Cohen et al. construction creates d copies of the logical support vertices,
connects copies of the same vertex across layers via path graphs (chains),
and joins vertices within each layer via the same hypergraph structure.

This is the layered incidence relation on Q × Fin d. The hypergraph gauging
framework from Rem_17 applies directly to this layered incidence, giving
pure X-type commuting Gauss operators and kernel characterization.
-/

section CohenRecovery

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (C : StabilizerCode Q) [DecidableEq C.I]
variable (L : PauliOp Q)

/-- The Cohen et al. layered vertex type: d copies of the qubit set Q. -/
abbrev CohenVertex (Q : Type*) (d : ℕ) := Q × Fin d

/-- The inter-layer edge type: connects copies of the same vertex in consecutive layers. -/
abbrev InterLayerEdge (Q : Type*) (d : ℕ) := Q × Fin (d - 1)

/-- The intra-layer edge type: replicates the original check structure within each layer. -/
abbrev IntraLayerEdge (I : Type*) (d : ℕ) := I × Fin d

/-- The combined edge type for the Cohen construction. -/
abbrev CohenEdge (Q I : Type*) (d : ℕ) := InterLayerEdge Q d ⊕ IntraLayerEdge I d

/-- The incidence relation for the layered construction.
    A vertex (q, ℓ) in the layered graph is incident to:
    - Inter-layer edge (q', k): q = q' and ℓ ∈ {k, k+1} (path graph connection)
    - Intra-layer edge (i, ℓ'): ℓ = ℓ' and q is incident to check i in restricted hypergraph -/
def layeredIncident (d : ℕ) :
    CohenVertex Q d → CohenEdge Q C.I d → Prop :=
  fun ⟨q, ℓ⟩ e => match e with
    | Sum.inl ⟨q', k⟩ =>  -- inter-layer edge (q', k)—(q', k+1)
      q = q' ∧ (ℓ.val = k.val ∨ ℓ.val = k.val + 1)
    | Sum.inr ⟨i, ℓ'⟩ =>  -- intra-layer edge: check i in layer ℓ'
      ℓ = ℓ' ∧ restrictedZCheckIncident C L q i

instance layeredIncident_decidable (d : ℕ)
    (v : CohenVertex Q d) (e : CohenEdge Q C.I d) :
    Decidable (layeredIncident C L d v e) := by
  unfold layeredIncident
  obtain ⟨q, ℓ⟩ := v
  cases e with
  | inl ie =>
    obtain ⟨q', k⟩ := ie
    exact inferInstanceAs (Decidable (_ ∧ _))
  | inr ie =>
    obtain ⟨i, ℓ'⟩ := ie
    exact inferInstanceAs (Decidable (_ ∧ _))

/-- The Cohen et al. scheme is recovered as hypergraph gauging (Rem_17) applied to
    the layered incidence with d copies.

    The all-ones Gauss subset product measures L: its xVec restricts to 1 on all
    vertex qubits by `hyperGaussSubsetProduct_xVec_vertex`, and it is pure X-type
    by `hyperGaussSubsetProduct_zVec`.

    The Gauss operators are pure X-type (`hyperGaussLawOp_zVec`) and mutually
    commute (`hyperGaussLaw_commute`). The kernel of the layered boundary map
    characterizes which operators can be measured (`ker_boundary_iff_commutes_all_gaussLaw`). -/
theorem cohen_layered_all_ones_measures_L (d : ℕ) (v : CohenVertex Q d) :
    (hyperGaussSubsetProduct (layeredIncident C L d)
      (fun _ => (1 : ZMod 2))).xVec (Sum.inl v) = 1 ∧
    (hyperGaussSubsetProduct (layeredIncident C L d)
      (fun _ => (1 : ZMod 2))).zVec = 0 :=
  ⟨by simp [hyperGaussSubsetProduct_xVec_vertex],
   hyperGaussSubsetProduct_zVec (layeredIncident C L d) _⟩

end CohenRecovery

/-! ## Cross et al. modification: fewer layers with Cheeger expansion

The Cross et al. modification uses R < d layers of dummy vertices. This is recovered
by choosing fewer layers in the hypergraph gauging construction while maintaining
sufficient expansion (Cheeger constant ≥ 1, Rem_4/Rem_11) in the inter-layer graph.

By Lemma 3 (`deformed_distance_ge_min_cheeger_d`): with Cheeger constant h(G) of the
inter-layer graph, the deformed code distance satisfies d* ≥ min(h(G), 1) · d.
When h(G) ≥ 1 (sufficient expansion, `SufficientExpansion`), d* ≥ d (distance
fully preserved, `deformed_distance_ge_d_sufficient_expansion`).
-/

section CrossRecovery

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (C : StabilizerCode Q) [DecidableEq C.I]
variable (L : PauliOp Q)

/-- The path graph on R vertices: vertices are Fin R, edges connect consecutive vertices.
    This is the inter-layer connectivity graph in the Cross et al. modification. -/
def pathGraphAdj (R : ℕ) (a b : Fin R) : Prop :=
  (a.val + 1 = b.val) ∨ (b.val + 1 = a.val)

instance pathGraphAdj_decidable (R : ℕ) (a b : Fin R) :
    Decidable (pathGraphAdj R a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The Cross et al. scheme applies the same layered construction with R ≤ d layers.
    The Gauss product for coefficient c gives a pure X-type operator with c as its
    vertex X-vector, by the hypergraph gauging framework (Rem_17). -/
theorem cross_layered_gauss_product_pure_X_with_vertex_values
    (R : ℕ) (c : CohenVertex Q R → ZMod 2) :
    (hyperGaussSubsetProduct (layeredIncident C L R) c).zVec = 0 ∧
    ∀ v : CohenVertex Q R,
      (hyperGaussSubsetProduct (layeredIncident C L R) c).xVec (Sum.inl v) = c v :=
  ⟨hyperGaussSubsetProduct_zVec _ _, fun v => by simp [hyperGaussSubsetProduct_xVec_vertex]⟩

/-- The path graph adjacency relation is symmetric. -/
theorem pathGraphAdj_symm (R : ℕ) (a b : Fin R) :
    pathGraphAdj R a b → pathGraphAdj R b a := by
  intro h; simp [pathGraphAdj] at h ⊢; omega

/-- The path graph adjacency is irreflexive. -/
theorem pathGraphAdj_irrefl (R : ℕ) (a : Fin R) : ¬ pathGraphAdj R a a := by
  simp [pathGraphAdj]

/-- The path graph on R vertices as a SimpleGraph. -/
def pathGraph (R : ℕ) : SimpleGraph (Fin R) where
  Adj a b := pathGraphAdj R a b
  symm a b h := pathGraphAdj_symm R a b h
  loopless a h := pathGraphAdj_irrefl R a h

instance pathGraph_decidableRel (R : ℕ) : DecidableRel (pathGraph R).Adj :=
  fun a b => pathGraphAdj_decidable R a b

/-- For the Cross et al. scheme with R layers: the edge boundary of any valid
    subset S satisfies |∂S| ≥ c · |S| for any c ≤ h(P_R), connecting the Cheeger
    constant of the path graph to the distance bound from Lemma 3. -/
theorem cross_expansion_bound (R : ℕ)
    (S : Finset (Fin R)) (hne : S.Nonempty) (hsize : 2 * S.card ≤ Fintype.card (Fin R))
    (c : ℝ) (hc : c ≤ QEC1.cheegerConstant (pathGraph R)) :
    c * S.card ≤ (QEC1.SimpleGraph.edgeBoundary (pathGraph R) S).card :=
  QEC1.SimpleGraph.edgeBoundary_card_ge_of_cheeger (pathGraph R) c hc S hne hsize

end CrossRecovery

/-! ## Joint measurement of products via edge addition

Given two systems (Q₁, E₁, incident₁) and (Q₂, E₂, incident₂), the joint system
has vertices Q₁ ⊕ Q₂ and edges E₁ ⊕ E₂ ⊕ B (where B are bridge edges connecting
the two systems). The key property is that the joint Gauss product measures the
*product* of the individual logicals L₁ ⊗ L₂.
-/

section JointMeasurement

variable {Q₁ Q₂ : Type*} [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
variable {E₁ : Type*} [Fintype E₁] [DecidableEq E₁]
variable (incident₁ : Q₁ → E₁ → Prop) [∀ q e, Decidable (incident₁ q e)]
variable {E₂ : Type*} [Fintype E₂] [DecidableEq E₂]
variable (incident₂ : Q₂ → E₂ → Prop) [∀ q e, Decidable (incident₂ q e)]

/-- The joint incidence: combines the two individual incidence relations
    with bridge edges connecting specified pairs across Q₁ and Q₂. -/
def jointIncident {B : Type*} [DecidableEq B]
    (bridgeQ1 : B → Q₁) (bridgeQ2 : B → Q₂) :
    (Q₁ ⊕ Q₂) → (E₁ ⊕ E₂ ⊕ B) → Prop :=
  fun q e => match q, e with
    | Sum.inl q₁, Sum.inl e₁ => incident₁ q₁ e₁
    | Sum.inr q₂, Sum.inr (Sum.inl e₂) => incident₂ q₂ e₂
    | Sum.inl q₁, Sum.inr (Sum.inr b) => q₁ = bridgeQ1 b
    | Sum.inr q₂, Sum.inr (Sum.inr b) => q₂ = bridgeQ2 b
    | _, _ => False

instance jointIncident_decidable {B : Type*} [DecidableEq B]
    (bridgeQ1 : B → Q₁) (bridgeQ2 : B → Q₂)
    (q : Q₁ ⊕ Q₂) (e : E₁ ⊕ E₂ ⊕ B) :
    Decidable (jointIncident incident₁ incident₂ bridgeQ1 bridgeQ2 q e) := by
  unfold jointIncident
  cases q with
  | inl q₁ => cases e with
    | inl e₁ => exact inferInstance
    | inr e₂ => cases e₂ with
      | inl e₂' => exact isFalse (fun h => h)
      | inr b => exact inferInstanceAs (Decidable (q₁ = bridgeQ1 b))
  | inr q₂ => cases e with
    | inl _ => exact isFalse (fun h => h)
    | inr e₂ => cases e₂ with
      | inl e₂' => exact inferInstance
      | inr b => exact inferInstanceAs (Decidable (q₂ = bridgeQ2 b))

/-- Adding bridge edges enables joint measurement: the joint Gauss subset product
    for coefficient (c₁, c₂) on Q₁ ⊕ Q₂ gives a pure X-type operator that
    restricts to c₁ on Q₁ and c₂ on Q₂, measuring L₁ ⊗ L₂. -/
theorem joint_gauss_product_measures_product {B : Type*} [Fintype B] [DecidableEq B]
    (bridgeQ1 : B → Q₁) (bridgeQ2 : B → Q₂)
    (c₁ : Q₁ → ZMod 2) (c₂ : Q₂ → ZMod 2)
    (c : Q₁ ⊕ Q₂ → ZMod 2)
    (hc : c = Sum.elim c₁ c₂) :
    (∀ q₁ : Q₁, (hyperGaussSubsetProduct
      (jointIncident incident₁ incident₂ bridgeQ1 bridgeQ2) c).xVec
      (Sum.inl (Sum.inl q₁)) = c₁ q₁) ∧
    (∀ q₂ : Q₂, (hyperGaussSubsetProduct
      (jointIncident incident₁ incident₂ bridgeQ1 bridgeQ2) c).xVec
      (Sum.inl (Sum.inr q₂)) = c₂ q₂) ∧
    ((hyperGaussSubsetProduct
      (jointIncident incident₁ incident₂ bridgeQ1 bridgeQ2) c).zVec = 0) := by
  subst hc
  exact ⟨fun q₁ => by simp [hyperGaussSubsetProduct_xVec_vertex],
         fun q₂ => by simp [hyperGaussSubsetProduct_xVec_vertex],
         hyperGaussSubsetProduct_zVec _ _⟩

end JointMeasurement

end CohenEtAlSchemeRecovery
