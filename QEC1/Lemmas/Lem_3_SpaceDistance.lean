import QEC1.Lemmas.Lem_1_DeformedCodeChecks
import QEC1.Remarks.Rem_4_NotationCheegerConstant
import QEC1.Remarks.Rem_5_ExactnessOfSequences
import QEC1.Remarks.Rem_8_FreedomInDeformedChecks
import QEC1.Remarks.Rem_11_DesiderataForGraphG
import QEC1.Theorems.Thm_1_GaugingMeasurementCorrectness
import Mathlib.Tactic

/-!
# Lemma 3: Space Distance

## Statement
Let G be the graph used in the gauging measurement procedure for a logical operator L
in an [[n,k,d]] stabilizer code. Let d* denote the distance of the deformed code. Then:
  d* ≥ min(h(G), 1) · d
where h(G) is the Cheeger constant of G and d is the distance of the original code.

In particular, if h(G) ≥ 1, then d* ≥ d.

## Main Results
- `restrictToV` : restriction of a Pauli operator on V ⊕ E to V
- `gaussSubsetProduct_mem_stabilizerGroup` : gaussSubsetProduct is in deformed stabilizer group
- `edgeXSupport_in_ker_secondCoboundary` : edge X-support of logical is a cocycle (Step 2)
- `cleaned_restriction_logical_disjunction` : at least one cleaned restriction is a logical
- `construct_wlog` : derives WLOG cleaning vector from exactness + cocycle + Step 4 hypothesis
- `distance_ge_min_cheeger_one_mul_d` : d* ≥ min(h(G), 1) · d
- `deformed_distance_ge_d_sufficient_expansion` : if h(G) ≥ 1 then d* ≥ d

## Corollaries
- `deformed_distance_ge_min_cheeger_d` : d* ≥ min(h(G), 1) · d (at code distance level)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
noncomputable section

namespace SpaceDistance

open Finset PauliOp GaussFlux DeformedOperator DeformedCode DeformedCodeChecks
     DesiderataForGraphG GaugingMeasurementCorrectness FreedomInDeformedChecks QEC1

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-- Every element of ZMod 2 is either 0 or 1. -/
private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Any ZMod 2-valued function equals the indicator of its support finset. -/
private theorem zmod2_fun_eq_finsetIndicator (c : V → ZMod 2) :
    c = finsetIndicator (Finset.univ.filter (fun v => c v = 1)) := by
  ext v
  simp only [finsetIndicator, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hv : c v = 1
  · simp only [hv, ite_true]
  · simp only [hv, ite_false]
    rcases zmod2_cases (c v) with h | h
    · exact h
    · exact absurd h hv

/-! ## Step 1: Restriction to Vertex Qubits -/

/-- Restriction of a Pauli operator on V ⊕ E to vertex qubits V. -/
def restrictToV (P : PauliOp (ExtQubit G)) : PauliOp V where
  xVec := fun v => P.xVec (Sum.inl v)
  zVec := fun v => P.zVec (Sum.inl v)

@[simp]
theorem restrictToV_xVec (P : PauliOp (ExtQubit G)) (v : V) :
    (restrictToV G P).xVec v = P.xVec (Sum.inl v) := rfl

@[simp]
theorem restrictToV_zVec (P : PauliOp (ExtQubit G)) (v : V) :
    (restrictToV G P).zVec v = P.zVec (Sum.inl v) := rfl

@[simp]
theorem restrictToV_one : restrictToV G (1 : PauliOp (ExtQubit G)) = 1 := by
  ext v <;> simp [restrictToV]

@[simp]
theorem restrictToV_mul (P Q : PauliOp (ExtQubit G)) :
    restrictToV G (P * Q) = restrictToV G P * restrictToV G Q := by
  ext v <;> simp [restrictToV, PauliOp.mul_xVec, PauliOp.mul_zVec, Pi.add_apply]

/-! ## Step 2: Cleaning a Logical Operator -/

/-- The X-support vector of P on edge qubits. -/
def edgeXSupport (P : PauliOp (ExtQubit G)) : G.edgeSet → ZMod 2 :=
  fun e => P.xVec (Sum.inr e)

/-- The cleaned operator: L' multiplied by gaussSubsetProduct(c). -/
def cleanedOp (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2) :
    PauliOp (ExtQubit G) :=
  L' * gaussSubsetProduct G c

/-- The cleaned operator has X-vector on edges equal to original plus coboundary of c. -/
theorem cleanedOp_xVec_edge (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2)
    (e : G.edgeSet) :
    (cleanedOp G L' c).xVec (Sum.inr e) =
    L'.xVec (Sum.inr e) + GraphMaps.coboundaryMap G c e := by
  simp [cleanedOp, PauliOp.mul_xVec, Pi.add_apply]

/-- The cleaned operator has X-vector on vertices equal to original plus c. -/
theorem cleanedOp_xVec_vertex (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2)
    (v : V) :
    (cleanedOp G L' c).xVec (Sum.inl v) = L'.xVec (Sum.inl v) + c v := by
  simp [cleanedOp, PauliOp.mul_xVec, Pi.add_apply]

/-- The cleaned operator preserves Z-vector (gaussSubsetProduct is pure X). -/
theorem cleanedOp_zVec (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2) :
    (cleanedOp G L' c).zVec = L'.zVec := by
  ext q
  simp [cleanedOp, PauliOp.mul_zVec, Pi.add_apply]

/-- If coboundary of c equals the edge X-support of L', then cleaned op
    has zero X-support on edges. -/
theorem cleaned_has_no_xSupport_on_edges
    (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2)
    (hcob : ∀ e : G.edgeSet, GraphMaps.coboundaryMap G c e = L'.xVec (Sum.inr e)) :
    ∀ e : G.edgeSet, (cleanedOp G L' c).xVec (Sum.inr e) = 0 := by
  intro e
  rw [cleanedOp_xVec_edge, hcob e]
  exact CharTwo.add_self_eq_zero _

/-! ## Step 3: Cleaned operator restricted to V commutes with original checks -/

/-- The symplectic inner product of Lbar with a deformed check equals the symplectic
    inner product of Lbar|_V with the original check, when Lbar has no X on edges. -/
theorem symplecticInner_noXEdge_deformed
    (Lbar : PauliOp (ExtQubit G))
    (data : DeformedCodeData G checks)
    (hnoX : ∀ e : G.edgeSet, Lbar.xVec (Sum.inr e) = 0)
    (j : J) :
    symplecticInner Lbar (deformedOriginalChecks G checks data j) =
    symplecticInner (restrictToV G Lbar) (checks j) := by
  unfold symplecticInner
  rw [Fintype.sum_sum_type]
  have h_edge : ∑ e : G.edgeSet,
      (Lbar.xVec (Sum.inr e) *
       (deformedOriginalChecks G checks data j).zVec (Sum.inr e) +
       Lbar.zVec (Sum.inr e) *
       (deformedOriginalChecks G checks data j).xVec (Sum.inr e)) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    rw [hnoX e]
    simp [deformedOriginalChecks, deformedCheck, deformedOpExt]
  have h_vertex : ∑ v : V,
      (Lbar.xVec (Sum.inl v) *
       (deformedOriginalChecks G checks data j).zVec (Sum.inl v) +
       Lbar.zVec (Sum.inl v) *
       (deformedOriginalChecks G checks data j).xVec (Sum.inl v)) =
      ∑ v : V, ((restrictToV G Lbar).xVec v * (checks j).zVec v +
                 (restrictToV G Lbar).zVec v * (checks j).xVec v) := by
    apply Finset.sum_congr rfl; intro v _
    simp [restrictToV, deformedOriginalChecks, deformedCheck, deformedOpExt]
  rw [h_vertex, h_edge, add_zero]

/-- If Lbar commutes with deformed check s̃_j and has no X on edges,
    then Lbar|_V commutes with s_j. -/
theorem cleaned_commutes_with_original_check
    (Lbar : PauliOp (ExtQubit G))
    (data : DeformedCodeData G checks)
    (hnoX : ∀ e : G.edgeSet, Lbar.xVec (Sum.inr e) = 0)
    (j : J)
    (hcomm : PauliCommute Lbar (deformedOriginalChecks G checks data j)) :
    PauliCommute (restrictToV G Lbar) (checks j) := by
  unfold PauliCommute at hcomm ⊢
  rw [← symplecticInner_noXEdge_deformed G checks Lbar data hnoX j]
  exact hcomm

/-- If Lbar commutes with all deformed checks and has no X on edges,
    then Lbar|_V commutes with all original checks. -/
theorem cleaned_commutes_with_all_original_checks
    (Lbar : PauliOp (ExtQubit G))
    (data : DeformedCodeData G checks)
    (hnoX : ∀ e : G.edgeSet, Lbar.xVec (Sum.inr e) = 0)
    (hcomm_all : ∀ j : J, PauliCommute Lbar (deformedOriginalChecks G checks data j)) :
    ∀ j : J, PauliCommute (restrictToV G Lbar) (checks j) := by
  intro j
  exact cleaned_commutes_with_original_check G checks Lbar data hnoX j (hcomm_all j)

/-! ## Step 4: gaussSubsetProduct commutes with all deformed code checks -/

/-- A product of operators that each commute with R also commutes with R. -/
private theorem pauliCommute_prod_of_forall {Q : Type*} [Fintype Q] [DecidableEq Q]
    (S : Finset Q) (f : Q → PauliOp (ExtQubit G))
    (R : PauliOp (ExtQubit G))
    (h : ∀ v ∈ S, PauliCommute (f v) R) :
    PauliCommute (∏ v ∈ S, f v) R := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact PauliOp.pauliCommute_one_left R
  | insert a s hna ih =>
    rw [Finset.prod_insert hna]
    unfold PauliCommute at *
    rw [symplecticInner_mul_left]
    have h1 := h _ (Finset.mem_insert_self a s)
    have h2 := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    rw [h1, h2, add_zero]

/-- The gaussSubsetProduct commutes with deformed checks.
    Proof: gaussSubsetProduct(c) = ∏_{v : c v = 1} A_v, and each A_v commutes
    with the deformed check by the boundary condition. -/
theorem gaussSubsetProduct_comm_deformedCheck
    (data : DeformedCodeData G checks) (c : V → ZMod 2) (j : J) :
    PauliCommute (gaussSubsetProduct G c) (deformedOriginalChecks G checks data j) := by
  conv_lhs => rw [show (gaussSubsetProduct G c) =
    gaussSubsetProduct G (finsetIndicator (Finset.univ.filter (fun v => c v = 1))) from by
    congr 1; exact zmod2_fun_eq_finsetIndicator c]
  rw [← prod_gaussLawOp_eq_gaussSubsetProduct]
  exact pauliCommute_prod_of_forall G _ _ _ (fun v _ =>
    (PauliOp.pauliCommute_comm _ _).mp
      (deformedCheck_comm_gaussLaw G (checks j) (data.edgePath j) (data.boundary_condition j) v))

/-- The gaussSubsetProduct commutes with gaussLaw checks (both pure X). -/
theorem gaussSubsetProduct_comm_gaussLaw (c : V → ZMod 2) (v : V) :
    PauliCommute (gaussSubsetProduct G c) (gaussLawChecks G v) := by
  unfold PauliCommute symplecticInner
  rw [Fintype.sum_sum_type]
  have h_edge : ∑ e : G.edgeSet,
      ((gaussSubsetProduct G c).xVec (Sum.inr e) *
       (gaussLawChecks G v).zVec (Sum.inr e) +
       (gaussSubsetProduct G c).zVec (Sum.inr e) *
       (gaussLawChecks G v).xVec (Sum.inr e)) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    have hz1 : (gaussSubsetProduct G c).zVec (Sum.inr e) = 0 := by simp [gaussSubsetProduct]
    have hz2 : (gaussLawChecks G v).zVec (Sum.inr e) = 0 := by
      simp [gaussLawChecks, gaussLawOp]
    rw [hz1, hz2]; ring
  have h_vertex : ∑ w : V,
      ((gaussSubsetProduct G c).xVec (Sum.inl w) *
       (gaussLawChecks G v).zVec (Sum.inl w) +
       (gaussSubsetProduct G c).zVec (Sum.inl w) *
       (gaussLawChecks G v).xVec (Sum.inl w)) = 0 := by
    apply Finset.sum_eq_zero; intro w _
    have hz : (gaussSubsetProduct G c).zVec (Sum.inl w) = 0 := by simp [gaussSubsetProduct]
    have hz2 : (gaussLawChecks G v).zVec (Sum.inl w) = 0 := by
      simp [gaussLawChecks, gaussLawOp]
    rw [hz, hz2]; ring
  rw [h_vertex, h_edge, add_zero]

/-- The gaussSubsetProduct commutes with flux checks. -/
theorem gaussSubsetProduct_comm_flux
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (c : V → ZMod 2) (p : C) :
    PauliCommute (gaussSubsetProduct G c) (fluxChecks G cycles p) := by
  conv_lhs => rw [show (gaussSubsetProduct G c) =
    gaussSubsetProduct G (finsetIndicator (Finset.univ.filter (fun v => c v = 1))) from by
    congr 1; exact zmod2_fun_eq_finsetIndicator c]
  rw [← prod_gaussLawOp_eq_gaussSubsetProduct]
  exact pauliCommute_prod_of_forall G _ _ _ (fun v _ =>
    allChecks_pairwise_commute_gaussLaw_flux G cycles hcyc v p)

/-- The gaussSubsetProduct commutes with all checks of the deformed code. -/
theorem gaussSubsetProduct_comm_allChecks
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (c : V → ZMod 2) (a : CheckIndex V C J) :
    PauliCommute (gaussSubsetProduct G c)
      (deformedCodeChecks G cycles checks data a) := by
  cases a with
  | gaussLaw v => exact gaussSubsetProduct_comm_gaussLaw G c v
  | flux p => exact gaussSubsetProduct_comm_flux G cycles hcyc c p
  | deformed j => exact gaussSubsetProduct_comm_deformedCheck G checks data c j

/-- gaussSubsetProduct is in the centralizer of the deformed code. -/
theorem gaussSubsetProduct_inCentralizer
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (c : V → ZMod 2) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer
      (gaussSubsetProduct G c) := by
  intro a
  exact gaussSubsetProduct_comm_allChecks G cycles checks data hcyc c a

/-! ## gaussSubsetProduct is in the Stabilizer Group -/

/-- **gaussSubsetProduct is in the stabilizer group of the deformed code.**
    This follows because gaussSubsetProduct(c) = ∏_{v : c v = 1} A_v,
    and each A_v is a check of the deformed code. -/
theorem gaussSubsetProduct_mem_stabilizerGroup
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (c : V → ZMod 2) :
    gaussSubsetProduct G c ∈
      (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
  rw [show gaussSubsetProduct G c =
    gaussSubsetProduct G (finsetIndicator (Finset.univ.filter (fun v => c v = 1))) from by
    congr 1; exact zmod2_fun_eq_finsetIndicator c]
  rw [← prod_gaussLawOp_eq_gaussSubsetProduct]
  apply Subgroup.prod_mem
  intro v _
  exact gaussLaw_mem_stabilizerGroup G cycles checks data hcyc hcomm v

/-! ## Weight Decomposition -/

/-- Weight of a Pauli on V ⊕ E decomposes as vertex + edge contributions. -/
theorem weight_eq_vertex_plus_edge (P : PauliOp (ExtQubit G)) :
    P.weight =
    (Finset.univ.filter (fun v : V =>
      P.xVec (Sum.inl v) ≠ 0 ∨ P.zVec (Sum.inl v) ≠ 0)).card +
    (Finset.univ.filter (fun e : G.edgeSet =>
      P.xVec (Sum.inr e) ≠ 0 ∨ P.zVec (Sum.inr e) ≠ 0)).card := by
  unfold PauliOp.weight PauliOp.support
  have h1 : (Finset.univ (α := ExtQubit G)).filter
      (fun q => P.xVec q ≠ 0 ∨ P.zVec q ≠ 0) =
    ((Finset.univ (α := V)).filter (fun v => P.xVec (Sum.inl v) ≠ 0 ∨ P.zVec (Sum.inl v) ≠ 0)).map
      ⟨Sum.inl, Sum.inl_injective⟩ ∪
    ((Finset.univ (α := G.edgeSet)).filter (fun e => P.xVec (Sum.inr e) ≠ 0 ∨ P.zVec (Sum.inr e) ≠ 0)).map
      ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hp
      cases q with
      | inl v => left; exact ⟨v, hp, rfl⟩
      | inr e => right; exact ⟨e, hp, rfl⟩
    · rintro (⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩) <;> exact ‹_›
  have h2 : Disjoint
    ((Finset.univ.filter (fun v : V => P.xVec (Sum.inl v) ≠ 0 ∨ P.zVec (Sum.inl v) ≠ 0)).map
      ⟨Sum.inl, Sum.inl_injective⟩)
    ((Finset.univ.filter (fun e : G.edgeSet => P.xVec (Sum.inr e) ≠ 0 ∨ P.zVec (Sum.inr e) ≠ 0)).map
      ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
               Function.Embedding.coeFn_mk] at hq1 hq2
    obtain ⟨_, _, rfl⟩ := hq1
    obtain ⟨_, _, habs⟩ := hq2
    exact absurd habs (by simp)
  rw [h1, Finset.card_union_of_disjoint h2, Finset.card_map, Finset.card_map]

/-- The weight of P on V ⊕ E equals the weight of its restriction plus edge support. -/
theorem weight_decomposition (P : PauliOp (ExtQubit G)) :
    P.weight =
    (restrictToV G P).weight +
    (Finset.univ.filter (fun e : G.edgeSet =>
      P.xVec (Sum.inr e) ≠ 0 ∨ P.zVec (Sum.inr e) ≠ 0)).card := by
  rw [weight_eq_vertex_plus_edge]
  congr 1

/-! ## Step 4 (Paper): Restriction to original qubits is a logical of the original code

The key insight: the two cleaned operators (with c and c + 1) differ by the logical L
on vertices. If both restrictions were in the original stabilizer group, their product
(= L|_V) would be too, contradicting L being a logical of the original code. -/

/-- The restriction of the logical operator L to V is the all-X operator. -/
theorem restrictToV_logicalOp :
    restrictToV G (logicalOp G) = logicalOpV (V := V) := by
  ext v <;> simp [restrictToV, logicalOp, logicalOpV]

/-- The two cleaned operators (with c and c + allOnes) differ by L on the extended system. -/
theorem cleanedOp_complement_eq_mul_logical (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2) :
    cleanedOp G L' (c + fun _ => 1) = cleanedOp G L' c * logicalOp G := by
  simp only [cleanedOp]
  rw [gaussSubsetProduct_add, ← mul_assoc,
      show gaussSubsetProduct G (fun _ => (1 : ZMod 2)) = logicalOp G from
        gaussSubsetProduct_allOnes G]

/-- The restrictions of the two cleaned operators differ by logicalOpV. -/
theorem restrictToV_cleanedOp_complement (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2) :
    restrictToV G (cleanedOp G L' (c + fun _ => 1)) =
    restrictToV G (cleanedOp G L' c) * logicalOpV (V := V) := by
  rw [cleanedOp_complement_eq_mul_logical, restrictToV_mul, restrictToV_logicalOp]

/-- If L' is a logical of the deformed code and gaussSubsetProduct(c) is a stabilizer,
    then cleanedOp = L' * gaussSubsetProduct(c) is not in the deformed stabilizer group. -/
theorem cleanedOp_not_in_stabilizerGroup
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (c : V → ZMod 2) :
    cleanedOp G L' c ∉
      (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
  intro hmem
  have hg := gaussSubsetProduct_mem_stabilizerGroup G cycles checks data hcyc hcomm c
  have : L' ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
    have : L' = cleanedOp G L' c * (gaussSubsetProduct G c)⁻¹ := by
      simp [cleanedOp, mul_assoc, PauliOp.mul_self]
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hg)
  exact hlog.2.1 this

/-- If L' is a logical of the deformed code, then cleanedOp is not identity. -/
theorem cleanedOp_ne_one
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (c : V → ZMod 2) :
    cleanedOp G L' c ≠ 1 := by
  intro h
  have hL : L' = gaussSubsetProduct G c := by
    have h1 : L' * gaussSubsetProduct G c = 1 := h
    have h2 := congr_arg (· * gaussSubsetProduct G c) h1
    simp only [PauliOp.mul_assoc, PauliOp.mul_self, PauliOp.mul_one, PauliOp.one_mul] at h2
    exact h2
  have : L' ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
    rw [hL]
    exact gaussSubsetProduct_mem_stabilizerGroup G cycles checks data hcyc hcomm c
  exact hlog.2.1 this

/-- The cleaned operator is a logical of the deformed code. -/
theorem cleanedOp_isLogical
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (c : V → ZMod 2) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp (cleanedOp G L' c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    unfold PauliCommute at *
    simp only [cleanedOp]
    rw [symplecticInner_mul_left]
    have h1 := hlog.1 a
    have h2 := (gaussSubsetProduct_inCentralizer G cycles checks data hcyc hcomm c) a
    unfold PauliCommute at h1 h2
    rw [h1, h2, add_zero]
  · exact cleanedOp_not_in_stabilizerGroup G cycles checks data hcyc hcomm L' hlog c
  · exact cleanedOp_ne_one G cycles checks data hcyc hcomm L' hlog c

/-- **Key theorem (Step 4): At least one of the two cleaned restrictions is a logical
    of the original code.** -/
theorem cleaned_restriction_logical_disjunction
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (c : V → ZMod 2)
    (hc : GraphMaps.coboundaryMap G c = edgeXSupport G L') :
    origCode.isLogicalOp (restrictToV G (cleanedOp G L' c)) ∨
    origCode.isLogicalOp (restrictToV G (cleanedOp G L' (c + fun _ => 1))) := by
  -- Both cleaned operators have no X on edges
  have hnoX : ∀ e, (cleanedOp G L' c).xVec (Sum.inr e) = 0 := by
    exact cleaned_has_no_xSupport_on_edges G L' c (fun e => by rw [hc]; rfl)
  have h_delta_one : GraphMaps.coboundaryMap G (fun _ : V => (1 : ZMod 2)) = 0 := by
    have h := GraphMaps.allOnes_mem_ker_coboundary G
    rw [LinearMap.mem_ker] at h
    have : (fun _ : V => (1 : ZMod 2)) = GraphMaps.allOnes (V := V) := by
      ext v; simp [GraphMaps.allOnes]
    rw [this]; exact h
  have hnoX' : ∀ e, (cleanedOp G L' (c + fun _ => 1)).xVec (Sum.inr e) = 0 := by
    exact cleaned_has_no_xSupport_on_edges G L' (c + fun _ => 1) (fun e => by
      rw [map_add, hc, h_delta_one, add_zero]; rfl)
  -- Both restrictions are in the centralizer of the original code
  have hcent₁ : origCode.inCentralizer (restrictToV G (cleanedOp G L' c)) := by
    intro i
    have hlog_clean := cleanedOp_isLogical G cycles checks data hcyc hcomm L' hlog c
    have hcomm_deformed := hlog_clean.1 (.deformed (hJ ▸ i))
    simp only [deformedCodeChecks_deformed] at hcomm_deformed
    have h_comm_check := cleaned_commutes_with_original_check G checks _ data hnoX (hJ ▸ i) hcomm_deformed
    have : origCode.check i = checks (hJ ▸ i) := by
      have := hchecks_eq (hJ ▸ i); subst hJ; simpa using this
    rw [this]; exact h_comm_check
  have hcent₂ : origCode.inCentralizer (restrictToV G (cleanedOp G L' (c + fun _ => 1))) := by
    intro i
    have hlog_clean := cleanedOp_isLogical G cycles checks data hcyc hcomm L' hlog (c + fun _ => 1)
    have hcomm_deformed := hlog_clean.1 (.deformed (hJ ▸ i))
    simp only [deformedCodeChecks_deformed] at hcomm_deformed
    have h_comm_check := cleaned_commutes_with_original_check G checks _ data hnoX' (hJ ▸ i) hcomm_deformed
    have : origCode.check i = checks (hJ ▸ i) := by
      have := hchecks_eq (hJ ▸ i); subst hJ; simpa using this
    rw [this]; exact h_comm_check
  -- The two restrictions differ by logicalOpV
  have hdiff := restrictToV_cleanedOp_complement G L' c
  -- Suppose for contradiction that neither is a logical
  by_contra h_neither
  push_neg at h_neither
  obtain ⟨h1, h2⟩ := h_neither
  -- Not logical + in centralizer → in stabilizerGroup or identity
  -- isLogicalOp P = inCentralizer P ∧ P ∉ stabilizerGroup ∧ P ≠ 1
  -- ¬isLogicalOp + inCentralizer → P ∈ stabilizerGroup ∨ P = 1
  have h1' : restrictToV G (cleanedOp G L' c) ∈ origCode.stabilizerGroup ∨
      restrictToV G (cleanedOp G L' c) = 1 := by
    by_contra h_contra
    push_neg at h_contra
    exact h1 ⟨hcent₁, h_contra.1, h_contra.2⟩
  have h2' : restrictToV G (cleanedOp G L' (c + fun _ => 1)) ∈ origCode.stabilizerGroup ∨
      restrictToV G (cleanedOp G L' (c + fun _ => 1)) = 1 := by
    by_contra h_contra
    push_neg at h_contra
    exact h2 ⟨hcent₂, h_contra.1, h_contra.2⟩
  -- In all cases, show logicalOpV is in stabilizer group or is identity → contradiction
  have : logicalOpV (V := V) ∈ origCode.stabilizerGroup ∨ logicalOpV (V := V) = 1 := by
    rcases h1', h2' with ⟨h1s | h1e, h2s | h2e⟩
    · -- Both in stabilizer group. Their quotient = logicalOpV is in stabGroup.
      left
      have hprod : restrictToV G (cleanedOp G L' c) * logicalOpV (V := V) =
          restrictToV G (cleanedOp G L' (c + fun _ => 1)) := hdiff.symm
      have hL : logicalOpV (V := V) =
          (restrictToV G (cleanedOp G L' c))⁻¹ *
          (restrictToV G (cleanedOp G L' c) * logicalOpV (V := V)) := by
        rw [← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul]
      rw [hL, hprod]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1s) h2s
    · -- c restriction in stabGroup, c+1 restriction = 1
      left
      have hmul1 : restrictToV G (cleanedOp G L' c) * logicalOpV (V := V) = 1 := by
        rw [← hdiff]; exact h2e
      have hlog_eq : logicalOpV (V := V) = restrictToV G (cleanedOp G L' c) := by
        have : logicalOpV (V := V) =
            (restrictToV G (cleanedOp G L' c))⁻¹ := mul_eq_one_iff_eq_inv'.mp hmul1
        rw [this, PauliOp.inv_eq_self]
      rw [hlog_eq]; exact h1s
    · -- c restriction = 1, c+1 restriction in stabGroup
      left
      rw [h1e, _root_.one_mul] at hdiff
      rw [← hdiff]; exact h2s
    · -- Both = 1. Then logicalOpV = 1.
      right
      rw [h1e, _root_.one_mul] at hdiff
      rw [← hdiff]; exact h2e
  rcases this with hstab | hone
  · exact hL_logical.2.1 hstab
  · exact hL_logical.2.2 hone

/-! ## Step 2: Edge X-support is a cocycle

The edge X-support of a logical operator L' of the deformed code lies in
ker(δ₂), i.e., it is a 1-cocycle. This follows because L' commutes with all
flux checks B_p, and the symplectic inner product ⟨L', B_p⟩ equals δ₂(edgeXSupport(L'))(p). -/

/-- The symplectic inner product of L' with a flux check equals the second coboundary
    of the edge X-support applied to that cycle. -/
theorem symplecticInner_flux_eq_secondCoboundary
    (L' : PauliOp (ExtQubit G)) (p : C) :
    symplecticInner L' (fluxChecks G cycles p) =
    GraphMaps.secondCoboundaryMap G cycles (edgeXSupport G L') p := by
  unfold symplecticInner
  rw [Fintype.sum_sum_type]
  have h_vertex : ∑ v : V,
      (L'.xVec (Sum.inl v) * (fluxChecks G cycles p).zVec (Sum.inl v) +
       L'.zVec (Sum.inl v) * (fluxChecks G cycles p).xVec (Sum.inl v)) = 0 := by
    apply Finset.sum_eq_zero; intro v _
    simp [fluxChecks, fluxOp]
  rw [h_vertex, zero_add]
  simp only [GraphMaps.secondCoboundaryMap_apply, edgeXSupport]
  apply Finset.sum_congr rfl; intro e _
  simp only [fluxChecks, fluxOp]
  split
  · simp
  · rename_i hne
    simp [hne]

/-- **Step 2 (Paper): The edge X-support of a logical operator of the deformed code
    is a cocycle (lies in ker δ₂).** This follows from L' commuting with all flux checks. -/
theorem edgeXSupport_in_ker_secondCoboundary
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L') :
    edgeXSupport G L' ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) := by
  rw [LinearMap.mem_ker]
  ext p
  have hcomm_flux := hlog.1 (.flux p)
  change PauliCommute L' (deformedCodeChecks G cycles checks data (.flux p)) at hcomm_flux
  rw [deformedCodeChecks_flux] at hcomm_flux
  unfold PauliCommute at hcomm_flux
  rw [symplecticInner_flux_eq_secondCoboundary] at hcomm_flux
  simp only [Pi.zero_apply]
  exact hcomm_flux

/-! ## Coboundary Support equals Edge Boundary -/

/-- The coboundary support of c (edges where δc ≠ 0) has the same cardinality as the
    edge boundary of the support of c. -/
theorem coboundary_support_card_eq_edgeBoundary_card
    (c : V → ZMod 2) :
    (Finset.univ.filter (fun e : G.edgeSet =>
      GraphMaps.coboundaryMap G c e ≠ 0)).card =
    (QEC1.SimpleGraph.edgeBoundary G
      (Finset.univ.filter (fun v : V => c v ≠ 0))).card := by
  set S := Finset.univ.filter (fun v : V => c v ≠ 0) with hS_def
  set cobSupp := Finset.univ.filter (fun e : G.edgeSet =>
    GraphMaps.coboundaryMap G c e ≠ 0) with hcobSupp_def
  set bdry := QEC1.SimpleGraph.edgeBoundary G S with hbdry_def
  suffices h : bdry = cobSupp.map ⟨Subtype.val, Subtype.val_injective⟩ by
    rw [h, Finset.card_map]
  ext e_val
  simp only [hbdry_def, hcobSupp_def, QEC1.SimpleGraph.edgeBoundary, Finset.mem_filter,
    SimpleGraph.mem_edgeFinset, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨he_mem, hcard⟩
    refine ⟨⟨e_val, he_mem⟩, ?_, rfl⟩
    intro h_zero
    revert h_zero hcard
    have he := he_mem
    induction e_val using Sym2.ind with
    | _ a b =>
      simp only [GraphMaps.coboundaryMap_apply, Sym2.lift_mk]
      intro hcard_inter hcab_zero
      have hab : a ≠ b := by
        intro h; subst h; exact G.loopless a (by rwa [SimpleGraph.mem_edgeSet] at he)
      have hca_eq_cb : c a = c b := by
        have h1 : c a = -(c b) := add_eq_zero_iff_eq_neg.mp hcab_zero
        have h2 : -(c b) = c b := by generalize c b = x; fin_cases x <;> simp
        rw [h2] at h1; exact h1
      by_cases hca : c a ≠ 0
      · have hcb : c b ≠ 0 := hca_eq_cb ▸ hca
        have hinter : (s(a, b)).toFinset ∩ S = (s(a, b)).toFinset := by
          ext v; simp only [Finset.mem_inter, Sym2.mem_toFinset, Sym2.mem_iff, hS_def,
            Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact fun ⟨h, _⟩ => h
          · intro hv; exact ⟨hv, by rcases hv with rfl | rfl <;> assumption⟩
        rw [hinter] at hcard_inter
        have : (s(a, b)).toFinset.card = 2 :=
          Sym2.card_toFinset_of_not_isDiag _
            (SimpleGraph.not_isDiag_of_mem_edgeSet G
              (by rwa [SimpleGraph.mem_edgeSet] at he))
        omega
      · push_neg at hca
        have hcb : c b = 0 := by rwa [← hca_eq_cb]
        have hinter : (s(a, b)).toFinset ∩ S = ∅ := by
          ext v; simp only [Finset.mem_inter, Sym2.mem_toFinset, Sym2.mem_iff, hS_def,
            Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            not_and]
          intro hv; rcases hv with rfl | rfl
          · exact fun h => absurd h (not_not.mpr hca)
          · exact fun h => absurd h (not_not.mpr hcb)
        rw [hinter, Finset.card_empty] at hcard_inter
        omega
  · rintro ⟨⟨e_val', he'⟩, hmem, rfl⟩
    refine ⟨he', ?_⟩
    have he := he'
    induction e_val' using Sym2.ind with
    | _ a b =>
      simp only [GraphMaps.coboundaryMap_apply, Sym2.lift_mk] at hmem
      have hab : a ≠ b := by
        intro h; subst h; exact G.loopless a (by rwa [SimpleGraph.mem_edgeSet] at he)
      have hca_ne_cb : c a ≠ c b := by
        intro h; apply hmem; rw [h]
        generalize c b = x; fin_cases x <;> decide
      -- Exactly one of c a, c b is nonzero
      rcases zmod2_cases (c a), zmod2_cases (c b) with ⟨ha | ha, hb | hb⟩
      · exact absurd (ha ▸ hb ▸ rfl : c a = c b) hca_ne_cb
      · -- c a = 0, c b = 1: only b is in S
        have : (s(a, b)).toFinset ∩ S = {b} := by
          ext v; simp only [Finset.mem_inter, Sym2.mem_toFinset, Sym2.mem_iff, hS_def,
            Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hv, hcv⟩
            rcases hv with rfl | rfl
            · exfalso; rw [ha] at hcv; exact hcv rfl
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, by rw [hb]; exact one_ne_zero⟩
        rw [this, Finset.card_singleton]
      · -- c a = 1, c b = 0: only a is in S
        have : (s(a, b)).toFinset ∩ S = {a} := by
          ext v; simp only [Finset.mem_inter, Sym2.mem_toFinset, Sym2.mem_iff, hS_def,
            Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hv, hcv⟩
            rcases hv with rfl | rfl
            · rfl
            · exfalso; rw [hb] at hcv; exact hcv rfl
          · rintro rfl; exact ⟨Or.inl rfl, by rw [ha]; exact one_ne_zero⟩
        rw [this, Finset.card_singleton]
      · exact absurd (ha ▸ hb ▸ rfl : c a = c b) hca_ne_cb

/-- The edge support of L' is at least the coboundary support of c₀. -/
theorem edge_support_ge_coboundary_support
    (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2)
    (hc : GraphMaps.coboundaryMap G c = edgeXSupport G L') :
    (Finset.univ.filter (fun e : G.edgeSet =>
      GraphMaps.coboundaryMap G c e ≠ 0)).card ≤
    (Finset.univ.filter (fun e : G.edgeSet =>
      L'.xVec (Sum.inr e) ≠ 0 ∨ L'.zVec (Sum.inr e) ≠ 0)).card := by
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  left
  rwa [hc] at he

/-- The supports of c and c+1 partition V: |supp(c)| + |supp(c+1)| = |V|. -/
theorem support_add_complement_card (c : V → ZMod 2) :
    (Finset.univ.filter (fun v : V => c v ≠ 0)).card +
    (Finset.univ.filter (fun v : V => c v + 1 ≠ 0)).card =
    Fintype.card V := by
  have h : (Finset.univ.filter (fun v : V => c v + 1 ≠ 0)) =
      (Finset.univ.filter (fun v : V => c v ≠ 0))ᶜ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
      Finset.mem_compl, not_not]
    constructor
    · intro hv
      rcases zmod2_cases (c v) with h | h
      · exact h
      · exfalso; apply hv; rw [h]; decide
    · intro hv
      rw [hv]; decide
  rw [h, Finset.card_add_card_compl]

/-- The coboundary of c and c+1 are the same (since δ(1) = 0). -/
theorem coboundary_add_ones_eq
    (c : V → ZMod 2) :
    GraphMaps.coboundaryMap G (c + fun _ => 1) = GraphMaps.coboundaryMap G c := by
  rw [map_add]
  have h := GraphMaps.allOnes_mem_ker_coboundary G
  rw [LinearMap.mem_ker] at h
  have : GraphMaps.coboundaryMap G (fun _ : V => (1 : ZMod 2)) = 0 := by
    have : (fun _ : V => (1 : ZMod 2)) = GraphMaps.allOnes (V := V) := by
      ext v; simp [GraphMaps.allOnes]
    rw [this]; exact h
  rw [this, add_zero]

/-! ## Step 4 (Paper): Any cleaning gives a logical of the original code

The key structural argument: given boundary exactness (ker(∂) = im(∂₂)), we show
that for ANY cleaning vector c with δc = edgeXSupport(L'), the restriction
restrictToV(cleanedOp(L', c)) is a logical of the original code.

The proof proceeds by contradiction:
- Case (b): If the restriction is identity on V, the cleaned operator is a pure-Z
  edge operator. Its Z-support on edges lies in ker(∂), hence in im(∂₂) by boundary
  exactness, making it a product of flux operators ∈ stabilizer group. Contradiction.
- Case (a): If the restriction is in origCode.stabilizerGroup, we lift it to a
  deformed stabilizer using closure induction. The quotient is again a pure-Z edge
  operator in the centralizer, and the same argument applies. Contradiction. -/

/-- The restriction of a deformed original check to V equals the original check. -/
theorem restrictToV_deformedOriginalCheck (data : DeformedCodeData G checks) (j : J) :
    restrictToV G (deformedOriginalChecks G checks data j) = checks j := by
  ext v <;> simp [restrictToV, deformedOriginalChecks, deformedCheck, deformedOpExt]

/-- The restriction of a flux check to V is identity. -/
theorem restrictToV_fluxChecks (p : C) :
    restrictToV G (fluxChecks G cycles p) = 1 := by
  ext v <;> simp [restrictToV, fluxChecks, fluxOp]

/-- The restriction of a gaussLaw check to V has X at v and no Z. -/
theorem restrictToV_gaussLawChecks_xVec (w v : V) :
    (restrictToV G (gaussLawChecks G v)).xVec w = if w = v then 1 else 0 := by
  simp [restrictToV, gaussLawChecks, gaussLawOp]

theorem restrictToV_gaussLawChecks_zVec (w v : V) :
    (restrictToV G (gaussLawChecks G v)).zVec w = 0 := by
  simp [restrictToV, gaussLawChecks, gaussLawOp]

/-- Multiplication of pure-Z edge operators adds their edge vectors. -/
theorem pureZEdgeOp_mul (δ₁ δ₂ : G.edgeSet → ZMod 2) :
    pureZEdgeOp G δ₁ * pureZEdgeOp G δ₂ = pureZEdgeOp G (δ₁ + δ₂) := by
  unfold pureZEdgeOp
  rw [deformedOpExt_mul]
  congr 1

/-- The pure-Z edge operator for a single cycle indicator equals the flux check. -/
theorem pureZEdgeOp_single_cycle_eq_fluxChecks (c : C) :
    pureZEdgeOp G (fun e => if e ∈ cycles c then 1 else 0) = fluxChecks G cycles c := by
  ext q <;> cases q with
  | inl v => simp [pureZEdgeOp, deformedOpExt, fluxChecks, fluxOp]
  | inr e => simp [pureZEdgeOp, deformedOpExt, fluxChecks, fluxOp]

/-- An operator equal to a pure-Z edge operator with δ = 0 is identity. -/
@[simp]
theorem pureZEdgeOp_zero : pureZEdgeOp G (0 : G.edgeSet → ZMod 2) = 1 := by
  ext q <;> cases q with
  | inl v => simp [pureZEdgeOp, deformedOpExt]
  | inr e => simp [pureZEdgeOp, deformedOpExt]

/-- If δ is in the image of ∂₂, then pureZEdgeOp(δ) is a product of flux checks,
    hence in the deformed stabilizer group. -/
theorem pureZEdgeOp_mem_stabilizerGroup_of_range
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (δ : G.edgeSet → ZMod 2)
    (hδ : δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles)) :
    pureZEdgeOp G δ ∈
      (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
  rw [LinearMap.mem_range] at hδ
  obtain ⟨σ, rfl⟩ := hδ
  -- Decompose: pureZEdgeOp(∂₂(σ)) = ∏_{c : σ c ≠ 0} fluxChecks c
  -- We prove this by induction on the support of σ
  suffices h : ∀ (S : Finset C),
      (∀ c, σ c ≠ 0 → c ∈ S) →
      pureZEdgeOp G (GraphMaps.secondBoundaryMap G cycles σ) ∈
        (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup by
    exact h Finset.univ (fun c _ => Finset.mem_univ c)
  -- We prove by converting σ to a sum of Pi.single terms
  -- First show: secondBoundaryMap σ = ∑_c σ_c • secondBoundaryMap (Pi.single c 1)
  have hdecomp : GraphMaps.secondBoundaryMap G cycles σ =
      ∑ c : C, σ c • GraphMaps.secondBoundaryMap G cycles (Pi.single c 1) := by
    have : σ = ∑ c : C, σ c • Pi.single c 1 := by
      ext c'; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
    conv_lhs => rw [this, map_sum]
    congr 1; ext c; rw [LinearMap.map_smul]
  -- In ZMod 2, σ c • x = if σ c = 1 then x else 0
  -- So the sum is over {c | σ c = 1}
  -- We use Subgroup.prod_mem
  intro S _
  -- Show pureZEdgeOp of a sum equals product of pureZEdgeOps
  -- Key: In ZMod 2, every nonzero element is 1, so σ c • x = σ c * x
  -- pureZEdgeOp(Σ δᵢ) = ∏ pureZEdgeOp(δᵢ) (by pureZEdgeOp_mul repeatedly)
  -- We'll prove it via the product over all c
  have hprod : pureZEdgeOp G (GraphMaps.secondBoundaryMap G cycles σ) =
      ∏ c ∈ Finset.univ.filter (fun c => σ c ≠ 0),
        fluxChecks G cycles c := by
    -- Each secondBoundaryMap (Pi.single c 1) = indicator of cycle c
    have hsingle : ∀ c : C, GraphMaps.secondBoundaryMap G cycles (Pi.single c 1) =
        fun e => if e ∈ cycles c then 1 else 0 := by
      intro c; ext e
      simp only [GraphMaps.secondBoundaryMap_apply, Pi.single_apply]
      rw [show (∑ x : C, if e ∈ cycles x then if x = c then (1 : ZMod 2) else 0 else 0) =
          ∑ x : C, if x = c then (if e ∈ cycles x then 1 else 0) else 0 from by
        apply Finset.sum_congr rfl; intro x _; split <;> split <;> simp_all]
      simp [Finset.sum_ite_eq']
    -- In ZMod 2, the sum ∑_{c : σ c ≠ 0} 1_c equals the sum over the support
    rw [hdecomp]
    -- Replace σ c • ... with the ZMod 2 version
    have hsum_eq : (∑ c : C, σ c • GraphMaps.secondBoundaryMap G cycles (Pi.single c 1)) =
        ∑ c ∈ Finset.univ.filter (fun c => σ c ≠ 0),
          (fun e => if e ∈ cycles c then (1 : ZMod 2) else 0) := by
      -- Split the univ sum into filter + complement
      have key : ∀ c : C, σ c • GraphMaps.secondBoundaryMap G cycles (Pi.single c 1) =
          if σ c ≠ 0 then (fun e => if e ∈ cycles c then (1 : ZMod 2) else 0) else 0 := by
        intro c
        rcases zmod2_cases (σ c) with h | h
        · simp [h]
        · simp [h, hsingle, one_ne_zero]
      simp_rw [key]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [hsum_eq]
    -- Now show: pureZEdgeOp of a finset sum = product of pureZEdgeOps
    -- and each pureZEdgeOp(1_c) = fluxChecks c
    induction (Finset.univ.filter (fun c => σ c ≠ 0)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [← ih]
      rw [← pureZEdgeOp_mul]
      rw [pureZEdgeOp_single_cycle_eq_fluxChecks]
  rw [hprod]
  apply Subgroup.prod_mem
  intro c _
  exact flux_mem_stabilizerGroup G cycles checks data hcyc hcomm c

/-- If Lbar is a logical of the deformed code, has no X on edges, and restrictToV(Lbar) = 1,
    then with boundary exactness, Lbar is in the deformed stabilizer group (contradiction). -/
theorem cleaned_not_identity_on_V
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (c : V → ZMod 2)
    (hc : GraphMaps.coboundaryMap G c = edgeXSupport G L')
    (hrestrict : restrictToV G (cleanedOp G L' c) = 1) :
    False := by
  -- The cleaned operator Lbar has no X on edges
  set Lbar := cleanedOp G L' c
  have hnoX : ∀ e, Lbar.xVec (Sum.inr e) = 0 :=
    cleaned_has_no_xSupport_on_edges G L' c (fun e => by rw [hc]; rfl)
  -- Since restrictToV = 1, Lbar is identity on V
  have hxV : ∀ v, Lbar.xVec (Sum.inl v) = 0 := by
    intro v; have h := congr_arg (·.xVec v) hrestrict; simpa [restrictToV] using h
  have hzV : ∀ v, Lbar.zVec (Sum.inl v) = 0 := by
    intro v; have h := congr_arg (·.zVec v) hrestrict; simpa [restrictToV] using h
  -- So Lbar = pureZEdgeOp(δ) where δ e = Lbar.zVec (Sum.inr e)
  set δ := fun e : G.edgeSet => Lbar.zVec (Sum.inr e)
  have hLbar_eq : Lbar = pureZEdgeOp G δ := by
    ext q
    · -- xVec
      cases q with
      | inl v => simp [pureZEdgeOp, deformedOpExt, hxV v]
      | inr e => simp [pureZEdgeOp, deformedOpExt, hnoX e]
    · -- zVec
      cases q with
      | inl v => simp [pureZEdgeOp, deformedOpExt, hzV v]
      | inr e => rfl
  -- Lbar is a logical of the deformed code
  have hlog_Lbar := cleanedOp_isLogical G cycles checks data hcyc hcomm L' hlog c
  -- Lbar commutes with all gaussLaw checks, so ∂(δ) = 0
  have hδ_ker : δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) := by
    rw [LinearMap.mem_ker]; ext v
    simp only [Pi.zero_apply]
    -- Use the fact that Lbar commutes with gaussLawChecks G v
    have hcomm_gauss := hlog_Lbar.1 (.gaussLaw v)
    change PauliCommute Lbar (deformedCodeChecks G cycles checks data (.gaussLaw v)) at hcomm_gauss
    rw [deformedCodeChecks_gaussLaw] at hcomm_gauss
    unfold PauliCommute symplecticInner at hcomm_gauss
    rw [Fintype.sum_sum_type] at hcomm_gauss
    -- The vertex sum is 0 (both Lbar and gaussLaw are known on vertices)
    have h_vertex : ∑ w : V,
        (Lbar.xVec (Sum.inl w) * (gaussLawChecks G v).zVec (Sum.inl w) +
         Lbar.zVec (Sum.inl w) * (gaussLawChecks G v).xVec (Sum.inl w)) = 0 := by
      apply Finset.sum_eq_zero; intro w _
      rw [hxV w, hzV w]; ring
    rw [h_vertex, zero_add] at hcomm_gauss
    -- The edge sum: Σ_e [Lbar.x_e * gaussLaw.z_e + Lbar.z_e * gaussLaw.x_e]
    -- gaussLaw has z_e = 0 and x_e = [v ∈ e], Lbar has x_e = 0 and z_e = δ e
    have h_edge : ∑ e : G.edgeSet,
        (Lbar.xVec (Sum.inr e) * (gaussLawChecks G v).zVec (Sum.inr e) +
         Lbar.zVec (Sum.inr e) * (gaussLawChecks G v).xVec (Sum.inr e)) =
        ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then δ e else 0) := by
      apply Finset.sum_congr rfl; intro e _
      simp only [hnoX e, gaussLawChecks, gaussLawOp, δ]
      ring_nf
      split <;> ring
    rw [h_edge] at hcomm_gauss
    -- This equals ∂(δ)(v)
    have hbdry : GraphMaps.boundaryMap G δ v = ∑ e : G.edgeSet,
        (if v ∈ (e : Sym2 V) then δ e else 0) := by
      simp [GraphMaps.boundaryMap_apply]
    rw [hbdry]; exact hcomm_gauss
  -- By boundary exactness, δ ∈ im(∂₂)
  have hδ_range := hexact_boundary δ hδ_ker
  -- So pureZEdgeOp(δ) ∈ stabilizerGroup
  have hstab := pureZEdgeOp_mem_stabilizerGroup_of_range G cycles checks data hcyc hcomm δ hδ_range
  -- But Lbar = pureZEdgeOp(δ) and Lbar is a logical (not in stabilizerGroup)
  rw [← hLbar_eq] at hstab
  exact hlog_Lbar.2.1 hstab

/-- Lifting: for any element S of the original stabilizer group, there exists
    S̃ in the deformed stabilizer group with restrictToV(S̃) = S and no X on edges. -/
theorem lift_originalStabilizer_to_deformed
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (S : PauliOp V)
    (hS : S ∈ origCode.stabilizerGroup) :
    ∃ S_tilde : PauliOp (ExtQubit G),
      S_tilde ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup ∧
      restrictToV G S_tilde = S ∧
      (∀ e : G.edgeSet, S_tilde.xVec (Sum.inr e) = 0) := by
  unfold StabilizerCode.stabilizerGroup at hS
  induction hS using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨i, hi⟩ := hs
    have hcheck : s = checks (hJ ▸ i) := by
      rw [← hi]; have := hchecks_eq (hJ ▸ i); subst hJ; simpa using this
    refine ⟨deformedOriginalChecks G checks data (hJ ▸ i), ?_, ?_, ?_⟩
    · exact deformed_mem_stabilizerGroup G cycles checks data hcyc hcomm (hJ ▸ i)
    · rw [restrictToV_deformedOriginalCheck, hcheck]
    · intro e; simp [deformedOriginalChecks, deformedCheck, deformedOpExt]
  | one =>
    exact ⟨1, Subgroup.one_mem _, restrictToV_one G, fun e => rfl⟩
  | mul s₁ s₂ _ _ ih₁ ih₂ =>
    obtain ⟨S₁t, hS₁_mem, hS₁_eq, hS₁_noX⟩ := ih₁
    obtain ⟨S₂t, hS₂_mem, hS₂_eq, hS₂_noX⟩ := ih₂
    refine ⟨S₁t * S₂t, Subgroup.mul_mem _ hS₁_mem hS₂_mem, ?_, ?_⟩
    · rw [restrictToV_mul, hS₁_eq, hS₂_eq]
    · intro e; simp [PauliOp.mul_xVec, Pi.add_apply, hS₁_noX e, hS₂_noX e]
  | inv s _ ih =>
    obtain ⟨S_tilde, hS_mem, hS_eq, hS_noX⟩ := ih
    refine ⟨S_tilde⁻¹, Subgroup.inv_mem _ hS_mem, ?_, ?_⟩
    · have : restrictToV G S_tilde⁻¹ = (restrictToV G S_tilde)⁻¹ := by
        simp [PauliOp.inv_eq_self, restrictToV]
      rw [this, hS_eq]
    · intro e; rw [PauliOp.inv_eq_self]; exact hS_noX e

/-- If Lbar is a logical of the deformed code, has no X on edges, and restrictToV(Lbar)
    is in the original stabilizer group, then with boundary exactness, Lbar is in the
    deformed stabilizer group (contradiction). -/
theorem cleaned_not_stabilizer_on_V
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (c : V → ZMod 2)
    (hc : GraphMaps.coboundaryMap G c = edgeXSupport G L')
    (hrestrict : restrictToV G (cleanedOp G L' c) ∈ origCode.stabilizerGroup) :
    False := by
  set Lbar := cleanedOp G L' c
  have hlog_Lbar := cleanedOp_isLogical G cycles checks data hcyc hcomm L' hlog c
  have hnoX : ∀ e, Lbar.xVec (Sum.inr e) = 0 :=
    cleaned_has_no_xSupport_on_edges G L' c (fun e => by rw [hc]; rfl)
  -- Lift restrictToV(Lbar) to a deformed stabilizer S̃ with no X on edges
  obtain ⟨S_tilde, hS_mem, hS_eq, hS_noX⟩ := lift_originalStabilizer_to_deformed G cycles checks
    origCode hJ hchecks_eq data hcyc hcomm (restrictToV G Lbar) hrestrict
  -- Q = Lbar * S̃ has restrictToV(Q) = 1
  have hQ_restrict : restrictToV G (Lbar * S_tilde) = 1 := by
    rw [restrictToV_mul, hS_eq, PauliOp.mul_self]
  -- Q has no X on edges (both Lbar and S̃ have no X on edges)
  have hQ_noX : ∀ e, (Lbar * S_tilde).xVec (Sum.inr e) = 0 := by
    intro e; simp [PauliOp.mul_xVec, Pi.add_apply, hnoX e, hS_noX e]
  -- Cases on Q
  by_cases hQ_one : Lbar * S_tilde = 1
  · -- Q = 1 → Lbar = S̃ ∈ stabilizerGroup
    have hLbar_eq_St : Lbar = S_tilde := by
      have h1 := congr_arg (· * S_tilde) hQ_one
      simp only [PauliOp.mul_assoc, PauliOp.mul_self, PauliOp.mul_one, PauliOp.one_mul] at h1
      exact h1
    have : Lbar ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
      rw [hLbar_eq_St]; exact hS_mem
    exact hlog_Lbar.2.1 this
  · by_cases hQ_stab : Lbar * S_tilde ∈
        (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup
    · -- Q ∈ stabilizerGroup → Lbar ∈ stabilizerGroup
      have hLbar_mem : Lbar ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
        have hLbar_eq2 : Lbar = (Lbar * S_tilde) * S_tilde := by
          simp only [PauliOp.mul_assoc, PauliOp.mul_self, PauliOp.mul_one]
        rw [hLbar_eq2]
        exact Subgroup.mul_mem _ hQ_stab hS_mem
      exact hlog_Lbar.2.1 hLbar_mem
    · -- Q is a logical of the deformed code
      have hQ_cent : (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer
          (Lbar * S_tilde) := by
        intro a
        unfold PauliCommute at *
        rw [symplecticInner_mul_left]
        have h1 := hlog_Lbar.1 a
        have h2 := StabilizerCode.stabilizerGroup_subset_centralizer
          (deformedStabilizerCode G cycles checks data hcyc hcomm) S_tilde hS_mem a
        unfold PauliCommute at h1 h2
        rw [h1, h2, add_zero]
      have hQ_log : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp
          (Lbar * S_tilde) := ⟨hQ_cent, hQ_stab, hQ_one⟩
      -- Q has restrictToV = 1 and no X on edges, so Q is a pureZEdgeOp
      -- Apply the same reasoning as case (b): Q.z on edges ∈ ker(∂), so in im(∂₂),
      -- so Q ∈ stabilizerGroup. Contradiction.
      -- Reuse cleaned_not_identity_on_V by constructing the right setup.
      -- Q has xVec = 0 on V (from hQ_restrict), zVec = 0 on V, xVec = 0 on edges.
      -- So Q = pureZEdgeOp(δ_Q) where δ_Q e = Q.zVec (Sum.inr e).
      have hxV : ∀ v, (Lbar * S_tilde).xVec (Sum.inl v) = 0 := by
        intro v; have h := congr_arg (·.xVec v) hQ_restrict; simpa [restrictToV] using h
      have hzV : ∀ v, (Lbar * S_tilde).zVec (Sum.inl v) = 0 := by
        intro v; have h := congr_arg (·.zVec v) hQ_restrict; simpa [restrictToV] using h
      set δ_Q := fun e : G.edgeSet => (Lbar * S_tilde).zVec (Sum.inr e)
      have hQ_eq : Lbar * S_tilde = pureZEdgeOp G δ_Q := by
        ext q
        · cases q with
          | inl v => simp [pureZEdgeOp, deformedOpExt, hxV v]
          | inr e => simp [pureZEdgeOp, deformedOpExt, hQ_noX e]
        · cases q with
          | inl v => simp [pureZEdgeOp, deformedOpExt, hzV v]
          | inr e => rfl
      -- δ_Q ∈ ker(∂) from Q commuting with gaussLaw checks
      have hδ_ker : δ_Q ∈ LinearMap.ker (GraphMaps.boundaryMap G) := by
        rw [LinearMap.mem_ker]; ext v; simp only [Pi.zero_apply]
        have hcomm_gauss := hQ_log.1 (.gaussLaw v)
        change PauliCommute (Lbar * S_tilde) (deformedCodeChecks G cycles checks data (.gaussLaw v)) at hcomm_gauss
        rw [deformedCodeChecks_gaussLaw] at hcomm_gauss
        unfold PauliCommute symplecticInner at hcomm_gauss
        rw [Fintype.sum_sum_type] at hcomm_gauss
        have h_vertex : ∑ w : V,
            ((Lbar * S_tilde).xVec (Sum.inl w) * (gaussLawChecks G v).zVec (Sum.inl w) +
             (Lbar * S_tilde).zVec (Sum.inl w) * (gaussLawChecks G v).xVec (Sum.inl w)) = 0 := by
          apply Finset.sum_eq_zero; intro w _; rw [hxV w, hzV w]; ring
        rw [h_vertex, zero_add] at hcomm_gauss
        have h_edge : ∑ e : G.edgeSet,
            ((Lbar * S_tilde).xVec (Sum.inr e) * (gaussLawChecks G v).zVec (Sum.inr e) +
             (Lbar * S_tilde).zVec (Sum.inr e) * (gaussLawChecks G v).xVec (Sum.inr e)) =
            ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then δ_Q e else 0) := by
          apply Finset.sum_congr rfl; intro e _
          simp only [hQ_noX e, gaussLawChecks, gaussLawOp, δ_Q]; ring_nf; split <;> ring
        rw [h_edge] at hcomm_gauss
        have hbdry : GraphMaps.boundaryMap G δ_Q v = ∑ e : G.edgeSet,
            (if v ∈ (e : Sym2 V) then δ_Q e else 0) := by
          simp [GraphMaps.boundaryMap_apply]
        rw [hbdry]; exact hcomm_gauss
      -- By boundary exactness, δ_Q ∈ im(∂₂)
      have hδ_range := hexact_boundary δ_Q hδ_ker
      -- So pureZEdgeOp(δ_Q) ∈ stabilizerGroup
      have hstab := pureZEdgeOp_mem_stabilizerGroup_of_range G cycles checks data hcyc hcomm δ_Q hδ_range
      rw [← hQ_eq] at hstab
      exact hQ_log.2.1 hstab

/-- **Step 4 (Paper): Any cleaning of L' restricted to V is a logical of the original code.**
    Given boundary exactness (ker(∂) ⊆ im(∂₂)), for any c with δc = edgeXSupport(L'),
    the restriction restrictToV(cleanedOp(L', c)) is a logical of the original code. -/
theorem any_cleaning_gives_logical
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (_hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (c : V → ZMod 2)
    (hc_cob : GraphMaps.coboundaryMap G c = edgeXSupport G L') :
    origCode.isLogicalOp (restrictToV G (cleanedOp G L' c)) := by
  set Lbar := cleanedOp G L' c
  have hlog_Lbar := cleanedOp_isLogical G cycles checks data hcyc hcomm L' hlog c
  have hnoX : ∀ e, Lbar.xVec (Sum.inr e) = 0 :=
    cleaned_has_no_xSupport_on_edges G L' c (fun e => by rw [hc_cob]; rfl)
  -- restrictToV(Lbar) is in the centralizer of the original code
  have hcent : origCode.inCentralizer (restrictToV G Lbar) := by
    intro i
    have hlog_clean := hlog_Lbar.1 (.deformed (hJ ▸ i))
    simp only [deformedCodeChecks_deformed] at hlog_clean
    have h_comm_check := cleaned_commutes_with_original_check G checks Lbar data hnoX (hJ ▸ i) hlog_clean
    have : origCode.check i = checks (hJ ▸ i) := by
      have := hchecks_eq (hJ ▸ i); subst hJ; simpa using this
    rw [this]; exact h_comm_check
  -- Suppose restrictToV(Lbar) is NOT a logical. Then either it's a stabilizer or identity.
  by_contra h_not_logical
  have h_cases : restrictToV G Lbar ∈ origCode.stabilizerGroup ∨ restrictToV G Lbar = 1 := by
    by_contra h_contra; push_neg at h_contra
    exact h_not_logical ⟨hcent, h_contra.1, h_contra.2⟩
  rcases h_cases with h_stab | h_id
  · -- Case (a): restriction is a stabilizer
    exact cleaned_not_stabilizer_on_V G cycles checks origCode hJ hchecks_eq data hcyc hcomm
      hexact_boundary L' hlog c hc_cob h_stab
  · -- Case (b): restriction is identity
    exact cleaned_not_identity_on_V G cycles checks data hcyc hcomm hexact_boundary L' hlog c hc_cob h_id

/-! ## Constructing the WLOG hypothesis

From the cocycle condition and exactness, we obtain a cleaning vector c.
From the disjunction and support partition, we show there exists a c with
small support that gives a logical restriction. -/

/-- **Construction of the WLOG cleaning vector.** Given exactness of both sequences
    and that any cleaning gives a logical (derived from boundary exactness), we find c
    with δc = edgeXSupport(L'), the restriction is a logical, and |supp(c)| ≤ |V|/2. -/
theorem construct_wlog
    (origCode : StabilizerCode V)
    (_hJ : origCode.I = J)
    (_hchecks_eq : ∀ j : J, origCode.check (_hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (_hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L') :
    ∃ c : V → ZMod 2,
      GraphMaps.coboundaryMap G c = edgeXSupport G L' ∧
      origCode.isLogicalOp (restrictToV G (cleanedOp G L' c)) ∧
      2 * (Finset.univ.filter (fun v : V => c v ≠ 0)).card ≤ Fintype.card V := by
  -- Step 2: edgeXSupport is a cocycle
  have hcocycle := edgeXSupport_in_ker_secondCoboundary G cycles checks data hcyc hcomm L' hlog
  -- From exactness, get c₀ with δc₀ = edgeXSupport(L')
  obtain ⟨c₀, hc₀⟩ := hexact _ hcocycle
  -- Any cleaning gives a logical (from boundary exactness)
  have hAllCleaningsLogical : ∀ c : V → ZMod 2,
      GraphMaps.coboundaryMap G c = edgeXSupport G L' →
      origCode.isLogicalOp (restrictToV G (cleanedOp G L' c)) :=
    fun c hc => any_cleaning_gives_logical G cycles checks origCode _hJ _hchecks_eq
      data hcyc hcomm hexact_boundary _hL_logical L' hlog c hc
  -- Choose c₀ or c₀+1 depending on support size
  by_cases hS : 2 * (Finset.univ.filter (fun v : V => c₀ v ≠ 0)).card ≤ Fintype.card V
  · -- c₀ has small support
    exact ⟨c₀, hc₀, hAllCleaningsLogical c₀ hc₀, hS⟩
  · -- c₀ has big support, use c₀ + 1 which has the same coboundary
    push_neg at hS
    set c₁ := c₀ + fun _ => (1 : ZMod 2)
    have hc₁ : GraphMaps.coboundaryMap G c₁ = edgeXSupport G L' := by
      rw [coboundary_add_ones_eq]; exact hc₀
    have hS₁ : 2 * (Finset.univ.filter (fun v : V => c₁ v ≠ 0)).card ≤ Fintype.card V := by
      have hpart := support_add_complement_card c₀
      have hfilt : (Finset.univ.filter (fun v : V => c₁ v ≠ 0)) =
          (Finset.univ.filter (fun v : V => c₀ v + 1 ≠ 0)) := by
        apply Finset.filter_congr; intro v _; simp [c₁, Pi.add_apply]
      rw [hfilt]; omega
    exact ⟨c₁, hc₁, hAllCleaningsLogical c₁ hc₁, hS₁⟩

/-! ## Arithmetic Core of the Distance Bound -/

/-- **Core arithmetic lemma for the distance bound.** -/
theorem weight_lower_bound_arithmetic
    (w d suppC_card coboundary_card : ℕ)
    (h_cheeger : ℝ)
    (h_cheeger_nn : 0 ≤ h_cheeger)
    (hw_ge_vertex_minus_plus_edge : w + suppC_card ≥ d + coboundary_card)
    (h_coboundary_ge : h_cheeger * suppC_card ≤ coboundary_card)
    (hw_ge_coboundary : coboundary_card ≤ w) :
    (w : ℝ) ≥ min h_cheeger 1 * d := by
  by_cases h1 : h_cheeger ≥ 1
  · rw [min_eq_right h1, _root_.one_mul]
    have hcob_ge_supp : suppC_card ≤ coboundary_card := by
      have : (1 : ℝ) * suppC_card ≤ h_cheeger * suppC_card :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      have : (suppC_card : ℝ) ≤ coboundary_card := by linarith
      exact_mod_cast this
    have : d ≤ w := by omega
    exact_mod_cast this
  · push_neg at h1
    rw [min_eq_left (le_of_lt h1)]
    by_cases hsd : (suppC_card : ℝ) ≤ d
    · have h_from_ineq : (w : ℝ) + suppC_card ≥ d + coboundary_card := by
        exact_mod_cast hw_ge_vertex_minus_plus_edge
      have : (w : ℝ) ≥ d + (h_cheeger - 1) * suppC_card := by linarith
      calc (w : ℝ) ≥ d + (h_cheeger - 1) * suppC_card := this
        _ ≥ d + (h_cheeger - 1) * d := by
            have : (h_cheeger - 1) * suppC_card ≥ (h_cheeger - 1) * d :=
              mul_le_mul_of_nonpos_left hsd (by linarith)
            linarith
        _ = h_cheeger * d := by ring
    · push_neg at hsd
      calc (w : ℝ) ≥ coboundary_card := by exact_mod_cast hw_ge_coboundary
        _ ≥ h_cheeger * suppC_card := h_coboundary_ge
        _ ≥ h_cheeger * d := mul_le_mul_of_nonneg_left (le_of_lt hsd) h_cheeger_nn

/-! ## Vertex Weight Bound -/

/-- The vertex weight of L' plus the size of c's support is at least the vertex weight
    of the cleaned operator restricted to V. -/
theorem vertex_weight_plus_c_ge_cleaned_weight
    (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2) :
    (restrictToV G L').weight + (Finset.univ.filter (fun v : V => c v ≠ 0)).card ≥
    (restrictToV G (cleanedOp G L' c)).weight := by
  unfold PauliOp.weight PauliOp.support
  apply le_trans _ (Finset.card_union_le _ _)
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
  rcases hv with hx | hz
  · -- X-support
    by_cases hcv : c v = 0
    · left; left
      simp only [restrictToV] at hx ⊢
      rwa [cleanedOp_xVec_vertex, hcv, add_zero] at hx
    · right; exact hcv
  · left; right
    simp only [restrictToV] at hz ⊢
    rwa [cleanedOp_zVec] at hz

/-! ## Cheeger bound for a specific cleaning vector -/

/-- The Cheeger constant times the support size of c is bounded by the edge support count. -/
private theorem cheeger_times_support_le_edge_card
    (L' : PauliOp (ExtQubit G)) (c : V → ZMod 2)
    (hc : GraphMaps.coboundaryMap G c = edgeXSupport G L')
    (hc_ne : c ≠ 0)
    (hS_half : 2 * (Finset.univ.filter (fun v : V => c v ≠ 0)).card ≤ Fintype.card V) :
    QEC1.cheegerConstant G *
      (Finset.univ.filter (fun v : V => c v ≠ 0)).card ≤
    (Finset.univ.filter (fun e : G.edgeSet =>
      L'.xVec (Sum.inr e) ≠ 0 ∨ L'.zVec (Sum.inr e) ≠ 0)).card := by
  have hS_ne : (Finset.univ.filter (fun v : V => c v ≠ 0)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    apply hc_ne; ext v
    have : v ∉ Finset.univ.filter (fun v : V => c v ≠ 0) := h ▸ Finset.notMem_empty v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this; exact this
  calc QEC1.cheegerConstant G *
        (Finset.univ.filter (fun v : V => c v ≠ 0)).card
      ≤ (QEC1.SimpleGraph.edgeBoundary G
          (Finset.univ.filter (fun v : V => c v ≠ 0))).card := by
        exact_mod_cast SimpleGraph.edgeBoundary_card_ge_of_cheeger G
          (QEC1.cheegerConstant G) (le_refl _) _ hS_ne hS_half
    _ = (Finset.univ.filter (fun e : G.edgeSet =>
          GraphMaps.coboundaryMap G c e ≠ 0)).card := by
        rw [coboundary_support_card_eq_edgeBoundary_card]
    _ ≤ (Finset.univ.filter (fun e : G.edgeSet =>
          L'.xVec (Sum.inr e) ≠ 0 ∨ L'.zVec (Sum.inr e) ≠ 0)).card := by
        exact_mod_cast edge_support_ge_coboundary_support G L' c hc

/-! ## Main Distance Bound Theorem -/

/-- **Lemma 3 (Space Distance): Per-operator bound.**
    d* ≥ min(h(G), 1) · d -/
theorem distance_ge_min_cheeger_one_mul_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (_hconn : G.Connected)
    (_hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L') :
    (L'.weight : ℝ) ≥ min (QEC1.cheegerConstant G) 1 * origCode.distance := by
  -- Derive WLOG from construct_wlog
  have hWLOG := construct_wlog G cycles checks origCode hJ hchecks_eq data hcyc hcomm
    hexact hexact_boundary hL_logical L' hlog
  obtain ⟨c, hc_eq, hlog_c, hS_half⟩ := hWLOG
  have _h_decomp := weight_decomposition G L'
  -- Main proof: given c with δc = edge X-support, c gives a logical, and 2|S| ≤ |V|
  set S := (Finset.univ.filter (fun v : V => c v ≠ 0)).card
  have hweight_ge_d : origCode.distance ≤ (restrictToV G (cleanedOp G L' c)).weight := by
    unfold StabilizerCode.distance; apply Nat.sInf_le; exact ⟨_, hlog_c, rfl⟩
  have h_vertex := vertex_weight_plus_c_ge_cleaned_weight G L' c
  have hw1 : L'.weight + S ≥ origCode.distance +
      (Finset.univ.filter (fun e : G.edgeSet =>
        L'.xVec (Sum.inr e) ≠ 0 ∨ L'.zVec (Sum.inr e) ≠ 0)).card := by
    have : (restrictToV G L').weight + S ≥ (restrictToV G (cleanedOp G L' c)).weight :=
      h_vertex
    omega
  have hw2 : (Finset.univ.filter (fun e : G.edgeSet =>
      L'.xVec (Sum.inr e) ≠ 0 ∨ L'.zVec (Sum.inr e) ≠ 0)).card ≤ L'.weight := by omega
  -- Cheeger bound: h·S ≤ edge support
  have h_cheeger : QEC1.cheegerConstant G * (S : ℝ) ≤
      (Finset.univ.filter (fun e : G.edgeSet =>
        L'.xVec (Sum.inr e) ≠ 0 ∨ L'.zVec (Sum.inr e) ≠ 0)).card := by
    by_cases hc_ne : c = 0
    · -- When c = 0, S = 0
      have hS_zero : S = 0 := by
        change (Finset.univ.filter (fun v : V => c v ≠ 0)).card = 0
        rw [hc_ne]; simp
      rw [hS_zero, Nat.cast_zero, mul_zero]
      exact_mod_cast Nat.zero_le _
    · exact_mod_cast cheeger_times_support_le_edge_card G L' c hc_eq hc_ne hS_half
  exact weight_lower_bound_arithmetic L'.weight origCode.distance S
    (Finset.univ.filter (fun e : G.edgeSet =>
      L'.xVec (Sum.inr e) ≠ 0 ∨ L'.zVec (Sum.inr e) ≠ 0)).card
    (QEC1.cheegerConstant G) (SimpleGraph.cheegerConstant_nonneg G)
    hw1 (by exact_mod_cast h_cheeger) hw2

/-! ## If L' is logical and gaussSubsetProduct is a stabilizer, the product is equivalent -/

/-- If L' is logical and s is a stabilizer, then L' * s is logical or a stabilizer. -/
theorem logical_mul_stabilizer
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c₀ : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c₀ ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L')
    (s : PauliOp (ExtQubit G))
    (hs : s ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup)
    (hne : L' * s ≠ 1) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp (L' * s) ∨
    L' * s ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
  have hcent : (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer (L' * s) := by
    intro i
    unfold PauliCommute at *
    rw [symplecticInner_mul_left]
    have h1 := hlog.1 i
    have h2 := StabilizerCode.stabilizerGroup_subset_centralizer
      (deformedStabilizerCode G cycles checks data hcyc hcomm) s hs i
    unfold PauliCommute at h1 h2
    rw [h1, h2, add_zero]
  by_cases hmem : L' * s ∈ (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup
  · right; exact hmem
  · left; exact ⟨hcent, hmem, hne⟩

/-! ## Sufficient Expansion Corollary -/

/-- **Corollary: if h(G) ≥ 1, then d* ≥ d for each logical operator.** -/
theorem distance_ge_d_of_sufficient_expansion
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
    (L' : PauliOp (ExtQubit G))
    (hlog : (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp L') :
    origCode.distance ≤ L'.weight := by
  have h := distance_ge_min_cheeger_one_mul_d G cycles checks origCode hJ hchecks_eq
    data hcyc hcomm hconn hcard hexact hexact_boundary hL_logical L' hlog
  rw [show min (QEC1.cheegerConstant G) 1 = 1 from min_eq_right hexp] at h
  rw [_root_.one_mul] at h
  exact_mod_cast h

/-! ## Deformed Code Distance -/

/-- **Main theorem: deformed code distance bound.**
    d* ≥ min(h(G), 1) · d. -/
theorem deformed_distance_ge_min_cheeger_d
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
    (hL_logical : origCode.isLogicalOp (logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P) :
    min (QEC1.cheegerConstant G) 1 * origCode.distance ≤
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance := by
  unfold StabilizerCode.distance
  obtain ⟨P₀, hP₀⟩ := hDeformedHasLogicals
  have hnonempty : { w : ℕ | ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P ∧
      P.weight = w }.Nonempty := ⟨P₀.weight, P₀, hP₀, rfl⟩
  have hbound : ∀ w ∈ { w : ℕ | ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P ∧
      P.weight = w }, min (QEC1.cheegerConstant G) 1 * origCode.distance ≤ (w : ℝ) := by
    intro w ⟨P, hP, hw⟩
    rw [← hw]
    exact distance_ge_min_cheeger_one_mul_d G cycles checks origCode hJ hchecks_eq
      data hcyc hcomm hconn hcard hexact hexact_boundary hL_logical P hP
  have hle : ∀ w ∈ { w : ℕ | ∃ P : PauliOp (ExtQubit G),
      (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P ∧
      P.weight = w }, (Nat.ceil (min (QEC1.cheegerConstant G) 1 * origCode.distance) : ℕ) ≤ w := by
    intro w hw
    exact Nat.ceil_le.mpr (hbound w hw)
  have hsInf_ge : Nat.ceil (min (QEC1.cheegerConstant G) 1 * origCode.distance) ≤
      sInf { w : ℕ | ∃ P : PauliOp (ExtQubit G),
        (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P ∧
        P.weight = w } := by
    apply le_csInf hnonempty
    intro w hw; exact hle w hw
  calc min (QEC1.cheegerConstant G) 1 * ↑origCode.distance
      ≤ ↑(Nat.ceil (min (QEC1.cheegerConstant G) 1 * ↑origCode.distance)) :=
        Nat.le_ceil _
    _ ≤ ↑(sInf { w : ℕ | ∃ P : PauliOp (ExtQubit G),
          (deformedStabilizerCode G cycles checks data hcyc hcomm).isLogicalOp P ∧
          P.weight = w }) := by exact_mod_cast hsInf_ge

/-- **Corollary: sufficient expansion preserves distance.**
    If h(G) ≥ 1, then the deformed code distance d* ≥ d. -/
theorem deformed_distance_ge_d_sufficient_expansion
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
    (deformedStabilizerCode G cycles checks data hcyc hcomm).distance := by
  have h := deformed_distance_ge_min_cheeger_d G cycles checks origCode hJ hchecks_eq
    data hcyc hcomm hconn hcard hexact hexact_boundary hL_logical hDeformedHasLogicals
  have h2 : min (QEC1.cheegerConstant G) 1 = 1 := min_eq_right hexp
  have h3 : (1 : ℝ) * origCode.distance ≤
      ((deformedStabilizerCode G cycles checks data hcyc hcomm).distance : ℝ) := by
    rw [← h2]; exact_mod_cast h
  rw [_root_.one_mul] at h3
  exact_mod_cast h3

end SpaceDistance
