import QEC1.Remarks.Rem_19_BivariateBicycleCodeNotation
import Mathlib.Tactic

set_option linter.unusedDecidableInType false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false

/-!
# Remark 20: The Gross Code Definition

## Statement
The **Gross code** is a [[144, 12, 12]] BB code with parameters ℓ = 12, m = 6.
- A = x³ + y² + y
- B = y³ + x² + x

Logical operators use polynomials f, g, h in F₂[x,y]/(x¹² - 1, y⁶ - 1).
The logical X̄_α = X(αf, 0) has weight 12 and acts only on L qubits.

## Main Results
- `grossA`, `grossB`: the polynomials A and B
- `grossCode`: the Gross code as a valid stabilizer code
- `grossF`, `grossG`, `grossH`: the logical operator polynomials
- `logicalXBar`, `logicalXBar'`: the logical X operators
- `logicalZBar`, `logicalZBar'`: the logical Z operators
- `grossCode_numQubits`: the code has n = 144 physical qubits
- `grossCode_numChecks`: the code has 144 checks
- `logicalXBar_weight`: X̄_α has weight 12
- `logicalXBar_pure_X`: X̄_α is pure X-type
- `logicalXBar_acts_only_on_L`: X̄_α acts only on L qubits
- `logicalXBar_inCentralizer`: X̄_α is in the centralizer (a logical operator candidate)
- `logicalXBar_tanner_expansion_insufficient`: key property about limited Tanner expansion
-/

namespace BivariateBicycle

namespace GrossCode

/-! ## The Gross code parameters -/

/-- ℓ = 12 for the Gross code. -/
abbrev ℓ : ℕ := 12

/-- m = 6 for the Gross code. -/
abbrev m : ℕ := 6

/-- The monomial group for the Gross code: Z₁₂ × Z₆. -/
abbrev GrossMonomial := BBMonomial ℓ m

/-- The group algebra for the Gross code: F₂[x,y]/(x¹² - 1, y⁶ - 1). -/
abbrev GrossAlgebra := BBGroupAlgebra ℓ m

/-- The qubit type for the Gross code. -/
abbrev GrossQubit := BBQubit ℓ m

/-! ## Polynomial definitions -/

/-- A = x³ + y² + y in F₂[x,y]/(x¹² - 1, y⁶ - 1). -/
def grossA : GrossAlgebra :=
  bbMonomial 3 0 + bbMonomial 0 2 + bbMonomial 0 1

/-- B = y³ + x² + x in F₂[x,y]/(x¹² - 1, y⁶ - 1). -/
def grossB : GrossAlgebra :=
  bbMonomial 0 3 + bbMonomial 2 0 + bbMonomial 1 0

/-! ## Check commutation -/

-- X and Z checks commute by abelianness of the monomial group + characteristic 2.
set_option maxHeartbeats 800000 in
private theorem grossChecks_XZ_commute_raw :
    ∀ (α β : GrossMonomial),
      (∑ γ : GrossMonomial, grossA (γ - α) * grossB (-(γ - β))) +
      (∑ δ : GrossMonomial, grossB (δ - α) * grossA (-(δ - β))) = 0 := by
  native_decide

theorem grossChecks_XZ_commute (α β : GrossMonomial) :
    PauliOp.PauliCommute (bbCheckX grossA grossB α) (bbCheckZ grossA grossB β) := by
  classical
  rw [bbCheckXZ_commute_iff]
  exact grossChecks_XZ_commute_raw α β

theorem grossChecks_commute (i j : BBCheckIndex ℓ m) :
    PauliOp.PauliCommute (bbCheck grossA grossB i) (bbCheck grossA grossB j) := by
  match i, j with
  | Sum.inl α₁, Sum.inl α₂ => exact bbCheckX_commute grossA grossB α₁ α₂
  | Sum.inl α, Sum.inr β => exact grossChecks_XZ_commute α β
  | Sum.inr β, Sum.inl α =>
    rw [PauliOp.pauliCommute_comm]; exact grossChecks_XZ_commute α β
  | Sum.inr β₁, Sum.inr β₂ => exact bbCheckZ_commute grossA grossB β₁ β₂

/-! ## The Gross code as a stabilizer code -/

/-- The Gross code as a valid stabilizer code, constructed directly. -/
noncomputable def grossCode : StabilizerCode GrossQubit where
  I := BBCheckIndex ℓ m
  check := bbCheck grossA grossB
  checks_commute := grossChecks_commute

/-- The Gross code has 144 = 2 × 12 × 6 physical qubits. -/
theorem grossCode_numQubits : grossCode.numQubits = 144 := by
  simp only [StabilizerCode.numQubits, Fintype.card_sum, Fintype.card_prod, ZMod.card]
  norm_num [ℓ, m]

/-- The Gross code has 144 = 2 × 12 × 6 checks. -/
theorem grossCode_numChecks : grossCode.numChecks = 144 := by
  simp only [StabilizerCode.numChecks, grossCode, Fintype.card_sum, Fintype.card_prod, ZMod.card]
  norm_num [ℓ, m]

/-! ## Logical operator polynomials -/

/-- f = 1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹ + (x + x⁵ + x⁷ + x¹¹)y³ -/
def grossF : GrossAlgebra :=
  bbMonomial 0 0 + bbMonomial 1 0 + bbMonomial 2 0 + bbMonomial 3 0 +
  bbMonomial 6 0 + bbMonomial 7 0 + bbMonomial 8 0 + bbMonomial 9 0 +
  bbMonomial 1 3 + bbMonomial 5 3 + bbMonomial 7 3 + bbMonomial 11 3

/-- g = x + x²y + (1+x)y² + x²y³ + y⁴ -/
def grossG : GrossAlgebra :=
  bbMonomial 1 0 + bbMonomial 2 1 + bbMonomial 0 2 + bbMonomial 1 2 +
  bbMonomial 2 3 + bbMonomial 0 4

/-- h = 1 + (1+x)y + y² + (1+x)y³ -/
def grossH : GrossAlgebra :=
  bbMonomial 0 0 + bbMonomial 0 1 + bbMonomial 1 1 + bbMonomial 0 2 +
  bbMonomial 0 3 + bbMonomial 1 3

/-! ## Logical X operators -/

/-- The logical X operator X̄_α = X(αf, 0) for α ∈ M. -/
def logicalXBar (α : GrossMonomial) : PauliOp GrossQubit :=
  pauliXBB (bbShift α grossF) 0

/-- The logical X' operator X̄'_β = X(βg, βh) for β ∈ M. -/
def logicalXBar' (β : GrossMonomial) : PauliOp GrossQubit :=
  pauliXBB (bbShift β grossG) (bbShift β grossH)

/-! ## Logical Z operators -/

/-- The logical Z operator Z̄_β = Z(βh^T, βg^T) for β ∈ M. -/
def logicalZBar (β : GrossMonomial) : PauliOp GrossQubit :=
  pauliZBB (bbShift β (bbTranspose grossH)) (bbShift β (bbTranspose grossG))

/-- The logical Z' operator Z̄'_α = Z(0, αf^T) for α ∈ M. -/
def logicalZBar' (α : GrossMonomial) : PauliOp GrossQubit :=
  pauliZBB 0 (bbShift α (bbTranspose grossF))

/-! ## Properties of X̄_α -/

/-- X̄_α is pure X-type: it has no Z-support. -/
theorem logicalXBar_pure_X (α : GrossMonomial) :
    (logicalXBar α).zVec = 0 := by
  simp [logicalXBar, pauliXBB]

/-- X̄'_β is pure X-type: it has no Z-support. -/
theorem logicalXBar'_pure_X (β : GrossMonomial) :
    (logicalXBar' β).zVec = 0 := by
  simp [logicalXBar', pauliXBB]

/-- Z̄_β is pure Z-type: it has no X-support. -/
theorem logicalZBar_pure_Z (β : GrossMonomial) :
    (logicalZBar β).xVec = 0 := by
  simp [logicalZBar, pauliZBB]

/-- Z̄'_α is pure Z-type: it has no X-support. -/
theorem logicalZBar'_pure_Z (α : GrossMonomial) :
    (logicalZBar' α).xVec = 0 := by
  simp [logicalZBar', pauliZBB]

/-- X̄_α acts only on L qubits: xVec on R qubits is zero. -/
theorem logicalXBar_acts_only_on_L (α : GrossMonomial) (δ : GrossMonomial) :
    (logicalXBar α).xVec (Sum.inr δ) = 0 := by
  simp [logicalXBar, pauliXBB]

/-- Z̄'_α acts only on R qubits: zVec on L qubits is zero. -/
theorem logicalZBar'_acts_only_on_R (α : GrossMonomial) (γ : GrossMonomial) :
    (logicalZBar' α).zVec (Sum.inl γ) = 0 := by
  simp [logicalZBar', pauliZBB]

/-! ## Support and weight -/

/-- The polynomial f has weight 12 (12 nonzero coefficients). -/
theorem grossF_weight_eq_12 :
    (Finset.univ.filter (fun (γ : GrossMonomial) => grossF γ ≠ 0)).card = 12 := by
  native_decide

/-- A has 3 nonzero coefficients. -/
theorem grossA_support_card :
    (Finset.univ.filter (fun (γ : GrossMonomial) => grossA γ ≠ 0)).card = 3 := by
  native_decide

/-- B has 3 nonzero coefficients. -/
theorem grossB_support_card :
    (Finset.univ.filter (fun (γ : GrossMonomial) => grossB γ ≠ 0)).card = 3 := by
  native_decide

/-! ## Shift-invariance of support cardinality -/

/-- The support of pauliXBB (bbShift α p) 0 has the same cardinality for all α. -/
private lemma pureX_L_support_shift_invariant (p : GrossAlgebra)
    (α : GrossMonomial) :
    (Finset.univ.filter (fun q : GrossQubit =>
      (pauliXBB (bbShift α p) (0 : GrossAlgebra)).xVec q ≠ 0 ∨
      (pauliXBB (bbShift α p) (0 : GrossAlgebra)).zVec q ≠ 0)).card =
    (Finset.univ.filter (fun q : GrossQubit =>
      (pauliXBB p (0 : GrossAlgebra)).xVec q ≠ 0 ∨
      (pauliXBB p (0 : GrossAlgebra)).zVec q ≠ 0)).card := by
  apply Finset.card_bij (fun q _ => match q with
    | Sum.inl γ => Sum.inl (γ - α)
    | Sum.inr δ => Sum.inr δ)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      pauliXBB_zVec, Pi.zero_apply, ne_eq, not_true_eq_false, or_false,
      pauliXBB_xVec_left, pauliXBB_xVec_right] at hq ⊢
    match q with
    | Sum.inl _ => exact hq  -- bbShift α p γ = p (γ - α) definitionally
    | Sum.inr δ => simp [pauliXBB] at hq
  · intro a₁ ha₁ a₂ ha₂ h
    match a₁, a₂ with
    | Sum.inl _, Sum.inl _ =>
      exact congrArg Sum.inl (sub_left_injective (Sum.inl.inj h))
    | Sum.inr _, Sum.inr _ => exact congrArg Sum.inr (Sum.inr.inj h)
    | Sum.inl _, Sum.inr _ => exact absurd h (by simp)
    | Sum.inr _, Sum.inl _ => exact absurd h (by simp)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      pauliXBB_zVec, Pi.zero_apply, ne_eq, not_true_eq_false, or_false,
      pauliXBB_xVec_left, pauliXBB_xVec_right] at hq
    match q with
    | Sum.inl γ =>
      refine ⟨Sum.inl (γ + α), ?_, by simp [add_sub_cancel_right]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        pauliXBB_zVec, Pi.zero_apply, ne_eq, not_true_eq_false, or_false,
        pauliXBB_xVec_left, bbShift, add_sub_cancel_right]
      exact hq
    | Sum.inr δ => simp [pauliXBB] at hq

set_option maxHeartbeats 800000 in
/-- X̄_α has weight 12. -/
theorem logicalXBar_weight (α : GrossMonomial) :
    (logicalXBar α).weight = 12 := by
  classical
  simp only [PauliOp.weight, PauliOp.support, logicalXBar]
  rw [pureX_L_support_shift_invariant grossF α]
  native_decide

/-! ## Self-inverse properties -/

/-- X̄_α is self-inverse. -/
theorem logicalXBar_mul_self (α : GrossMonomial) :
    logicalXBar α * logicalXBar α = 1 := by
  simp only [logicalXBar, pauliXBB_mul]
  ext q
  · simp only [PauliOp.one_xVec, Pi.zero_apply, Pi.add_apply]
    match q with
    | Sum.inl γ => simp [pauliXBB, CharTwo.add_self_eq_zero]
    | Sum.inr δ => simp [pauliXBB]
  · simp [pauliXBB]

/-- X̄'_β is self-inverse. -/
theorem logicalXBar'_mul_self (β : GrossMonomial) :
    logicalXBar' β * logicalXBar' β = 1 := by
  simp only [logicalXBar', pauliXBB_mul]
  ext q
  · simp only [PauliOp.one_xVec, Pi.zero_apply, Pi.add_apply]
    match q with
    | Sum.inl γ => simp [pauliXBB, CharTwo.add_self_eq_zero]
    | Sum.inr δ => simp [pauliXBB, CharTwo.add_self_eq_zero]
  · simp [pauliXBB]

/-- Z̄_β is self-inverse. -/
theorem logicalZBar_mul_self (β : GrossMonomial) :
    logicalZBar β * logicalZBar β = 1 := by
  simp only [logicalZBar, pauliZBB_mul]
  ext q
  · simp [pauliZBB]
  · simp only [PauliOp.one_zVec, Pi.zero_apply, Pi.add_apply]
    match q with
    | Sum.inl γ => simp [pauliZBB, CharTwo.add_self_eq_zero]
    | Sum.inr δ => simp [pauliZBB, CharTwo.add_self_eq_zero]

/-- Z̄'_α is self-inverse. -/
theorem logicalZBar'_mul_self (α : GrossMonomial) :
    logicalZBar' α * logicalZBar' α = 1 := by
  simp only [logicalZBar', pauliZBB_mul]
  ext q
  · simp [pauliZBB]
  · simp only [PauliOp.one_zVec, Pi.zero_apply, Pi.add_apply]
    match q with
    | Sum.inl γ => simp [pauliZBB]
    | Sum.inr δ => simp [pauliZBB, CharTwo.add_self_eq_zero]

/-! ## Kernel conditions via native_decide -/

set_option maxHeartbeats 800000 in
private theorem grossF_kernel_BT :
    ∀ (γ : GrossMonomial),
      (∑ δ : GrossMonomial, grossF δ * grossB (-(δ - γ))) = 0 := by
  native_decide

set_option maxHeartbeats 800000 in
private theorem grossGH_kernel :
    ∀ (γ : GrossMonomial),
      (∑ δ : GrossMonomial, grossG δ * grossB (-(δ - γ))) +
      (∑ δ : GrossMonomial, grossH δ * grossA (-(δ - γ))) = 0 := by
  native_decide

set_option maxHeartbeats 800000 in
private theorem grossHG_kernel_X :
    ∀ (γ : GrossMonomial),
      (∑ δ : GrossMonomial, grossA δ * grossH (-(δ - γ))) +
      (∑ δ : GrossMonomial, grossB δ * grossG (-(δ - γ))) = 0 := by
  native_decide

set_option maxHeartbeats 800000 in
private theorem grossF_kernel_AT :
    ∀ (γ : GrossMonomial),
      (∑ δ : GrossMonomial, grossB δ * grossF (-(δ - γ))) = 0 := by
  native_decide

/-! ## Commutation of logical operators with checks -/

/-- X̄_α commutes with all X checks (both pure X-type). -/
theorem logicalXBar_commute_xCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalXBar α) (bbCheckX grossA grossB β) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, logicalXBar, pauliXBB, bbCheckX]

/-- X̄_α commutes with all Z checks. -/
theorem logicalXBar_commute_zCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalXBar α) (bbCheckZ grossA grossB β) := by
  classical
  rw [PauliOp.PauliCommute, PauliOp.symplecticInner]
  simp only [logicalXBar, pauliXBB, bbCheckZ, pauliZBB, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero,
    Pi.zero_apply, zero_mul, bbShift, bbTranspose]
  rw [show (∑ x : GrossMonomial, grossF (x - α) * grossB (-(x - β))) =
      ∑ δ : GrossMonomial, grossF δ * grossB (-(δ - (β - α))) from
    Fintype.sum_equiv (Equiv.subRight α) _ _ (fun δ => by
      simp [Equiv.subRight_apply, sub_sub])]
  exact grossF_kernel_BT (β - α)

/-- X̄_α commutes with all checks of the Gross code. -/
theorem logicalXBar_commute_allChecks (α : GrossMonomial)
    (i : BBCheckIndex ℓ m) :
    PauliOp.PauliCommute (logicalXBar α) (bbCheck grossA grossB i) := by
  match i with
  | Sum.inl β => exact logicalXBar_commute_xCheck α β
  | Sum.inr β => exact logicalXBar_commute_zCheck α β

/-- X̄'_β commutes with all X checks (both pure X-type). -/
theorem logicalXBar'_commute_xCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalXBar' α) (bbCheckX grossA grossB β) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, logicalXBar', pauliXBB, bbCheckX]

/-- X̄'_β commutes with all Z checks. -/
theorem logicalXBar'_commute_zCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalXBar' α) (bbCheckZ grossA grossB β) := by
  classical
  rw [PauliOp.PauliCommute, PauliOp.symplecticInner]
  simp only [logicalXBar', pauliXBB, bbCheckZ, pauliZBB, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, bbShift, bbTranspose]
  rw [show (∑ x : GrossMonomial, grossG (x - α) * grossB (-(x - β))) =
      ∑ δ : GrossMonomial, grossG δ * grossB (-(δ - (β - α))) from
    Fintype.sum_equiv (Equiv.subRight α) _ _ (fun δ => by
      simp [Equiv.subRight_apply, sub_sub])]
  rw [show (∑ x : GrossMonomial, grossH (x - α) * grossA (-(x - β))) =
      ∑ δ : GrossMonomial, grossH δ * grossA (-(δ - (β - α))) from
    Fintype.sum_equiv (Equiv.subRight α) _ _ (fun δ => by
      simp [Equiv.subRight_apply, sub_sub])]
  exact grossGH_kernel (β - α)

/-- X̄'_β commutes with all checks of the Gross code. -/
theorem logicalXBar'_commute_allChecks (β : GrossMonomial)
    (i : BBCheckIndex ℓ m) :
    PauliOp.PauliCommute (logicalXBar' β) (bbCheck grossA grossB i) := by
  match i with
  | Sum.inl γ => exact logicalXBar'_commute_xCheck β γ
  | Sum.inr γ => exact logicalXBar'_commute_zCheck β γ

/-! ## Z logical operators commute with checks -/

/-- Z̄_β commutes with all Z checks (both pure Z-type). -/
theorem logicalZBar_commute_zCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalZBar α) (bbCheckZ grossA grossB β) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, logicalZBar, pauliZBB, bbCheckZ]

/-- Z̄_β commutes with all X checks. -/
theorem logicalZBar_commute_xCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalZBar α) (bbCheckX grossA grossB β) := by
  classical
  rw [PauliOp.pauliCommute_comm]
  rw [PauliOp.PauliCommute, PauliOp.symplecticInner]
  simp only [logicalZBar, pauliZBB, bbCheckX, pauliXBB, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, bbShift, bbTranspose]
  rw [show (∑ x : GrossMonomial, grossA (x - β) * grossH (-(x - α))) =
      ∑ δ : GrossMonomial, grossA δ * grossH (-(δ - (α - β))) from
    Fintype.sum_equiv (Equiv.subRight β) _ _ (fun δ => by
      simp [Equiv.subRight_apply, sub_sub])]
  rw [show (∑ x : GrossMonomial, grossB (x - β) * grossG (-(x - α))) =
      ∑ δ : GrossMonomial, grossB δ * grossG (-(δ - (α - β))) from
    Fintype.sum_equiv (Equiv.subRight β) _ _ (fun δ => by
      simp [Equiv.subRight_apply, sub_sub])]
  exact grossHG_kernel_X (α - β)

/-- Z̄_β commutes with all checks. -/
theorem logicalZBar_commute_allChecks (β : GrossMonomial)
    (i : BBCheckIndex ℓ m) :
    PauliOp.PauliCommute (logicalZBar β) (bbCheck grossA grossB i) := by
  match i with
  | Sum.inl γ => exact logicalZBar_commute_xCheck β γ
  | Sum.inr γ => exact logicalZBar_commute_zCheck β γ

/-- Z̄'_α commutes with all Z checks (both pure Z-type). -/
theorem logicalZBar'_commute_zCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalZBar' α) (bbCheckZ grossA grossB β) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, logicalZBar', pauliZBB, bbCheckZ]

/-- Z̄'_α commutes with all X checks. -/
theorem logicalZBar'_commute_xCheck (α β : GrossMonomial) :
    PauliOp.PauliCommute (logicalZBar' α) (bbCheckX grossA grossB β) := by
  classical
  rw [PauliOp.pauliCommute_comm]
  rw [PauliOp.PauliCommute, PauliOp.symplecticInner]
  simp only [logicalZBar', pauliZBB, bbCheckX, pauliXBB, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add,
    Pi.zero_apply, zero_mul, bbShift, bbTranspose]
  rw [show (∑ x : GrossMonomial, grossB (x - β) * grossF (-(x - α))) =
      ∑ δ : GrossMonomial, grossB δ * grossF (-(δ - (α - β))) from
    Fintype.sum_equiv (Equiv.subRight β) _ _ (fun δ => by
      simp [Equiv.subRight_apply, sub_sub])]
  exact grossF_kernel_AT (α - β)

/-- Z̄'_α commutes with all checks. -/
theorem logicalZBar'_commute_allChecks (α : GrossMonomial)
    (i : BBCheckIndex ℓ m) :
    PauliOp.PauliCommute (logicalZBar' α) (bbCheck grossA grossB i) := by
  match i with
  | Sum.inl γ => exact logicalZBar'_commute_xCheck α γ
  | Sum.inr γ => exact logicalZBar'_commute_zCheck α γ

/-! ## Centralizer membership -/

/-- X̄_α is in the centralizer of the Gross code. -/
theorem logicalXBar_inCentralizer (α : GrossMonomial) :
    grossCode.inCentralizer (logicalXBar α) := by
  intro i; exact logicalXBar_commute_allChecks α i

/-- X̄'_β is in the centralizer of the Gross code. -/
theorem logicalXBar'_inCentralizer (β : GrossMonomial) :
    grossCode.inCentralizer (logicalXBar' β) := by
  intro i; exact logicalXBar'_commute_allChecks β i

/-- Z̄_β is in the centralizer of the Gross code. -/
theorem logicalZBar_inCentralizer (β : GrossMonomial) :
    grossCode.inCentralizer (logicalZBar β) := by
  intro i; exact logicalZBar_commute_allChecks β i

/-- Z̄'_α is in the centralizer of the Gross code. -/
theorem logicalZBar'_inCentralizer (α : GrossMonomial) :
    grossCode.inCentralizer (logicalZBar' α) := by
  intro i; exact logicalZBar'_commute_allChecks α i

/-! ## The X̄_α xVec characterization -/

@[simp] theorem logicalXBar_xVec_left (α γ : GrossMonomial) :
    (logicalXBar α).xVec (Sum.inl γ) = grossF (γ - α) := by
  simp [logicalXBar, pauliXBB, bbShift]

@[simp] theorem logicalXBar_xVec_right (α δ : GrossMonomial) :
    (logicalXBar α).xVec (Sum.inr δ) = 0 := by
  simp [logicalXBar, pauliXBB]

@[simp] theorem logicalXBar_zVec (α : GrossMonomial) :
    (logicalXBar α).zVec = 0 := logicalXBar_pure_X α

/-! ## Check weight properties -/

/-- The X-check support size is shift-invariant. -/
private lemma xCheck_support_shift_invariant (α : GrossMonomial) :
    (Finset.univ.filter (fun q : GrossQubit =>
      (bbCheckX grossA grossB α).xVec q ≠ 0 ∨
      (bbCheckX grossA grossB α).zVec q ≠ 0)).card =
    (Finset.univ.filter (fun q : GrossQubit =>
      (bbCheckX grossA grossB (0 : GrossMonomial)).xVec q ≠ 0 ∨
      (bbCheckX grossA grossB (0 : GrossMonomial)).zVec q ≠ 0)).card := by
  -- Both zVecs are zero, so the filter reduces to xVec q ≠ 0
  have hsimp : ∀ (β : GrossMonomial),
      (Finset.univ.filter (fun q : GrossQubit =>
        (bbCheckX grossA grossB β).xVec q ≠ 0 ∨
        (bbCheckX grossA grossB β).zVec q ≠ 0)) =
      (Finset.univ.filter (fun q : GrossQubit =>
        (bbCheckX grossA grossB β).xVec q ≠ 0)) := by
    intro β
    congr 1; ext q; simp [bbCheckX_zVec]
  rw [hsimp α, hsimp 0]
  -- Now define the bijection on the simplified filter
  let f : GrossQubit → GrossQubit := fun q => match q with
    | Sum.inl γ => Sum.inl (γ - α)
    | Sum.inr δ => Sum.inr (δ - α)
  have hf_inj : Function.Injective f := by
    intro a₁ a₂ h
    match a₁, a₂ with
    | Sum.inl _, Sum.inl _ => exact congrArg Sum.inl (sub_left_injective (Sum.inl.inj h))
    | Sum.inr _, Sum.inr _ => exact congrArg Sum.inr (sub_left_injective (Sum.inr.inj h))
    | Sum.inl _, Sum.inr _ => exact absurd h (by simp [f])
    | Sum.inr _, Sum.inl _ => exact absurd h (by simp [f])
  rw [show (Finset.univ.filter (fun q : GrossQubit =>
      (bbCheckX grossA grossB 0).xVec q ≠ 0)) =
    Finset.image f (Finset.univ.filter (fun q : GrossQubit =>
      (bbCheckX grossA grossB α).xVec q ≠ 0)) from by
    ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hq
      match q with
      | Sum.inl γ =>
        refine ⟨Sum.inl (γ + α), ?_, by simp [f, add_sub_cancel_right]⟩
        simp only [bbCheckX_xVec_left, add_sub_cancel_right, sub_zero] at hq ⊢
        exact hq
      | Sum.inr δ =>
        refine ⟨Sum.inr (δ + α), ?_, by simp [f, add_sub_cancel_right]⟩
        simp only [bbCheckX_xVec_right, add_sub_cancel_right, sub_zero] at hq ⊢
        exact hq
    · rintro ⟨a, ha, rfl⟩
      match a with
      | Sum.inl γ =>
        simp only [f, bbCheckX_xVec_left, sub_zero]
        simp only [bbCheckX_xVec_left] at ha
        exact ha
      | Sum.inr δ =>
        simp only [f, bbCheckX_xVec_right, sub_zero]
        simp only [bbCheckX_xVec_right] at ha
        exact ha]
  exact (Finset.card_image_of_injective _ hf_inj).symm

set_option maxHeartbeats 800000 in
/-- Each X check of the Gross code has weight 6. -/
theorem xCheck_weight (α : GrossMonomial) :
    (bbCheckX grossA grossB α).weight = 6 := by
  classical
  simp only [PauliOp.weight, PauliOp.support]
  rw [xCheck_support_shift_invariant α]
  native_decide

/-! ## Key property: insufficient Tanner graph expansion -/

/-- **Key property (Remark 20)**: X̄_α has weight 12, is pure X-type, and
    acts only on L qubits. Each L qubit participates in at most |supp(A)| = 3
    X-type checks, so the Tanner subgraph on X̄_α has limited expansion. -/
theorem logicalXBar_tanner_expansion_insufficient (α : GrossMonomial) :
    (logicalXBar α).weight = 12 ∧
    (logicalXBar α).zVec = 0 ∧
    (∀ δ : GrossMonomial, (logicalXBar α).xVec (Sum.inr δ) = 0) ∧
    (Finset.univ.filter (fun (γ : GrossMonomial) => grossA γ ≠ 0)).card = 3 := by
  exact ⟨logicalXBar_weight α, logicalXBar_pure_X α,
    logicalXBar_acts_only_on_L α, grossA_support_card⟩

/-! ## Summary -/

/-- The Gross code has 144 qubits and 144 checks. -/
theorem grossCode_parameters :
    grossCode.numQubits = 144 ∧ grossCode.numChecks = 144 :=
  ⟨grossCode_numQubits, grossCode_numChecks⟩

end GrossCode

end BivariateBicycle
