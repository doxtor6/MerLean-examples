import QEC1.Remarks.Rem_2_NotationPauliOperators
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.unusedDecidableInType false

/-!
# Remark 19: Bivariate Bicycle Code Notation

## Statement
The Bivariate Bicycle (BB) code construction uses cyclic permutation matrices and their
tensor products to define CSS codes on 2ℓm qubits.

## Main Results
- `BBMonomial`: the monomial group M = Z_ℓ × Z_m indexing qubits and checks
- `BBGroupAlgebra`: the group algebra F₂[x,y]/(x^ℓ-1, y^m-1) as ZMod 2-valued functions
- `BBQubit`: the qubit type for a BB code (L ⊕ R, each indexed by M)
- `bbConvolve`: polynomial multiplication in the group algebra (convolution)
- `bbTranspose`: the transpose operation A(x,y) ↦ A(x⁻¹,y⁻¹)
- `bbCheckX`, `bbCheckZ`: X-type and Z-type parity checks
- `BBCode`: the bivariate bicycle code as a stabilizer code
- `pauliXBB`, `pauliZBB`: the Pauli notation X(p,q) and Z(p,q)

## Corollaries
- `bbConvolve_comm`: convolution is commutative (the monomial group is abelian)
- `bbTranspose_involutive`: transpose is an involution
- `bbCode_numQubits`: the code has 2ℓm physical qubits
- `bbChecks_commute`: X and Z checks commute (CSS property)
-/

namespace BivariateBicycle

/-! ## The monomial group and group algebra -/

/-- The monomial group M = Z_ℓ × Z_m, representing monomials x^a y^b
    with a ∈ {0,...,ℓ-1} and b ∈ {0,...,m-1}. We use ZMod for the additive
    group structure (addition corresponds to monomial multiplication). -/
abbrev BBMonomial (ℓ m : ℕ) := ZMod ℓ × ZMod m

/-- The group algebra F₂[x,y]/(x^ℓ-1, y^m-1). An element is a function
    M → ZMod 2, where the value at (a,b) is the coefficient of x^a y^b. -/
abbrev BBGroupAlgebra (ℓ m : ℕ) := BBMonomial ℓ m → ZMod 2

variable {ℓ m : ℕ}

/-- The monomial x^a y^b as an element of the group algebra:
    the indicator function of the single element (a, b). -/
def bbMonomial (a : ZMod ℓ) (b : ZMod m) : BBGroupAlgebra ℓ m :=
  fun p => if p = (a, b) then 1 else 0

/-- The zero polynomial. -/
def bbZero : BBGroupAlgebra ℓ m := fun _ => 0

/-- The unit polynomial 1 = x^0 y^0. -/
def bbOne [NeZero ℓ] [NeZero m] : BBGroupAlgebra ℓ m := bbMonomial 0 0

/-- Addition in the group algebra (pointwise XOR, since coefficients are in ZMod 2). -/
def bbAdd (p q : BBGroupAlgebra ℓ m) : BBGroupAlgebra ℓ m := p + q

/-- Convolution (polynomial multiplication) in F₂[x,y]/(x^ℓ-1, y^m-1).
    (p * q)(γ) = Σ_{α} p(α) · q(γ - α) where subtraction is in Z_ℓ × Z_m.
    This corresponds to matrix multiplication of the associated circulant-like matrices. -/
noncomputable def bbConvolve [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (p q : BBGroupAlgebra ℓ m) : BBGroupAlgebra ℓ m :=
  fun γ => ∑ α : BBMonomial ℓ m, p α * q (γ - α)

/-- The support of a polynomial: the set of monomials with nonzero coefficient. -/
def bbSupport (p : BBGroupAlgebra ℓ m) : Set (BBMonomial ℓ m) :=
  { α | p α ≠ 0 }

/-- The support as a finset (decidable). -/
noncomputable def bbSupportFinset [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    [DecidableEq (ZMod ℓ)] [DecidableEq (ZMod m)]
    (p : BBGroupAlgebra ℓ m) : Finset (BBMonomial ℓ m) :=
  Finset.univ.filter (fun α => p α ≠ 0)

/-- The transpose operation: A^T(x,y) = A(x⁻¹, y⁻¹).
    Since x^{-1} = x^{ℓ-1} and y^{-1} = y^{m-1} in the quotient ring,
    this maps the coefficient of x^a y^b to x^{-a} y^{-b}. -/
def bbTranspose (p : BBGroupAlgebra ℓ m) : BBGroupAlgebra ℓ m :=
  fun α => p (-α)

/-! ## Transpose properties -/

@[simp]
theorem bbTranspose_involutive (p : BBGroupAlgebra ℓ m) :
    bbTranspose (bbTranspose p) = p := by
  ext α
  simp [bbTranspose, neg_neg]

theorem bbTranspose_bbMonomial [NeZero ℓ] [NeZero m] (a : ZMod ℓ) (b : ZMod m) :
    bbTranspose (bbMonomial a b) = bbMonomial (-a) (-b) := by
  ext ⟨c, d⟩
  simp only [bbTranspose, bbMonomial, Prod.neg_mk, Prod.mk.injEq]
  simp only [neg_eq_iff_eq_neg]

theorem bbTranspose_add (p q : BBGroupAlgebra ℓ m) :
    bbTranspose (p + q) = bbTranspose p + bbTranspose q := by
  ext α; simp [bbTranspose, Pi.add_apply]

/-! ## Convolution properties -/

theorem bbConvolve_comm [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (p q : BBGroupAlgebra ℓ m) :
    bbConvolve p q = bbConvolve q p := by
  ext γ
  simp only [bbConvolve]
  -- Reindex LHS with β = γ - α (α = γ - β)
  have : (∑ α, p α * q (γ - α)) = ∑ β, p (γ - β) * q β :=
    Fintype.sum_equiv (Equiv.subLeft γ) _ _ (fun β => by
      simp only [Equiv.subLeft_apply]; congr 1; congr 1; abel)
  rw [this]
  congr 1; ext β; exact mul_comm _ _

noncomputable instance bbGroupAlgebraAddCommMonoid [Fintype (ZMod ℓ)] [Fintype (ZMod m)] :
    AddCommMonoid (BBGroupAlgebra ℓ m) := Pi.addCommMonoid

/-! ## The BB qubit type -/

/-- The qubit type for a BB code: Left (L) qubits and Right (R) qubits,
    each indexed by the monomial group M = Z_ℓ × Z_m. -/
abbrev BBQubit (ℓ m : ℕ) := BBMonomial ℓ m ⊕ BBMonomial ℓ m

/-- The number of physical qubits in a BB code is 2ℓm. -/
theorem bbCode_numQubits [NeZero ℓ] [NeZero m] :
    Fintype.card (BBQubit ℓ m) = 2 * (ℓ * m) := by
  simp [BBQubit, BBMonomial, Fintype.card_sum, Fintype.card_prod, ZMod.card, two_mul]

/-! ## Pauli operators on BB codes -/

/-- The X-type Pauli operator X(p, q) on a BB code.
    Acts with X on L qubit γ iff p(γ) = 1, and on R qubit δ iff q(δ) = 1.
    This is a pure X-type operator (zVec = 0). -/
def pauliXBB (p q : BBGroupAlgebra ℓ m) : PauliOp (BBQubit ℓ m) where
  xVec := Sum.elim p q
  zVec := 0

/-- The Z-type Pauli operator Z(p, q) on a BB code.
    Acts with Z on L qubit γ iff p(γ) = 1, and on R qubit δ iff q(δ) = 1.
    This is a pure Z-type operator (xVec = 0). -/
def pauliZBB (p q : BBGroupAlgebra ℓ m) : PauliOp (BBQubit ℓ m) where
  xVec := 0
  zVec := Sum.elim p q

@[simp]
theorem pauliXBB_xVec_left (p q : BBGroupAlgebra ℓ m) (γ : BBMonomial ℓ m) :
    (pauliXBB p q).xVec (Sum.inl γ) = p γ := rfl

@[simp]
theorem pauliXBB_xVec_right (p q : BBGroupAlgebra ℓ m) (δ : BBMonomial ℓ m) :
    (pauliXBB p q).xVec (Sum.inr δ) = q δ := rfl

@[simp]
theorem pauliXBB_zVec (p q : BBGroupAlgebra ℓ m) :
    (pauliXBB p q).zVec = 0 := rfl

@[simp]
theorem pauliZBB_xVec (p q : BBGroupAlgebra ℓ m) :
    (pauliZBB p q).xVec = 0 := rfl

@[simp]
theorem pauliZBB_zVec_left (p q : BBGroupAlgebra ℓ m) (γ : BBMonomial ℓ m) :
    (pauliZBB p q).zVec (Sum.inl γ) = p γ := rfl

@[simp]
theorem pauliZBB_zVec_right (p q : BBGroupAlgebra ℓ m) (δ : BBMonomial ℓ m) :
    (pauliZBB p q).zVec (Sum.inr δ) = q δ := rfl

/-! ## The shifted polynomial: α-shift of p is p(· - α), i.e., convolution with δ_α -/

/-- Left-shift a polynomial by monomial α: (shift_α p)(γ) = p(γ - α).
    This corresponds to multiplication by x^a y^b in the group algebra. -/
def bbShift (α : BBMonomial ℓ m) (p : BBGroupAlgebra ℓ m) : BBGroupAlgebra ℓ m :=
  fun γ => p (γ - α)

theorem bbShift_zero (p : BBGroupAlgebra ℓ m) [NeZero ℓ] [NeZero m] :
    bbShift (0 : BBMonomial ℓ m) p = p := by
  ext γ; simp [bbShift]

theorem bbShift_add (α β : BBMonomial ℓ m) (p : BBGroupAlgebra ℓ m) :
    bbShift α (bbShift β p) = bbShift (α + β) p := by
  ext γ; simp [bbShift, sub_sub]

/-! ## X-type and Z-type checks of the BB code -/

/-- The X-type check indexed by α ∈ M. Its X-support on L qubits is the support of αA,
    and on R qubits is the support of αB. Using the shift representation:
    check (α, X) = X(shift_α A, shift_α B). -/
def bbCheckX [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) : PauliOp (BBQubit ℓ m) :=
  pauliXBB (bbShift α A) (bbShift α B)

/-- The Z-type check indexed by β ∈ M. Its Z-support on L qubits is the support of βB^T,
    and on R qubits is the support of βA^T. Using the shift representation:
    check (β, Z) = Z(shift_β B^T, shift_β A^T). -/
def bbCheckZ [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) : PauliOp (BBQubit ℓ m) :=
  pauliZBB (bbShift β (bbTranspose B)) (bbShift β (bbTranspose A))

@[simp]
theorem bbCheckX_xVec_left [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) (γ : BBMonomial ℓ m) :
    (bbCheckX A B α).xVec (Sum.inl γ) = A (γ - α) := rfl

@[simp]
theorem bbCheckX_xVec_right [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) (δ : BBMonomial ℓ m) :
    (bbCheckX A B α).xVec (Sum.inr δ) = B (δ - α) := rfl

@[simp]
theorem bbCheckX_zVec [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) :
    (bbCheckX A B α).zVec = 0 := rfl

@[simp]
theorem bbCheckZ_xVec [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) :
    (bbCheckZ A B β).xVec = 0 := rfl

@[simp]
theorem bbCheckZ_zVec_left [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) (γ : BBMonomial ℓ m) :
    (bbCheckZ A B β).zVec (Sum.inl γ) = B (-(γ - β)) := rfl

@[simp]
theorem bbCheckZ_zVec_right [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) (δ : BBMonomial ℓ m) :
    (bbCheckZ A B β).zVec (Sum.inr δ) = A (-(δ - β)) := rfl

/-! ## X checks are pure X-type, Z checks are pure Z-type -/

theorem bbCheckX_pure_X [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) :
    (bbCheckX A B α).zVec = 0 := rfl

theorem bbCheckZ_pure_Z [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) :
    (bbCheckZ A B β).xVec = 0 := rfl

/-! ## CSS commutation: X checks commute with Z checks -/

/-- X checks commute with each other (both pure X, so symplectic inner product = 0). -/
theorem bbCheckX_commute [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α₁ α₂ : BBMonomial ℓ m) :
    PauliOp.PauliCommute (bbCheckX A B α₁) (bbCheckX A B α₂) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, bbCheckX_zVec]

/-- Z checks commute with each other (both pure Z, so symplectic inner product = 0). -/
theorem bbCheckZ_commute [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β₁ β₂ : BBMonomial ℓ m) :
    PauliOp.PauliCommute (bbCheckZ A B β₁) (bbCheckZ A B β₂) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, bbCheckZ_xVec]

/-- The CSS commutation condition: X check α commutes with Z check β iff
    Σ_γ A(γ-α)·B(-γ+β) + Σ_δ B(δ-α)·A(-δ+β) = 0 in ZMod 2.
    This is the condition H_X · H_Z^T = 0, equivalently A·B^T = B·A^T. -/
theorem bbCheckXZ_commute_iff [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α β : BBMonomial ℓ m) :
    PauliOp.PauliCommute (bbCheckX A B α) (bbCheckZ A B β) ↔
    (∑ γ : BBMonomial ℓ m, A (γ - α) * B (-(γ - β)) +
     ∑ δ : BBMonomial ℓ m, B (δ - α) * A (-(δ - β))) = 0 := by
  classical
  simp only [PauliOp.PauliCommute, PauliOp.symplecticInner]
  constructor <;> intro h <;> convert h using 1 <;>
  · simp only [Fintype.sum_sum_type]
    congr 1 <;> congr 1 <;> ext v <;>
    simp [bbCheckX, bbCheckZ, pauliXBB, pauliZBB, bbShift, bbTranspose]

/-! ## The CSS condition: AB^T = BA^T (in the group algebra) -/

/-- The CSS condition for a BB code: A * B^T = B * A^T as convolutions.
    This is the necessary and sufficient condition for all X and Z checks to commute. -/
def BBCSSCondition [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) : Prop :=
  bbConvolve A (bbTranspose B) = bbConvolve B (bbTranspose A)

/-- Under the CSS condition, all X and Z checks commute.
    In fact, for BB codes over abelian groups the commutation is automatic:
    each sum equals the convolution bbConvolve evaluated at β-α, and by
    commutativity of convolution their sum vanishes in characteristic 2. -/
theorem bbChecksXZ_commute_of_css [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (_hcss : BBCSSCondition A B)
    (α β : BBMonomial ℓ m) :
    PauliOp.PauliCommute (bbCheckX A B α) (bbCheckZ A B β) := by
  classical
  rw [bbCheckXZ_commute_iff]
  -- We need: Σ_γ A(γ-α)·B(-(γ-β)) + Σ_δ B(δ-α)·A(-(δ-β)) = 0
  -- Each sum equals bbConvolve at β-α: reindex via δ = γ-α, use B(-(γ-β)) = B((β-α)-δ)
  have lhs_eq : (∑ γ : BBMonomial ℓ m, A (γ - α) * B (-(γ - β))) =
      bbConvolve A B (β - α) := by
    simp only [bbConvolve]
    symm
    apply Fintype.sum_equiv (Equiv.addRight α)
    intro δ; simp only [Equiv.coe_addRight]
    congr 1 <;> congr 1 <;> abel
  have rhs_eq : (∑ δ : BBMonomial ℓ m, B (δ - α) * A (-(δ - β))) =
      bbConvolve B A (β - α) := by
    simp only [bbConvolve]
    symm
    apply Fintype.sum_equiv (Equiv.addRight α)
    intro δ; simp only [Equiv.coe_addRight]
    congr 1 <;> congr 1 <;> abel
  rw [lhs_eq, rhs_eq, bbConvolve_comm A B]
  exact CharTwo.add_self_eq_zero _

/-! ## The BB code check index and the full stabilizer code -/

/-- Check index for a BB code: X checks indexed by M, Z checks indexed by M. -/
abbrev BBCheckIndex (ℓ m : ℕ) := BBMonomial ℓ m ⊕ BBMonomial ℓ m

/-- The number of checks in a BB code is 2ℓm. -/
theorem bbCode_numChecks [NeZero ℓ] [NeZero m] :
    Fintype.card (BBCheckIndex ℓ m) = 2 * (ℓ * m) := by
  simp [BBCheckIndex, BBMonomial, Fintype.card_sum, Fintype.card_prod, ZMod.card, two_mul]

/-- The check map for a BB code: X checks on the left, Z checks on the right. -/
def bbCheck [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) : BBCheckIndex ℓ m → PauliOp (BBQubit ℓ m)
  | Sum.inl α => bbCheckX A B α
  | Sum.inr β => bbCheckZ A B β

/-- Under the CSS condition, all checks in a BB code pairwise commute. -/
theorem bbChecks_commute [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (hcss : BBCSSCondition A B)
    (i j : BBCheckIndex ℓ m) :
    PauliOp.PauliCommute (bbCheck A B i) (bbCheck A B j) := by
  match i, j with
  | Sum.inl α₁, Sum.inl α₂ =>
    exact bbCheckX_commute A B α₁ α₂
  | Sum.inl α, Sum.inr β =>
    exact bbChecksXZ_commute_of_css A B hcss α β
  | Sum.inr β, Sum.inl α =>
    rw [PauliOp.pauliCommute_comm]
    exact bbChecksXZ_commute_of_css A B hcss α β
  | Sum.inr β₁, Sum.inr β₂ =>
    exact bbCheckZ_commute A B β₁ β₂

/-- A BB code forms a valid stabilizer code under the CSS condition. -/
noncomputable def BBCode [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    [DecidableEq (ZMod ℓ)] [DecidableEq (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (hcss : BBCSSCondition A B) :
    StabilizerCode (BBQubit ℓ m) where
  I := BBCheckIndex ℓ m
  check := bbCheck A B
  checks_commute := bbChecks_commute A B hcss

/-! ## Properties of the cyclic shift operators x and y -/

/-- The x-shift operator: multiplication by x = x^1 y^0 in the group algebra.
    Maps coefficient at (a, b) to (a-1, b), i.e., shifts the first coordinate. -/
def xShift [NeZero ℓ] [NeZero m] : BBMonomial ℓ m := (1, 0)

/-- The y-shift operator: multiplication by y = x^0 y^1 in the group algebra.
    Maps coefficient at (a, b) to (a, b-1), i.e., shifts the second coordinate. -/
def yShift [NeZero ℓ] [NeZero m] : BBMonomial ℓ m := (0, 1)

/-- x^ℓ = 1: shifting by ℓ in the first coordinate is the identity (mod ℓ). -/
@[simp]
theorem xShift_pow_ℓ [NeZero ℓ] [NeZero m] :
    (ℓ : ℕ) • xShift (ℓ := ℓ) (m := m) = 0 := by
  simp [xShift, Prod.smul_mk, smul_eq_mul, ZMod.natCast_self, mul_zero]

/-- y^m = 1: shifting by m in the second coordinate is the identity (mod m). -/
@[simp]
theorem yShift_pow_m [NeZero ℓ] [NeZero m] :
    (m : ℕ) • yShift (ℓ := ℓ) (m := m) = 0 := by
  simp [yShift, Prod.smul_mk, smul_eq_mul, ZMod.natCast_self, mul_zero]

/-- x and y commute: the monomial group is abelian. -/
theorem xShift_yShift_comm [NeZero ℓ] [NeZero m] :
    xShift (ℓ := ℓ) (m := m) + yShift = yShift + xShift := by
  simp [xShift, yShift, Prod.ext_iff, add_comm]

/-! ## Transpose as variable inversion -/

/-- The transpose satisfies A^T(γ) = A(-γ), which corresponds to
    substituting x → x⁻¹ = x^{ℓ-1} and y → y⁻¹ = y^{m-1}. -/
theorem bbTranspose_eq_neg (p : BBGroupAlgebra ℓ m) (γ : BBMonomial ℓ m) :
    bbTranspose p γ = p (-γ) := rfl

/-- Transpose of a monomial: (x^a y^b)^T = x^{-a} y^{-b}. -/
theorem bbTranspose_monomial_neg [NeZero ℓ] [NeZero m]
    (a : ZMod ℓ) (b : ZMod m) (γ : BBMonomial ℓ m) :
    bbTranspose (bbMonomial a b) γ = bbMonomial (-a) (-b) γ := by
  simp only [bbTranspose, bbMonomial]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2
    obtain ⟨ha, hb⟩ := Prod.mk.inj h1
    exact Prod.ext (by rw [← ha, neg_neg]) (by rw [← hb, neg_neg])
  · exfalso; apply h1
    obtain ⟨ha, hb⟩ := Prod.mk.inj h2
    exact Prod.ext (by simp [ha]) (by simp [hb])
  · rfl

/-! ## Convolution distributes over transposition -/

theorem bbConvolve_transpose [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (p q : BBGroupAlgebra ℓ m) :
    bbTranspose (bbConvolve p q) = bbConvolve (bbTranspose q) (bbTranspose p) := by
  ext γ
  simp only [bbTranspose, bbConvolve]
  -- LHS: ∑ α, p(α) * q(-γ - α)
  -- RHS: ∑ α, q(-α) * p(-γ + α) = ∑ α, q(-α) * p(-(γ - α))
  -- Reindex LHS: β = -γ - α (α = -γ - β) gives ∑ β, p(-γ-β) * q(β)
  have lhs_eq : (∑ α, p α * q (-γ - α)) = ∑ β, p (-γ - β) * q β :=
    Fintype.sum_equiv (Equiv.subLeft (-γ)) _ _ (fun β => by
      simp only [Equiv.subLeft_apply]; congr 1; congr 1; abel)
  -- Reindex RHS: β = -α (α = -β) gives ∑ β, q(β) * p(-γ - β)
  have rhs_eq : (∑ α, q (-α) * p (-(γ - α))) = ∑ β, q β * p (-γ - β) :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun β => by
      simp only [Equiv.neg_apply, neg_neg]; congr 1; congr 1; abel)
  rw [lhs_eq, rhs_eq]
  congr 1; ext β; exact mul_comm _ _

/-! ## The labeling convention -/

/-- Left qubit labeled by γ ∈ M. -/
abbrev leftQubit (γ : BBMonomial ℓ m) : BBQubit ℓ m := Sum.inl γ

/-- Right qubit labeled by δ ∈ M. -/
abbrev rightQubit (δ : BBMonomial ℓ m) : BBQubit ℓ m := Sum.inr δ

/-- X check labeled by α ∈ M. -/
abbrev xCheckIndex (α : BBMonomial ℓ m) : BBCheckIndex ℓ m := Sum.inl α

/-- Z check labeled by β ∈ M. -/
abbrev zCheckIndex (β : BBMonomial ℓ m) : BBCheckIndex ℓ m := Sum.inr β

/-- The check at index (α, X) is the X check for α. -/
@[simp]
theorem bbCheck_xCheck [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) :
    bbCheck A B (xCheckIndex α) = bbCheckX A B α := rfl

/-- The check at index (β, Z) is the Z check for β. -/
@[simp]
theorem bbCheck_zCheck [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) :
    bbCheck A B (zCheckIndex β) = bbCheckZ A B β := rfl

/-! ## The CSS condition is equivalent to AB^T = BA^T -/

/-- The CSS condition states that A * B^T = B * A^T in the group algebra.
    This ensures the parity check matrices H_X and H_Z satisfy H_X · H_Z^T = 0.
    Equivalently: for every γ ∈ M,
    Σ_α A(α) · B(α - γ) = Σ_α B(α) · A(α - γ). -/
theorem bbCSSCondition_iff [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) :
    BBCSSCondition A B ↔
    ∀ γ : BBMonomial ℓ m,
      (∑ α : BBMonomial ℓ m, A α * B (α - γ)) =
      (∑ α : BBMonomial ℓ m, B α * A (α - γ)) := by
  simp only [BBCSSCondition, bbConvolve, bbTranspose, funext_iff]
  constructor
  · intro h γ
    have := h γ
    convert this using 1 <;>
    · congr 1; ext α; congr 1; abel
  · intro h γ
    have := h γ
    convert this using 1 <;>
    · congr 1; ext α; congr 1; abel

/-! ## Pauli notation properties -/

/-- X(p, q) is pure X-type. -/
theorem pauliXBB_pure_X (p q : BBGroupAlgebra ℓ m) :
    (pauliXBB p q).zVec = 0 := rfl

/-- Z(p, q) is pure Z-type. -/
theorem pauliZBB_pure_Z (p q : BBGroupAlgebra ℓ m) :
    (pauliZBB p q).xVec = 0 := rfl

/-- X(0, 0) is the identity operator. -/
@[simp]
theorem pauliXBB_zero : pauliXBB (0 : BBGroupAlgebra ℓ m) 0 = 1 := by
  ext q
  · match q with
    | Sum.inl _ => simp [pauliXBB]
    | Sum.inr _ => simp [pauliXBB]
  · simp [pauliXBB]

/-- Z(0, 0) is the identity operator. -/
@[simp]
theorem pauliZBB_zero : pauliZBB (0 : BBGroupAlgebra ℓ m) 0 = 1 := by
  ext q
  · simp [pauliZBB]
  · match q with
    | Sum.inl _ => simp [pauliZBB]
    | Sum.inr _ => simp [pauliZBB]

/-- X(p₁, q₁) · X(p₂, q₂) = X(p₁ + p₂, q₁ + q₂) as Pauli operators
    (since X-type operators multiply by adding their binary vectors). -/
theorem pauliXBB_mul (p₁ q₁ p₂ q₂ : BBGroupAlgebra ℓ m) :
    pauliXBB p₁ q₁ * pauliXBB p₂ q₂ = pauliXBB (p₁ + p₂) (q₁ + q₂) := by
  ext v
  · simp only [PauliOp.mul_xVec, Pi.add_apply]
    match v with
    | Sum.inl γ => simp [pauliXBB]
    | Sum.inr δ => simp [pauliXBB]
  · simp only [PauliOp.mul_zVec, Pi.add_apply]
    match v with
    | Sum.inl γ => simp [pauliXBB]
    | Sum.inr δ => simp [pauliXBB]

/-- Z(p₁, q₁) · Z(p₂, q₂) = Z(p₁ + p₂, q₁ + q₂). -/
theorem pauliZBB_mul (p₁ q₁ p₂ q₂ : BBGroupAlgebra ℓ m) :
    pauliZBB p₁ q₁ * pauliZBB p₂ q₂ = pauliZBB (p₁ + p₂) (q₁ + q₂) := by
  ext v
  · simp only [PauliOp.mul_xVec, Pi.add_apply]
    match v with
    | Sum.inl γ => simp [pauliZBB]
    | Sum.inr δ => simp [pauliZBB]
  · simp only [PauliOp.mul_zVec, Pi.add_apply]
    match v with
    | Sum.inl γ => simp [pauliZBB]
    | Sum.inr δ => simp [pauliZBB]

/-- Two X-type Pauli operators always commute. -/
theorem pauliXBB_pauliXBB_commute [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (p₁ q₁ p₂ q₂ : BBGroupAlgebra ℓ m) :
    PauliOp.PauliCommute (pauliXBB p₁ q₁) (pauliXBB p₂ q₂) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, pauliXBB]

/-- Two Z-type Pauli operators always commute. -/
theorem pauliZBB_pauliZBB_commute [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (p₁ q₁ p₂ q₂ : BBGroupAlgebra ℓ m) :
    PauliOp.PauliCommute (pauliZBB p₁ q₁) (pauliZBB p₂ q₂) := by
  classical
  simp [PauliOp.PauliCommute, PauliOp.symplecticInner, pauliZBB]

/-- The symplectic inner product of X(p₁,q₁) and Z(p₂,q₂) equals
    Σ_γ p₁(γ)·p₂(γ) + Σ_δ q₁(δ)·q₂(δ), which is ⟨p₁,p₂⟩ + ⟨q₁,q₂⟩
    where ⟨·,·⟩ is the standard inner product in ZMod 2. -/
theorem symplecticInner_pauliXBB_pauliZBB [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (p₁ q₁ p₂ q₂ : BBGroupAlgebra ℓ m) :
    PauliOp.symplecticInner (pauliXBB p₁ q₁) (pauliZBB p₂ q₂) =
    ∑ γ : BBMonomial ℓ m, p₁ γ * p₂ γ +
    ∑ δ : BBMonomial ℓ m, q₁ δ * q₂ δ := by
  classical
  simp only [PauliOp.symplecticInner, pauliXBB, pauliZBB, Pi.zero_apply, mul_zero,
    zero_mul, add_zero, zero_add]
  rw [show (∑ v : BBQubit ℓ m, Sum.elim p₁ q₁ v * Sum.elim p₂ q₂ v) =
    (∑ a : BBMonomial ℓ m, Sum.elim p₁ q₁ (Sum.inl a) * Sum.elim p₂ q₂ (Sum.inl a)) +
    (∑ b : BBMonomial ℓ m, Sum.elim p₁ q₁ (Sum.inr b) * Sum.elim p₂ q₂ (Sum.inr b))
    from by simp [Fintype.sum_sum_type]]
  simp [Sum.elim_inl, Sum.elim_inr]

/-! ## X check is exactly X(shift_α A, shift_α B) -/

theorem bbCheckX_eq_pauliXBB [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) :
    bbCheckX A B α = pauliXBB (bbShift α A) (bbShift α B) := rfl

/-- Z check is exactly Z(shift_β B^T, shift_β A^T). -/
theorem bbCheckZ_eq_pauliZBB [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) :
    bbCheckZ A B β = pauliZBB (bbShift β (bbTranspose B)) (bbShift β (bbTranspose A)) := rfl

/-! ## Monomial group cardinality -/

/-- The monomial group has ℓm elements. -/
theorem bbMonomial_card [NeZero ℓ] [NeZero m] :
    Fintype.card (BBMonomial ℓ m) = ℓ * m := by
  simp [BBMonomial, Fintype.card_prod, ZMod.card]

/-! ## Check acts on qubit characterization -/

/-- X check (α, X) acts on L qubit γ iff A(γ - α) = 1,
    i.e., γ is in the support of the shifted polynomial αA. -/
theorem bbCheckX_acts_on_left [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α γ : BBMonomial ℓ m) :
    (bbCheckX A B α).xVec (Sum.inl γ) = A (γ - α) := rfl

/-- X check (α, X) acts on R qubit δ iff B(δ - α) = 1,
    i.e., δ is in the support of the shifted polynomial αB. -/
theorem bbCheckX_acts_on_right [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α δ : BBMonomial ℓ m) :
    (bbCheckX A B α).xVec (Sum.inr δ) = B (δ - α) := rfl

/-- Z check (β, Z) acts on L qubit γ iff B^T(γ - β) = B(β - γ) = 1,
    i.e., γ is in the support of the shifted polynomial β B^T. -/
theorem bbCheckZ_acts_on_left [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β γ : BBMonomial ℓ m) :
    (bbCheckZ A B β).zVec (Sum.inl γ) = B (β - γ) := by
  simp [bbCheckZ, pauliZBB, bbShift, bbTranspose, neg_sub]

/-- Z check (β, Z) acts on R qubit δ iff A^T(δ - β) = A(β - δ) = 1,
    i.e., δ is in the support of the shifted polynomial β A^T. -/
theorem bbCheckZ_acts_on_right [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β δ : BBMonomial ℓ m) :
    (bbCheckZ A B β).zVec (Sum.inr δ) = A (β - δ) := by
  simp [bbCheckZ, pauliZBB, bbShift, bbTranspose, neg_sub]

/-! ## Self-inverse properties -/

/-- X checks are self-inverse: (α, X) · (α, X) = I. -/
theorem bbCheckX_mul_self [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (α : BBMonomial ℓ m) :
    bbCheckX A B α * bbCheckX A B α = 1 := by
  rw [bbCheckX_eq_pauliXBB, pauliXBB_mul]
  ext q
  · simp only [PauliOp.one_xVec, Pi.zero_apply]
    match q with
    | Sum.inl γ => simp [pauliXBB, CharTwo.add_self_eq_zero]
    | Sum.inr δ => simp [pauliXBB, CharTwo.add_self_eq_zero]
  · simp [pauliXBB]

/-- Z checks are self-inverse: (β, Z) · (β, Z) = I. -/
theorem bbCheckZ_mul_self [Fintype (ZMod ℓ)] [Fintype (ZMod m)]
    (A B : BBGroupAlgebra ℓ m) (β : BBMonomial ℓ m) :
    bbCheckZ A B β * bbCheckZ A B β = 1 := by
  rw [bbCheckZ_eq_pauliZBB, pauliZBB_mul]
  ext q
  · simp [pauliZBB]
  · simp only [PauliOp.one_zVec, Pi.zero_apply]
    match q with
    | Sum.inl γ => simp [pauliZBB, CharTwo.add_self_eq_zero]
    | Sum.inr δ => simp [pauliZBB, CharTwo.add_self_eq_zero]

end BivariateBicycle
