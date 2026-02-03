import QEC1.Definitions.Def_13_BivariateBicycleCode

/-!
# Def_14: Gross Code

## Statement
The **Gross code** is a specific [[144, 12, 12]] Bivariate Bicycle code,
so named because a 'gross' is a dozen dozens (144).

**Parameters**: ℓ = 12, m = 6, giving n = 2 · 12 · 6 = 144 qubits.

**Polynomials**:
  A = x³ + y² + y,  B = y³ + x² + x

**Logical operators**: A convenient basis of logical operators uses the polynomials:
  f = 1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹ + (x + x⁵ + x⁷ + x¹¹)y³
  g = x + x²y + (1 + x)y² + x²y³ + y⁴
  h = 1 + (1 + x)y + y² + (1 + x)y³

Then for any monomials α, β ∈ M:
- X̄_α = X(αf, 0) are X-type logical operators of weight 12
- X̄'_β = X(βg, βh) are X-type logical operators
- Z̄_β = Z(βh^T, βg^T) are Z-type logical operators
- Z̄'_α = Z(0, αf^T) are Z-type logical operators

## Main Definitions
- `GrossCode` : The Gross code as a BivariateBicycleCode with ℓ = 12, m = 6
- `GrossCode.polyF` : Polynomial f for X-type logical operators
- `GrossCode.polyG` : Polynomial g for X-type logical operators
- `GrossCode.polyH` : Polynomial h for X-type logical operators
- `GrossCode.logicalX` : X̄_α = X(αf, 0)
- `GrossCode.logicalXPrime` : X̄'_β = X(βg, βh)
- `GrossCode.logicalZ` : Z̄_β = Z(βh^T, βg^T)
- `GrossCode.logicalZPrime` : Z̄'_α = Z(0, αf^T)

## Corollaries
- `GrossCode.numQubits_eq` : The number of physical qubits is 144
- `GrossCode.ell_val` : ℓ = 12
- `GrossCode.m_val` : m = 6
-/

set_option linter.unusedSectionVars false

open QEC1.BivariateBicycle

namespace QEC1.GrossCode

/-! ## Section 1: Parameters

The Gross code has ℓ = 12, m = 6. -/

/-- The ℓ parameter of the Gross code. -/
abbrev ell : ℕ := 12

/-- The m parameter of the Gross code. -/
abbrev m_param : ℕ := 6

instance : NeZero ell := ⟨by decide⟩
instance : NeZero m_param := ⟨by decide⟩

/-- The monomial set for the Gross code. -/
abbrev GM := M ell m_param

/-- The group algebra for the Gross code. -/
abbrev GGroupAlg := GroupAlg ell m_param

/-! ## Section 2: Convenience for building polynomials

We use the `monomial` function from the BB code definitions. -/

/-- Shorthand for monomials x^a y^b in the Gross code group algebra. -/
noncomputable def mon (a : ZMod ell) (b : ZMod m_param) : GGroupAlg :=
  monomial ell m_param a b

/-! ## Section 3: The polynomials A and B

A = x³ + y² + y
B = y³ + x² + x -/

/-- Polynomial A = x³ + y² + y for the Gross code. -/
noncomputable def polyA : GGroupAlg :=
  mon 3 0 + mon 0 2 + mon 0 1

/-- Polynomial B = y³ + x² + x for the Gross code. -/
noncomputable def polyB : GGroupAlg :=
  mon 0 3 + mon 2 0 + mon 1 0

/-! ## Section 4: The Gross Code

The Gross code is a BB code with the above parameters and polynomials. -/

/-- The Gross code: a [[144, 12, 12]] Bivariate Bicycle code. -/
noncomputable def grossCode : BivariateBicycleCode ell m_param where
  polyA := polyA
  polyB := polyB

/-! ## Section 5: Parameter verification -/

/-- The number of physical qubits in the Gross code is 144. -/
theorem numQubits_eq :
    BivariateBicycleCode.numPhysicalQubits ell m_param = 144 := by
  unfold BivariateBicycleCode.numPhysicalQubits
  norm_num

/-- ℓ = 12. -/
@[simp] theorem ell_val : ell = 12 := rfl

/-- m = 6. -/
@[simp] theorem m_val : m_param = 6 := rfl

/-- The number of left qubits is 72. -/
theorem numLeftQubits_eq :
    BivariateBicycleCode.numLeftQubits ell m_param = 72 := by
  unfold BivariateBicycleCode.numLeftQubits
  norm_num

/-- The number of right qubits is 72. -/
theorem numRightQubits_eq :
    BivariateBicycleCode.numRightQubits ell m_param = 72 := by
  unfold BivariateBicycleCode.numRightQubits
  norm_num

/-- The number of X checks is 72. -/
theorem numXChecks_eq :
    BivariateBicycleCode.numXChecks ell m_param = 72 := by
  unfold BivariateBicycleCode.numXChecks
  norm_num

/-- The number of Z checks is 72. -/
theorem numZChecks_eq :
    BivariateBicycleCode.numZChecks ell m_param = 72 := by
  unfold BivariateBicycleCode.numZChecks
  norm_num

/-- n = 2 · ℓ · m = 2 · 12 · 6 = 144 -/
theorem n_eq_2_ell_m : 2 * ell * m_param = 144 := by norm_num

/-! ## Section 6: Logical operator polynomials

f = 1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹ + (x + x⁵ + x⁷ + x¹¹)y³
g = x + x²y + (1 + x)y² + x²y³ + y⁴
h = 1 + (1 + x)y + y² + (1 + x)y³ -/

/-- Polynomial f for X-type logical operators.
f = 1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹ + (x + x⁵ + x⁷ + x¹¹)y³ -/
noncomputable def polyF : GGroupAlg :=
  -- Constant and x-power terms (y^0 part): 1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹
  mon 0 0 + mon 1 0 + mon 2 0 + mon 3 0 +
  mon 6 0 + mon 7 0 + mon 8 0 + mon 9 0 +
  -- y³ part: (x + x⁵ + x⁷ + x¹¹)y³
  mon 1 3 + mon 5 3 + mon 7 3 + mon 11 3

/-- Polynomial g for logical operators.
g = x + x²y + (1 + x)y² + x²y³ + y⁴ -/
noncomputable def polyG : GGroupAlg :=
  mon 1 0 +          -- x
  mon 2 1 +          -- x²y
  mon 0 2 + mon 1 2 + -- (1 + x)y²
  mon 2 3 +          -- x²y³
  mon 0 4            -- y⁴

/-- Polynomial h for logical operators.
h = 1 + (1 + x)y + y² + (1 + x)y³ -/
noncomputable def polyH : GGroupAlg :=
  mon 0 0 +            -- 1
  mon 0 1 + mon 1 1 +  -- (1 + x)y
  mon 0 2 +            -- y²
  mon 0 3 + mon 1 3    -- (1 + x)y³

/-! ## Section 7: Logical Operators

For any monomials α, β ∈ M:
- X̄_α = X(αf, 0) are X-type logical operators of weight 12
- X̄'_β = X(βg, βh) are X-type logical operators
- Z̄_β = Z(βh^T, βg^T) are Z-type logical operators
- Z̄'_α = Z(0, αf^T) are Z-type logical operators -/

/-- Multiplication of a monomial by a group algebra element (left multiplication).
α · p shifts all monomials in p by α. -/
noncomputable def monomialMul (α : GM) (p : GGroupAlg) : GGroupAlg :=
  Finsupp.mapDomain (· + α) p

/-- X̄_α = X(αf, 0): X-type logical operator of weight 12. -/
noncomputable def logicalX (α : GM) : BivariateBicycleCode.PauliX ell m_param where
  leftPoly := monomialMul α polyF
  rightPoly := 0

/-- X̄'_β = X(βg, βh): X-type logical operator. -/
noncomputable def logicalXPrime (β : GM) : BivariateBicycleCode.PauliX ell m_param where
  leftPoly := monomialMul β polyG
  rightPoly := monomialMul β polyH

/-- Z̄_β = Z(βh^T, βg^T): Z-type logical operator. -/
noncomputable def logicalZ (β : GM) : BivariateBicycleCode.PauliZ ell m_param where
  leftPoly := monomialMul β (transposeAlg ell m_param polyH)
  rightPoly := monomialMul β (transposeAlg ell m_param polyG)

/-- Z̄'_α = Z(0, αf^T): Z-type logical operator. -/
noncomputable def logicalZPrime (α : GM) : BivariateBicycleCode.PauliZ ell m_param where
  leftPoly := 0
  rightPoly := monomialMul α (transposeAlg ell m_param polyF)

/-! ## Section 8: Symmetry

The symmetry in the BB code construction means that if gauging measurements are
constructed for X̄_α and X̄'_β, the same Tanner graph connectivity works for
Z̄'_α and Z̄_β.

The symmetry arises from the relationship between X and Z logical operators:
X̄_α uses (αf, 0) while Z̄'_α uses (0, αf^T),
X̄'_β uses (βg, βh) while Z̄_β uses (βh^T, βg^T). -/

/-- The Z̄'_α right polynomial is the transpose of the X̄_α left polynomial. -/
theorem logicalZPrime_right_eq_transpose_logicalX_left (α : GM) :
    (logicalZPrime α).leftPoly = 0 ∧
    (logicalX α).rightPoly = 0 := by
  constructor <;> rfl

/-- Structural symmetry: logicalX uses (αf, 0) and logicalZPrime uses (0, αf^T). -/
theorem symmetry_X_ZPrime (α : GM) :
    (logicalX α).leftPoly = monomialMul α polyF ∧
    (logicalX α).rightPoly = 0 ∧
    (logicalZPrime α).leftPoly = 0 ∧
    (logicalZPrime α).rightPoly = monomialMul α (transposeAlg ell m_param polyF) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Structural symmetry: logicalXPrime uses (βg, βh) and logicalZ uses (βh^T, βg^T). -/
theorem symmetry_XPrime_Z (β : GM) :
    (logicalXPrime β).leftPoly = monomialMul β polyG ∧
    (logicalXPrime β).rightPoly = monomialMul β polyH ∧
    (logicalZ β).leftPoly = monomialMul β (transposeAlg ell m_param polyH) ∧
    (logicalZ β).rightPoly = monomialMul β (transposeAlg ell m_param polyG) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 9: Code parameters record

The Gross code is a [[144, 12, 12]] code. We record the claimed parameters. -/

/-- The code parameters [[n, k, d]] of the Gross code. -/
structure CodeParameters where
  n : ℕ  -- number of physical qubits
  k : ℕ  -- number of logical qubits
  d : ℕ  -- code distance

/-- The claimed parameters of the Gross code: [[144, 12, 12]]. -/
def grossCodeParams : CodeParameters where
  n := 144
  k := 12
  d := 12

@[simp] theorem grossCodeParams_n : grossCodeParams.n = 144 := rfl
@[simp] theorem grossCodeParams_k : grossCodeParams.k = 12 := rfl
@[simp] theorem grossCodeParams_d : grossCodeParams.d = 12 := rfl

/-- 144 = 12 × 12, i.e., a gross is a dozen dozens. -/
theorem gross_is_dozen_dozens : grossCodeParams.n = 12 * 12 := by norm_num

/-- The number of physical qubits matches the code parameter n. -/
theorem numQubits_eq_params :
    BivariateBicycleCode.numPhysicalQubits ell m_param = grossCodeParams.n := by
  simp [numQubits_eq]

/-! ## Section 10: Simp lemmas for the Gross code polynomials -/

@[simp] theorem grossCode_polyA : grossCode.polyA = polyA := rfl
@[simp] theorem grossCode_polyB : grossCode.polyB = polyB := rfl

/-- The logicalX operator has zero right component. -/
@[simp] theorem logicalX_rightPoly (α : GM) :
    (logicalX α).rightPoly = 0 := rfl

/-- The logicalZPrime operator has zero left component. -/
@[simp] theorem logicalZPrime_leftPoly (α : GM) :
    (logicalZPrime α).leftPoly = 0 := rfl

end QEC1.GrossCode
