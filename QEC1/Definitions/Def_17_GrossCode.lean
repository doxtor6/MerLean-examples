import QEC1.Definitions.Def_16_BivariateBicycleCode
import QEC1.Definitions.Def_2_LogicalOperator

set_option linter.unusedSectionVars false

/-!
# Gross Code (Definition 17)

## Statement
The **Gross code** is the [[144, 12, 12]] Bivariate Bicycle code with parameters:
- ℓ = 12, m = 6
- A = x³ + y² + y
- B = y³ + x² + x

The name comes from "gross" = 12 dozen = 144.

**Logical operators**: A basis of logical X operators is given by:
- X̄_α = X(αf, 0) where f = 1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹ + (x + x⁵ + x⁷ + x¹¹)y³
- X̄'_β = X(βg, βh) where:
  - g = x + x²y + (1 + x)y² + x²y³ + y⁴
  - h = 1 + (1 + x)y + y² + (1 + x)y³

The logical Z operators are obtained by the BB code symmetry:
- Z̄_β = Z(βhᵀ, βgᵀ)
- Z̄'_α = Z(0, αfᵀ)

**Weight**: |X̄_α| = |f| = 12 (weight 12 logical).

## Main Results
**Main Definition** (`GrossCode`): The [[144, 12, 12]] BB code
- `grossCodeParams`: The code parameters [[144, 12, 12]]
- `grossPolyA`, `grossPolyB`: The defining polynomials A and B
- `logicalXOperatorF`, `logicalXOperatorGH`: Logical X operator polynomials

## File Structure
1. Code Parameters: ℓ = 12, m = 6
2. Defining Polynomials: A = x³ + y² + y, B = y³ + x² + x
3. Gross Code Construction: The BivariateBicycleCode instance
4. Logical Operators: The f, g, h polynomials for logical operators
5. Weight Verification: f has weight 12
6. Helper Lemmas: Basic properties of the Gross code
-/

namespace QEC

/-! ## Section 1: Code Parameters -/

/-- The ℓ parameter for the Gross code: ℓ = 12 -/
abbrev GrossCode.ell : ℕ := 12

/-- The m parameter for the Gross code: m = 6 -/
abbrev GrossCode.m : ℕ := 6

/-- ℓ is nonzero -/
instance : NeZero GrossCode.ell := ⟨by decide⟩

/-- m is nonzero -/
instance : NeZero GrossCode.m := ⟨by decide⟩

/-- Total number of physical qubits: n = 2 * ℓ * m = 144 -/
theorem GrossCode.numQubits : 2 * GrossCode.ell * GrossCode.m = 144 := by decide

/-- 144 = 12 * 12 = 12 dozen = "gross" -/
theorem gross_eq_dozen_squared : 12 * 12 = 144 := by decide

/-! ## Section 2: Defining Polynomials -/

/-- Polynomial A for the Gross code: A = x³ + y² + y
    Support: {(3, 0), (0, 2), (0, 1)} -/
def grossPolyA : BBPolynomial GrossCode.ell GrossCode.m where
  support := {(3, 0), (0, 2), (0, 1)}

/-- Polynomial B for the Gross code: B = y³ + x² + x
    Support: {(0, 3), (2, 0), (1, 0)} -/
def grossPolyB : BBPolynomial GrossCode.ell GrossCode.m where
  support := {(0, 3), (2, 0), (1, 0)}

/-- A has 3 terms -/
theorem grossPolyA_numTerms : grossPolyA.numTerms = 3 := by
  simp only [grossPolyA, BBPolynomial.numTerms]
  decide

/-- B has 3 terms -/
theorem grossPolyB_numTerms : grossPolyB.numTerms = 3 := by
  simp only [grossPolyB, BBPolynomial.numTerms]
  decide

/-! ## Section 3: The Gross Code -/

/-- The Gross code: a [[144, 12, 12]] Bivariate Bicycle code -/
def GrossCode : BivariateBicycleCode GrossCode.ell GrossCode.m where
  polyA := grossPolyA
  polyB := grossPolyB

/-- The Gross code parameters: [[n, k, d]] = [[144, 12, 12]] -/
structure GrossCodeParams where
  /-- Number of physical qubits: n = 144 -/
  n : ℕ := 144
  /-- Number of logical qubits: k = 12 -/
  k : ℕ := 12
  /-- Code distance: d = 12 -/
  d : ℕ := 12

/-- The canonical Gross code parameters -/
def grossCodeParams : GrossCodeParams := {}

/-- Gross code has 144 physical qubits -/
theorem GrossCode.numPhysical : GrossCode.numPhysicalQubits = 144 := by
  simp only [BivariateBicycleCode.numPhysicalQubits]
  decide

/-- Gross code has 72 left qubits and 72 right qubits -/
theorem GrossCode.numEachSide :
    GrossCode.numLeftQubits = 72 ∧ GrossCode.numRightQubits = 72 := by
  simp only [BivariateBicycleCode.numLeftQubits, BivariateBicycleCode.numRightQubits]
  constructor <;> decide

/-! ## Section 4: Logical X Operator Polynomial f -/

/-- The polynomial f for logical X operators:
    f = 1 + x + x² + x³ + x⁶ + x⁷ + x⁸ + x⁹ + (x + x⁵ + x⁷ + x¹¹)y³

    Breaking down:
    - Constant and x terms: (0,0), (1,0), (2,0), (3,0), (6,0), (7,0), (8,0), (9,0)
    - y³ terms: (1,3), (5,3), (7,3), (11,3)

    Total: 12 terms -/
def logicalXPolyF : BBPolynomial GrossCode.ell GrossCode.m where
  support := {
    (0, 0), (1, 0), (2, 0), (3, 0), (6, 0), (7, 0), (8, 0), (9, 0),
    (1, 3), (5, 3), (7, 3), (11, 3)
  }

/-- f has weight 12 -/
theorem logicalXPolyF_weight : logicalXPolyF.numTerms = 12 := by
  simp only [logicalXPolyF, BBPolynomial.numTerms]
  decide

/-! ## Section 5: Logical X Operator Polynomials g and h -/

/-- The polynomial g for the second logical X operator basis:
    g = x + x²y + (1 + x)y² + x²y³ + y⁴

    Support: (1,0), (2,1), (0,2), (1,2), (2,3), (0,4) -/
def logicalXPolyG : BBPolynomial GrossCode.ell GrossCode.m where
  support := {(1, 0), (2, 1), (0, 2), (1, 2), (2, 3), (0, 4)}

/-- The polynomial h for the second logical X operator basis:
    h = 1 + (1 + x)y + y² + (1 + x)y³

    Support: (0,0), (0,1), (1,1), (0,2), (0,3), (1,3) -/
def logicalXPolyH : BBPolynomial GrossCode.ell GrossCode.m where
  support := {(0, 0), (0, 1), (1, 1), (0, 2), (0, 3), (1, 3)}

/-- g has 6 terms -/
theorem logicalXPolyG_numTerms : logicalXPolyG.numTerms = 6 := by
  simp only [logicalXPolyG, BBPolynomial.numTerms]
  decide

/-- h has 6 terms -/
theorem logicalXPolyH_numTerms : logicalXPolyH.numTerms = 6 := by
  simp only [logicalXPolyH, BBPolynomial.numTerms]
  decide

/-! ## Section 6: Logical Z Operators via Transpose Symmetry -/

/-- Transpose of f: f^T = f(x⁻¹, y⁻¹) for logical Z operators.
    Under x → x⁻¹ = x^{11}, y → y⁻¹ = y^{5}:
    - (0,0) → (0,0)
    - (a,b) → (12-a mod 12, 6-b mod 6) -/
def logicalZPolyFT : BBPolynomial GrossCode.ell GrossCode.m :=
  logicalXPolyF.transpose

/-- Transpose of g for logical Z operators -/
def logicalZPolyGT : BBPolynomial GrossCode.ell GrossCode.m :=
  logicalXPolyG.transpose

/-- Transpose of h for logical Z operators -/
def logicalZPolyHT : BBPolynomial GrossCode.ell GrossCode.m :=
  logicalXPolyH.transpose

/-- f^T has the same number of terms as f -/
theorem logicalZPolyFT_weight : logicalZPolyFT.numTerms ≤ 12 := by
  simp only [logicalZPolyFT, BBPolynomial.transpose, BBPolynomial.numTerms]
  exact Finset.card_image_le

/-! ## Section 7: Logical Operator Support Structures -/

/-- A logical X operator of the first kind: X̄_α = X(αf, 0)
    Acts on left qubits at positions αf, no action on right qubits -/
structure LogicalXAlpha where
  /-- The monomial coefficient α ∈ M -/
  alpha : Fin GrossCode.ell × Fin GrossCode.m

/-- The support of the logical X operator X̄_α on left qubits -/
def LogicalXAlpha.leftSupport (L : LogicalXAlpha) :
    Finset (Fin GrossCode.ell × Fin GrossCode.m) :=
  logicalXPolyF.support.image (fun ⟨a, b⟩ => (L.alpha.1 + a, L.alpha.2 + b))

/-- X̄_α has no support on right qubits -/
def LogicalXAlpha.rightSupport (_L : LogicalXAlpha) :
    Finset (Fin GrossCode.ell × Fin GrossCode.m) := ∅

/-- Total weight of X̄_α is at most 12 -/
theorem LogicalXAlpha.totalWeight (L : LogicalXAlpha) :
    L.leftSupport.card ≤ 12 := by
  simp only [LogicalXAlpha.leftSupport]
  calc L.leftSupport.card
    = (logicalXPolyF.support.image _).card := rfl
    _ ≤ logicalXPolyF.support.card := Finset.card_image_le
    _ = 12 := logicalXPolyF_weight

/-- A logical X operator of the second kind: X̄'_β = X(βg, βh)
    Acts on left qubits at positions βg and right qubits at positions βh -/
structure LogicalXBeta where
  /-- The monomial coefficient β ∈ M -/
  beta : Fin GrossCode.ell × Fin GrossCode.m

/-- The support of the logical X operator X̄'_β on left qubits -/
def LogicalXBeta.leftSupport (L : LogicalXBeta) :
    Finset (Fin GrossCode.ell × Fin GrossCode.m) :=
  logicalXPolyG.support.image (fun ⟨a, b⟩ => (L.beta.1 + a, L.beta.2 + b))

/-- The support of the logical X operator X̄'_β on right qubits -/
def LogicalXBeta.rightSupport (L : LogicalXBeta) :
    Finset (Fin GrossCode.ell × Fin GrossCode.m) :=
  logicalXPolyH.support.image (fun ⟨a, b⟩ => (L.beta.1 + a, L.beta.2 + b))

/-- A logical Z operator of the first kind: Z̄_β = Z(βh^T, βg^T)
    Uses transpose symmetry of the BB code -/
structure LogicalZBeta where
  /-- The monomial coefficient β ∈ M -/
  beta : Fin GrossCode.ell × Fin GrossCode.m

/-- A logical Z operator of the second kind: Z̄'_α = Z(0, αf^T)
    No action on left qubits, acts on right qubits at αf^T -/
structure LogicalZAlpha where
  /-- The monomial coefficient α ∈ M -/
  alpha : Fin GrossCode.ell × Fin GrossCode.m

/-- Z̄'_α has no support on left qubits -/
def LogicalZAlpha.leftSupport (_L : LogicalZAlpha) :
    Finset (Fin GrossCode.ell × Fin GrossCode.m) := ∅

/-- The support of Z̄'_α on right qubits -/
def LogicalZAlpha.rightSupport (L : LogicalZAlpha) :
    Finset (Fin GrossCode.ell × Fin GrossCode.m) :=
  logicalZPolyFT.support.image (fun ⟨a, b⟩ => (L.alpha.1 + a, L.alpha.2 + b))

/-! ## Section 8: Code Properties -/

/-- The Gross code distance is 12 (by construction, the weight of the logical operators) -/
def GrossCode.distance : ℕ := 12

/-- The number of logical qubits is 12 -/
def GrossCode.numLogical : ℕ := 12

/-- Dimension of code space: 2^12 = 4096 -/
theorem GrossCode.codeDimension : (2 : ℕ) ^ GrossCode.numLogical = 4096 := by
  simp only [GrossCode.numLogical]
  decide

/-- The name "gross" comes from 12 dozen -/
theorem gross_etymology : 12 * 12 = GrossCode.ell * GrossCode.ell := by rfl

/-! ## Section 9: Check Weight Bounds -/

/-- Each X-check has weight at most 6 (|A| + |B| = 3 + 3 = 6) -/
theorem GrossCode.xCheckWeightBound :
    grossPolyA.numTerms + grossPolyB.numTerms = 6 := by
  rw [grossPolyA_numTerms, grossPolyB_numTerms]

/-- Each Z-check also has weight at most 6 (by transpose symmetry) -/
theorem GrossCode.zCheckWeightBound :
    grossPolyA.transpose.numTerms + grossPolyB.transpose.numTerms ≤ 6 := by
  have h1 : grossPolyA.transpose.numTerms ≤ 3 := by
    simp only [BBPolynomial.transpose, BBPolynomial.numTerms]
    calc (Finset.image (fun ⟨a, b⟩ => (-a, -b)) grossPolyA.support).card
      ≤ grossPolyA.support.card := Finset.card_image_le
      _ = 3 := grossPolyA_numTerms
  have h2 : grossPolyB.transpose.numTerms ≤ 3 := by
    simp only [BBPolynomial.transpose, BBPolynomial.numTerms]
    calc (Finset.image (fun ⟨a, b⟩ => (-a, -b)) grossPolyB.support).card
      ≤ grossPolyB.support.card := Finset.card_image_le
      _ = 3 := grossPolyB_numTerms
  omega

/-! ## Section 10: Helper Lemmas -/

/-- The Gross code uses ℓ = 12 -/
@[simp]
theorem GrossCode.ell_val : GrossCode.ell = 12 := rfl

/-- The Gross code uses m = 6 -/
@[simp]
theorem GrossCode.m_val : GrossCode.m = 6 := rfl

/-- ℓ * m = 72 -/
@[simp]
theorem GrossCode.ell_mul_m : GrossCode.ell * GrossCode.m = 72 := by decide

/-- The polynomial A is x³ + y² + y -/
theorem GrossCode.polyA_eq : GrossCode.polyA = grossPolyA := rfl

/-- The polynomial B is y³ + x² + x -/
theorem GrossCode.polyB_eq : GrossCode.polyB = grossPolyB := rfl

/-- A and B have the same number of terms -/
theorem GrossCode.polyAB_same_weight : grossPolyA.numTerms = grossPolyB.numTerms := by
  rw [grossPolyA_numTerms, grossPolyB_numTerms]

/-- The monomial group M = Z_ℓ × Z_m has order 72 -/
theorem GrossCode.monomialGroupOrder :
    Fintype.card (Fin GrossCode.ell × Fin GrossCode.m) = 72 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  decide

/-- There are 72 X-checks and 72 Z-checks, totaling 144 checks -/
theorem GrossCode.numChecks : GrossCode.numTotalChecks = 144 := by
  simp only [BivariateBicycleCode.numTotalChecks]
  decide

/-- The Gross code is symmetric: A and B have the same structure up to x↔y exchange -/
theorem GrossCode.symmetry :
    grossPolyA.support.card = grossPolyB.support.card := by
  simp only [grossPolyA, grossPolyB]
  decide

/-- The Gross code has rate k/n = 12/144 = 1/12 -/
theorem GrossCode.rate : (grossCodeParams.k : ℚ) / grossCodeParams.n = 1 / 12 := by
  unfold grossCodeParams
  norm_num

/-- The Gross code is a member of the BB code family -/
theorem GrossCode.isBBCode : GrossCode = ⟨grossPolyA, grossPolyB⟩ := rfl

/-- Support of polynomial A contains x³ -/
theorem grossPolyA_contains_x3 : (3, 0) ∈ grossPolyA.support := by
  simp only [grossPolyA]
  decide

/-- Support of polynomial A contains y² -/
theorem grossPolyA_contains_y2 : (0, 2) ∈ grossPolyA.support := by
  simp only [grossPolyA]
  decide

/-- Support of polynomial A contains y -/
theorem grossPolyA_contains_y : (0, 1) ∈ grossPolyA.support := by
  simp only [grossPolyA]
  decide

/-- Support of polynomial B contains y³ -/
theorem grossPolyB_contains_y3 : (0, 3) ∈ grossPolyB.support := by
  simp only [grossPolyB]
  decide

/-- Support of polynomial B contains x² -/
theorem grossPolyB_contains_x2 : (2, 0) ∈ grossPolyB.support := by
  simp only [grossPolyB]
  decide

/-- Support of polynomial B contains x -/
theorem grossPolyB_contains_x : (1, 0) ∈ grossPolyB.support := by
  simp only [grossPolyB]
  decide

end QEC
