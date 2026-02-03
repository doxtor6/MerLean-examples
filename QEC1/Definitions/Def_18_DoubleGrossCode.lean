import QEC1.Definitions.Def_16_BivariateBicycleCode
import QEC1.Definitions.Def_17_GrossCode

set_option linter.unusedSectionVars false

/-!
# Double Gross Code (Definition 18)

## Statement
The **Double Gross code** is the [[288, 12, 18]] Bivariate Bicycle code with parameters:
- ℓ = 12, m = 12
- A = x³ + y⁷ + y²
- B = y³ + x² + x

**Logical operators**: The weight-18 logical X operators are:
  X̄_α = X(αf, 0)
where f is a polynomial with 18 terms (see logicalXPolyF definition).

**Weight**: |X̄_α| = |f| = 18.

The name comes from "double gross" = 2 × 144 = 288.

## Main Results
**Main Definition** (`DoubleGrossCode`): The [[288, 12, 18]] BB code
- `doubleGrossCodeParams`: The code parameters [[288, 12, 18]]
- `doubleGrossPolyA`, `doubleGrossPolyB`: The defining polynomials A and B
- `doubleGrossLogicalXPolyF`: The logical X operator polynomial f

## File Structure
1. Code Parameters: ℓ = 12, m = 12
2. Defining Polynomials: A = x³ + y⁷ + y², B = y³ + x² + x
3. Double Gross Code Construction: The BivariateBicycleCode instance
4. Logical Operators: The f polynomial for logical X operators
5. Weight Verification: f has weight 18
6. Helper Lemmas: Basic properties of the Double Gross code
-/

namespace QEC

/-! ## Section 1: Code Parameters -/

/-- The ℓ parameter for the Double Gross code: ℓ = 12 -/
abbrev DoubleGrossCode.ell : ℕ := 12

/-- The m parameter for the Double Gross code: m = 12 -/
abbrev DoubleGrossCode.m : ℕ := 12

/-- ℓ is nonzero -/
instance DoubleGrossCode.ellNeZero : NeZero DoubleGrossCode.ell := ⟨by decide⟩

/-- m is nonzero -/
instance DoubleGrossCode.mNeZero : NeZero DoubleGrossCode.m := ⟨by decide⟩

/-- Total number of physical qubits: n = 2 * ℓ * m = 288 -/
theorem DoubleGrossCode.numQubits :
    2 * DoubleGrossCode.ell * DoubleGrossCode.m = 288 := by decide

/-- 288 = 2 * 144 = 2 * gross = "double gross" -/
theorem doubleGross_eq_two_gross : 2 * 144 = 288 := by decide

/-! ## Section 2: Defining Polynomials -/

/-- Polynomial A for the Double Gross code: A = x³ + y⁷ + y²
    Support: {(3, 0), (0, 7), (0, 2)} -/
def doubleGrossPolyA : BBPolynomial DoubleGrossCode.ell DoubleGrossCode.m where
  support := {(3, 0), (0, 7), (0, 2)}

/-- Polynomial B for the Double Gross code: B = y³ + x² + x
    Support: {(0, 3), (2, 0), (1, 0)} -/
def doubleGrossPolyB : BBPolynomial DoubleGrossCode.ell DoubleGrossCode.m where
  support := {(0, 3), (2, 0), (1, 0)}

/-- A has 3 terms -/
theorem doubleGrossPolyA_numTerms : doubleGrossPolyA.numTerms = 3 := by
  simp only [doubleGrossPolyA, BBPolynomial.numTerms]
  decide

/-- B has 3 terms -/
theorem doubleGrossPolyB_numTerms : doubleGrossPolyB.numTerms = 3 := by
  simp only [doubleGrossPolyB, BBPolynomial.numTerms]
  decide

/-! ## Section 3: The Double Gross Code -/

/-- The Double Gross code: a [[288, 12, 18]] Bivariate Bicycle code -/
def DoubleGrossCode : BivariateBicycleCode DoubleGrossCode.ell DoubleGrossCode.m where
  polyA := doubleGrossPolyA
  polyB := doubleGrossPolyB

/-- The Double Gross code parameters: [[n, k, d]] = [[288, 12, 18]] -/
structure DoubleGrossCodeParams where
  /-- Number of physical qubits: n = 288 -/
  n : ℕ := 288
  /-- Number of logical qubits: k = 12 -/
  k : ℕ := 12
  /-- Code distance: d = 18 -/
  d : ℕ := 18

/-- The canonical Double Gross code parameters -/
def doubleGrossCodeParams : DoubleGrossCodeParams := {}

/-- Double Gross code has 288 physical qubits -/
theorem DoubleGrossCode.numPhysical : DoubleGrossCode.numPhysicalQubits = 288 := by
  simp only [BivariateBicycleCode.numPhysicalQubits]
  decide

/-- Double Gross code has 144 left qubits and 144 right qubits -/
theorem DoubleGrossCode.numEachSide :
    DoubleGrossCode.numLeftQubits = 144 ∧ DoubleGrossCode.numRightQubits = 144 := by
  simp only [BivariateBicycleCode.numLeftQubits, BivariateBicycleCode.numRightQubits]
  constructor <;> decide

/-! ## Section 4: Logical X Operator Polynomial f -/

/-- The polynomial f for logical X operators with 18 terms:
    - Pure x terms (y⁰): 8 terms at (0,0), (1,0), (2,0), (7,0), (8,0), (9,0), (10,0), (11,0)
    - y³ terms: 4 terms at (0,3), (6,3), (8,3), (10,3)
    - y⁶ terms: 4 terms at (5,6), (6,6), (9,6), (10,6)
    - y⁹ terms: 2 terms at (4,9), (8,9) -/
def doubleGrossLogicalXPolyF : BBPolynomial DoubleGrossCode.ell DoubleGrossCode.m where
  support := {
    -- Pure x terms (1 + x + x² + x⁷ + x⁸ + x⁹ + x¹⁰ + x¹¹)
    (0, 0), (1, 0), (2, 0), (7, 0), (8, 0), (9, 0), (10, 0), (11, 0),
    -- y³ terms: (1 + x⁶ + x⁸ + x¹⁰)y³
    (0, 3), (6, 3), (8, 3), (10, 3),
    -- y⁶ terms: (x⁵ + x⁶ + x⁹ + x¹⁰)y⁶
    (5, 6), (6, 6), (9, 6), (10, 6),
    -- y⁹ terms: (x⁴ + x⁸)y⁹
    (4, 9), (8, 9)
  }

/-- The support of the logical X polynomial f -/
def doubleGrossLogicalXPolyF_support_explicit :
    Finset (Fin 12 × Fin 12) :=
  {(0, 0), (1, 0), (2, 0), (7, 0), (8, 0), (9, 0), (10, 0), (11, 0),
   (0, 3), (6, 3), (8, 3), (10, 3),
   (5, 6), (6, 6), (9, 6), (10, 6),
   (4, 9), (8, 9)}

/-- f has weight 18 (the support has 18 elements) -/
theorem doubleGrossLogicalXPolyF_weight : doubleGrossLogicalXPolyF.numTerms = 18 := by
  simp only [doubleGrossLogicalXPolyF, BBPolynomial.numTerms]
  decide

/-! ## Section 5: Logical X Operator Structure -/

/-- A logical X operator for the Double Gross code: X̄_α = X(αf, 0)
    Acts on left qubits at positions αf, no action on right qubits -/
structure DoubleGrossLogicalX where
  /-- The monomial coefficient α ∈ M -/
  alpha : Fin DoubleGrossCode.ell × Fin DoubleGrossCode.m

/-- The support of the logical X operator X̄_α on left qubits -/
def DoubleGrossLogicalX.leftSupport (L : DoubleGrossLogicalX) :
    Finset (Fin DoubleGrossCode.ell × Fin DoubleGrossCode.m) :=
  doubleGrossLogicalXPolyF.support.image (fun ⟨a, b⟩ => (L.alpha.1 + a, L.alpha.2 + b))

/-- X̄_α has no support on right qubits -/
def DoubleGrossLogicalX.rightSupport (_L : DoubleGrossLogicalX) :
    Finset (Fin DoubleGrossCode.ell × Fin DoubleGrossCode.m) := ∅

/-- Total weight of X̄_α is at most 18 -/
theorem DoubleGrossLogicalX.totalWeight (L : DoubleGrossLogicalX) :
    L.leftSupport.card ≤ 18 := by
  simp only [DoubleGrossLogicalX.leftSupport]
  calc (doubleGrossLogicalXPolyF.support.image _).card
    ≤ doubleGrossLogicalXPolyF.support.card := Finset.card_image_le
    _ = 18 := doubleGrossLogicalXPolyF_weight

/-! ## Section 6: Logical Z Operator via Transpose Symmetry -/

/-- Transpose of f: f^T = f(x⁻¹, y⁻¹) for logical Z operators -/
def doubleGrossLogicalZPolyFT : BBPolynomial DoubleGrossCode.ell DoubleGrossCode.m :=
  doubleGrossLogicalXPolyF.transpose

/-- f^T has at most 18 terms -/
theorem doubleGrossLogicalZPolyFT_weight : doubleGrossLogicalZPolyFT.numTerms ≤ 18 := by
  unfold doubleGrossLogicalZPolyFT BBPolynomial.transpose BBPolynomial.numTerms
  calc (Finset.image _ doubleGrossLogicalXPolyF.support).card
    ≤ doubleGrossLogicalXPolyF.support.card := Finset.card_image_le
    _ = 18 := doubleGrossLogicalXPolyF_weight

/-- A logical Z operator for the Double Gross code: Z̄'_α = Z(0, αf^T)
    No action on left qubits, acts on right qubits at αf^T -/
structure DoubleGrossLogicalZ where
  /-- The monomial coefficient α ∈ M -/
  alpha : Fin DoubleGrossCode.ell × Fin DoubleGrossCode.m

/-- Z̄'_α has no support on left qubits -/
def DoubleGrossLogicalZ.leftSupport (_L : DoubleGrossLogicalZ) :
    Finset (Fin DoubleGrossCode.ell × Fin DoubleGrossCode.m) := ∅

/-- The support of Z̄'_α on right qubits -/
def DoubleGrossLogicalZ.rightSupport (L : DoubleGrossLogicalZ) :
    Finset (Fin DoubleGrossCode.ell × Fin DoubleGrossCode.m) :=
  doubleGrossLogicalZPolyFT.support.image (fun ⟨a, b⟩ => (L.alpha.1 + a, L.alpha.2 + b))

/-! ## Section 7: Code Properties -/

/-- The Double Gross code distance is 18 -/
def DoubleGrossCode.distance : ℕ := 18

/-- The number of logical qubits is 12 -/
def DoubleGrossCode.numLogical : ℕ := 12

/-- Dimension of code space: 2^12 = 4096 -/
theorem DoubleGrossCode.codeDimension : (2 : ℕ) ^ DoubleGrossCode.numLogical = 4096 := by
  simp only [DoubleGrossCode.numLogical]
  decide

/-- The name "double gross" comes from 2 × 144 -/
theorem double_gross_etymology : 2 * (GrossCode.ell * GrossCode.m) = 144 := by rfl

/-! ## Section 8: Check Weight Bounds -/

/-- Each X-check has weight at most 6 (|A| + |B| = 3 + 3 = 6) -/
theorem DoubleGrossCode.xCheckWeightBound :
    doubleGrossPolyA.numTerms + doubleGrossPolyB.numTerms = 6 := by
  rw [doubleGrossPolyA_numTerms, doubleGrossPolyB_numTerms]

/-- Each Z-check also has weight at most 6 (by transpose symmetry) -/
theorem DoubleGrossCode.zCheckWeightBound :
    doubleGrossPolyA.transpose.numTerms + doubleGrossPolyB.transpose.numTerms ≤ 6 := by
  have h1 : doubleGrossPolyA.transpose.numTerms ≤ 3 := by
    simp only [BBPolynomial.transpose, BBPolynomial.numTerms]
    calc (Finset.image (fun ⟨a, b⟩ => (-a, -b)) doubleGrossPolyA.support).card
      ≤ doubleGrossPolyA.support.card := Finset.card_image_le
      _ = 3 := doubleGrossPolyA_numTerms
  have h2 : doubleGrossPolyB.transpose.numTerms ≤ 3 := by
    simp only [BBPolynomial.transpose, BBPolynomial.numTerms]
    calc (Finset.image (fun ⟨a, b⟩ => (-a, -b)) doubleGrossPolyB.support).card
      ≤ doubleGrossPolyB.support.card := Finset.card_image_le
      _ = 3 := doubleGrossPolyB_numTerms
  omega

/-! ## Section 9: Helper Lemmas -/

/-- The Double Gross code uses ℓ = 12 -/
@[simp]
theorem DoubleGrossCode.ell_val : DoubleGrossCode.ell = 12 := rfl

/-- The Double Gross code uses m = 12 -/
@[simp]
theorem DoubleGrossCode.m_val : DoubleGrossCode.m = 12 := rfl

/-- ℓ * m = 144 -/
@[simp]
theorem DoubleGrossCode.ell_mul_m : DoubleGrossCode.ell * DoubleGrossCode.m = 144 := by decide

/-- The polynomial A is x³ + y⁷ + y² -/
theorem DoubleGrossCode.polyA_eq : DoubleGrossCode.polyA = doubleGrossPolyA := rfl

/-- The polynomial B is y³ + x² + x -/
theorem DoubleGrossCode.polyB_eq : DoubleGrossCode.polyB = doubleGrossPolyB := rfl

/-- A and B have the same number of terms -/
theorem DoubleGrossCode.polyAB_same_weight :
    doubleGrossPolyA.numTerms = doubleGrossPolyB.numTerms := by
  rw [doubleGrossPolyA_numTerms, doubleGrossPolyB_numTerms]

/-- The monomial group M = Z_ℓ × Z_m has order 144 -/
theorem DoubleGrossCode.monomialGroupOrder :
    Fintype.card (Fin DoubleGrossCode.ell × Fin DoubleGrossCode.m) = 144 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  decide

/-- There are 144 X-checks and 144 Z-checks, totaling 288 checks -/
theorem DoubleGrossCode.numChecks : DoubleGrossCode.numTotalChecks = 288 := by
  simp only [BivariateBicycleCode.numTotalChecks]
  decide

/-- The Double Gross code is a member of the BB code family -/
theorem DoubleGrossCode.isBBCode :
    DoubleGrossCode = ⟨doubleGrossPolyA, doubleGrossPolyB⟩ := rfl

/-- Support of polynomial A contains x³ -/
theorem doubleGrossPolyA_contains_x3 : (3, 0) ∈ doubleGrossPolyA.support := by
  simp only [doubleGrossPolyA]
  decide

/-- Support of polynomial A contains y⁷ -/
theorem doubleGrossPolyA_contains_y7 : (0, 7) ∈ doubleGrossPolyA.support := by
  simp only [doubleGrossPolyA]
  decide

/-- Support of polynomial A contains y² -/
theorem doubleGrossPolyA_contains_y2 : (0, 2) ∈ doubleGrossPolyA.support := by
  simp only [doubleGrossPolyA]
  decide

/-- Support of polynomial B contains y³ -/
theorem doubleGrossPolyB_contains_y3 : (0, 3) ∈ doubleGrossPolyB.support := by
  simp only [doubleGrossPolyB]
  decide

/-- Support of polynomial B contains x² -/
theorem doubleGrossPolyB_contains_x2 : (2, 0) ∈ doubleGrossPolyB.support := by
  simp only [doubleGrossPolyB]
  decide

/-- Support of polynomial B contains x -/
theorem doubleGrossPolyB_contains_x : (1, 0) ∈ doubleGrossPolyB.support := by
  simp only [doubleGrossPolyB]
  decide

/-- The Double Gross code has rate k/n = 12/288 = 1/24 -/
theorem DoubleGrossCode.rate :
    (doubleGrossCodeParams.k : ℚ) / doubleGrossCodeParams.n = 1 / 24 := by
  unfold doubleGrossCodeParams
  norm_num

/-- Double Gross code has twice the qubits per side as Gross code -/
theorem doubleGross_vs_gross_qubits_per_side :
    DoubleGrossCode.ell * DoubleGrossCode.m = 2 * (GrossCode.ell * GrossCode.m) := by
  rfl

/-- Polynomial f contains the identity term -/
theorem doubleGrossLogicalXPolyF_contains_identity :
    (0, 0) ∈ doubleGrossLogicalXPolyF.support := by
  simp only [doubleGrossLogicalXPolyF]
  decide

/-- Polynomial f contains x term -/
theorem doubleGrossLogicalXPolyF_contains_x :
    (1, 0) ∈ doubleGrossLogicalXPolyF.support := by
  simp only [doubleGrossLogicalXPolyF]
  decide

/-- Polynomial f contains x² term -/
theorem doubleGrossLogicalXPolyF_contains_x2 :
    (2, 0) ∈ doubleGrossLogicalXPolyF.support := by
  simp only [doubleGrossLogicalXPolyF]
  decide

/-- The logical X operator weight equals the code distance -/
theorem doubleGrossLogicalX_weight_eq_distance :
    doubleGrossLogicalXPolyF.numTerms = DoubleGrossCode.distance := by
  rw [doubleGrossLogicalXPolyF_weight, DoubleGrossCode.distance]

end QEC
