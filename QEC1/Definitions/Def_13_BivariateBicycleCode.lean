import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# Def_13: Bivariate Bicycle Code

## Statement
A **Bivariate Bicycle (BB) code** is a CSS code defined as follows:

**Setup**: Let ℓ, m be positive integers. Define:
- I_r: the r × r identity matrix
- C_r: the cyclic permutation matrix of r items, satisfying ⟨i|C_r = ⟨(i+1) mod r|
- x = C_ℓ ⊗ I_m (cyclic shift in the first coordinate)
- y = I_ℓ ⊗ C_m (cyclic shift in the second coordinate)

These matrices satisfy x^ℓ = y^m = I_{ℓm} and xᵀx = yᵀy = I_{ℓm}.

**Qubits**: The code uses n = 2ℓm physical qubits divided into ℓm left (L) and ℓm right (R)
qubits.

**Parity check matrices**: Given polynomials A, B ∈ F₂[x,y], the parity check matrices are:
  H_X = [A | B], H_Z = [Bᵀ | Aᵀ]
where Aᵀ = A(x⁻¹, y⁻¹).

**Labeling**: X checks, Z checks, L qubits, R qubits are each in 1-1 correspondence with
elements of M = {x^a y^b : a, b ∈ Z}.

## Main Definitions
- `M` : Monomial set ZMod ℓ × ZMod m
- `GroupAlg` : Group algebra F₂[M] for polynomials in x, y
- `cyclicShiftX` : Generator x as group algebra element
- `cyclicShiftY` : Generator y as group algebra element
- `transposeAlg` : Transpose operation A ↦ A(x⁻¹, y⁻¹)
- `LabelType` : Type for labeling {X, Z, L, R}
- `BivariateBicycleCode` : The full BB code structure with H_X and H_Z
- `parityCheckX` : H_X = [A | B]
- `parityCheckZ` : H_Z = [Bᵀ | Aᵀ]

## Corollaries
- `cyclicShiftX_order` : x^ℓ = 1 in the group algebra
- `cyclicShiftY_order` : y^m = 1 in the group algebra
- `transposeAlg_involutive` : (Aᵀ)ᵀ = A
- `permX_permY_comm` : x and y commute as permutations
- `permX_transpose_mul` : xᵀx = I
-/

set_option linter.unusedSectionVars false

open Matrix Finset

namespace QEC1.BivariateBicycle

variable (ℓ m : ℕ) [NeZero ℓ] [NeZero m]

/-! ## Section 1: The Monomial Set M

Elements of M = {x^a y^b} are represented as pairs (a, b) ∈ ZMod ℓ × ZMod m.
This is an additive abelian group where addition represents multiplication of monomials. -/

/-- The monomial set M = {x^a y^b : a ∈ ZMod ℓ, b ∈ ZMod m}. -/
abbrev M := ZMod ℓ × ZMod m

/-! ## Section 2: Group Algebra F₂[M]

Polynomials in x, y over F₂ are elements of the group algebra (ZMod 2)[M].
An element is a finitely supported function M → ZMod 2. -/

/-- The group algebra F₂[x, y] / (x^ℓ - 1, y^m - 1), represented as AddMonoidAlgebra. -/
abbrev GroupAlg := AddMonoidAlgebra (ZMod 2) (M ℓ m)

/-! ## Section 3: Generators x and y

x corresponds to the monomial (1, 0) in M, representing C_ℓ ⊗ I_m.
y corresponds to the monomial (0, 1) in M, representing I_ℓ ⊗ C_m. -/

/-- The generator x = C_ℓ ⊗ I_m as an element of the group algebra. -/
noncomputable def cyclicShiftX : GroupAlg ℓ m :=
  Finsupp.single ((1 : ZMod ℓ), (0 : ZMod m)) 1

/-- The generator y = I_ℓ ⊗ C_m as an element of the group algebra. -/
noncomputable def cyclicShiftY : GroupAlg ℓ m :=
  Finsupp.single ((0 : ZMod ℓ), (1 : ZMod m)) 1

/-- A monomial x^a y^b as an element of the group algebra. -/
noncomputable def monomial (a : ZMod ℓ) (b : ZMod m) : GroupAlg ℓ m :=
  Finsupp.single (a, b) 1

/-! ## Section 4: Transpose Operation

For a BB code, the transpose operation is A^T = A(x⁻¹, y⁻¹).
In the additive group M, this corresponds to negating both coordinates:
(a, b) ↦ (-a, -b). -/

/-- The transpose operation on monomials: (a, b) ↦ (-a, -b). -/
def transposeMonomial : M ℓ m → M ℓ m :=
  fun ⟨a, b⟩ => (-a, -b)

@[simp]
theorem transposeMonomial_apply (a : ZMod ℓ) (b : ZMod m) :
    transposeMonomial ℓ m (a, b) = (-a, -b) := rfl

@[simp]
theorem transposeMonomial_involutive :
    Function.Involutive (transposeMonomial ℓ m) := by
  intro ⟨a, b⟩
  simp [transposeMonomial, neg_neg]

theorem transposeMonomial_injective :
    Function.Injective (transposeMonomial ℓ m) :=
  (transposeMonomial_involutive ℓ m).injective

/-- The transpose of a group algebra element: A^T = A(x⁻¹, y⁻¹).
This maps each monomial (a,b) to (-a,-b), preserving coefficients. -/
noncomputable def transposeAlg (p : GroupAlg ℓ m) : GroupAlg ℓ m :=
  Finsupp.mapDomain (transposeMonomial ℓ m) p

@[simp]
theorem transposeAlg_involutive :
    Function.Involutive (transposeAlg ℓ m) := by
  intro p
  simp only [transposeAlg]
  rw [← Finsupp.mapDomain_comp]
  have : transposeMonomial ℓ m ∘ transposeMonomial ℓ m = id :=
    (transposeMonomial_involutive ℓ m).comp_self
  rw [this, Finsupp.mapDomain_id]

/-! ## Section 5: Matrix Representation

The group algebra acts on F₂^{ℓm} by permutation.
The matrix representation sends a polynomial p to the matrix whose (α, β) entry is
the coefficient of α - β in p (i.e., a circulant-like structure on the product group). -/

/-- Matrix representation of a group algebra element: the (α, β)-entry is p(α - β). -/
noncomputable def toMatrix (p : GroupAlg ℓ m) : Matrix (M ℓ m) (M ℓ m) (ZMod 2) :=
  Matrix.of fun α β => p (α - β)

/-- The matrix transpose equals the algebraic transpose. -/
theorem toMatrix_transpose (p : GroupAlg ℓ m) :
    (toMatrix ℓ m p)ᵀ = toMatrix ℓ m (transposeAlg ℓ m p) := by
  ext α β
  simp only [toMatrix, transposeAlg, Matrix.transpose_apply, Matrix.of_apply]
  have key : α - β = transposeMonomial ℓ m (β - α) := by
    simp [transposeMonomial, neg_sub, Prod.ext_iff]
  rw [key, Finsupp.mapDomain_apply (transposeMonomial_injective ℓ m)]

/-! ## Section 6: Label Types

Checks and qubits are labeled by (α, T) where α ∈ M and T ∈ {X, Z, L, R}. -/

/-- The four label types for checks and qubits. -/
inductive LabelType : Type where
  | X : LabelType  -- X-type check
  | Z : LabelType  -- Z-type check
  | L : LabelType  -- Left qubit
  | R : LabelType  -- Right qubit
  deriving DecidableEq, Repr

/-- A labeled element: a monomial paired with a label type. -/
abbrev LabeledElement := M ℓ m × LabelType

/-! ## Section 7: Bivariate Bicycle Code Structure -/

/-- A Bivariate Bicycle (BB) code specified by parameters ℓ, m and polynomials A, B. -/
structure BivariateBicycleCode where
  /-- First polynomial A ∈ F₂[x, y] -/
  polyA : GroupAlg ℓ m
  /-- Second polynomial B ∈ F₂[x, y] -/
  polyB : GroupAlg ℓ m

namespace BivariateBicycleCode

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]
variable (code : BivariateBicycleCode ℓ m)

/-- The number of physical qubits: n = 2ℓm. -/
def numPhysicalQubits (ℓ m : ℕ) : ℕ := 2 * ℓ * m

/-- The number of left qubits: ℓm. -/
def numLeftQubits (ℓ m : ℕ) : ℕ := ℓ * m

/-- The number of right qubits: ℓm. -/
def numRightQubits (ℓ m : ℕ) : ℕ := ℓ * m

/-- n = numLeftQubits + numRightQubits -/
theorem numPhysicalQubits_eq (ℓ m : ℕ) :
    numPhysicalQubits ℓ m = numLeftQubits ℓ m + numRightQubits ℓ m := by
  unfold numPhysicalQubits numLeftQubits numRightQubits
  ring

/-- The number of X checks: ℓm. -/
def numXChecks (ℓ m : ℕ) : ℕ := ℓ * m

/-- The number of Z checks: ℓm. -/
def numZChecks (ℓ m : ℕ) : ℕ := ℓ * m

/-! ## Section 8: Parity Check Matrices

H_X = [A | B] : ℓm × 2ℓm matrix (rows indexed by M, columns by M ⊕ M)
H_Z = [B^T | A^T] : ℓm × 2ℓm matrix -/

/-- Matrix representation of polynomial A. -/
noncomputable def matA : Matrix (M ℓ m) (M ℓ m) (ZMod 2) :=
  toMatrix ℓ m code.polyA

/-- Matrix representation of polynomial B. -/
noncomputable def matB : Matrix (M ℓ m) (M ℓ m) (ZMod 2) :=
  toMatrix ℓ m code.polyB

/-- Matrix representation of A^T = A(x⁻¹, y⁻¹). -/
noncomputable def matAT : Matrix (M ℓ m) (M ℓ m) (ZMod 2) :=
  toMatrix ℓ m (transposeAlg ℓ m code.polyA)

/-- Matrix representation of B^T = B(x⁻¹, y⁻¹). -/
noncomputable def matBT : Matrix (M ℓ m) (M ℓ m) (ZMod 2) :=
  toMatrix ℓ m (transposeAlg ℓ m code.polyB)

/-- matAT is the matrix transpose of matA. -/
theorem matAT_eq_transpose : code.matAT = code.matAᵀ := by
  simp only [matAT, matA, toMatrix_transpose]

/-- matBT is the matrix transpose of matB. -/
theorem matBT_eq_transpose : code.matBT = code.matBᵀ := by
  simp only [matBT, matB, toMatrix_transpose]

/-- The X parity check matrix H_X = [A | B].
Rows indexed by M (checks), columns by M ⊕ M (left ⊕ right qubits). -/
noncomputable def parityCheckX : Matrix (M ℓ m) (M ℓ m ⊕ M ℓ m) (ZMod 2) :=
  Matrix.fromCols code.matA code.matB

/-- The Z parity check matrix H_Z = [B^T | A^T].
Rows indexed by M (checks), columns by M ⊕ M (left ⊕ right qubits). -/
noncomputable def parityCheckZ : Matrix (M ℓ m) (M ℓ m ⊕ M ℓ m) (ZMod 2) :=
  Matrix.fromCols code.matBT code.matAT

/-! ## Section 9: CSS Orthogonality

For a valid CSS code, H_X · H_Z^T = 0. This follows from AB^T + BA^T = 0 in F₂. -/

/-- CSS orthogonality condition: A * B^T + B * A^T = 0 over F₂.
This ensures commutativity of X and Z stabilizers. -/
def isCSS : Prop :=
  code.matA * code.matBT + code.matB * code.matAT = 0

/-! ## Section 10: Pauli Notation

X(p, q) denotes an X-type Pauli acting on left qubits with pattern p and right qubits
with pattern q. Similarly Z(p, q) for Z-type. -/

/-- An X-type Pauli operator X(p, q) specified by polynomials for left and right qubits. -/
structure PauliX (ℓ m : ℕ) [NeZero ℓ] [NeZero m] where
  /-- Pattern on left qubits -/
  leftPoly : GroupAlg ℓ m
  /-- Pattern on right qubits -/
  rightPoly : GroupAlg ℓ m

/-- A Z-type Pauli operator Z(p, q) specified by polynomials for left and right qubits. -/
structure PauliZ (ℓ m : ℕ) [NeZero ℓ] [NeZero m] where
  /-- Pattern on left qubits -/
  leftPoly : GroupAlg ℓ m
  /-- Pattern on right qubits -/
  rightPoly : GroupAlg ℓ m

/-- Support of a Pauli X(p,q) as a binary vector over left ⊕ right qubits. -/
noncomputable def PauliX.support {ℓ m : ℕ} [NeZero ℓ] [NeZero m] (P : PauliX ℓ m) :
    M ℓ m ⊕ M ℓ m → ZMod 2 :=
  fun
    | Sum.inl α => P.leftPoly α
    | Sum.inr α => P.rightPoly α

/-- Support of a Pauli Z(p,q) as a binary vector over left ⊕ right qubits. -/
noncomputable def PauliZ.support {ℓ m : ℕ} [NeZero ℓ] [NeZero m] (P : PauliZ ℓ m) :
    M ℓ m ⊕ M ℓ m → ZMod 2 :=
  fun
    | Sum.inl α => P.leftPoly α
    | Sum.inr α => P.rightPoly α

end BivariateBicycleCode

/-! ## Section 11: Order Properties of x and y -/

/-- x^ℓ = 1 in the group algebra (since ℓ · (1, 0) = (0, 0) in ZMod ℓ × ZMod m). -/
theorem cyclicShiftX_order :
    monomial ℓ m (ℓ : ZMod ℓ) 0 = monomial ℓ m 0 0 := by
  simp [monomial, ZMod.natCast_self]

/-- y^m = 1 in the group algebra (since m · (0, 1) = (0, 0) in ZMod ℓ × ZMod m). -/
theorem cyclicShiftY_order :
    monomial ℓ m 0 (m : ZMod m) = monomial ℓ m 0 0 := by
  simp [monomial, ZMod.natCast_self]

/-! ## Section 12: The Cyclic Permutation Matrix

C_r is the permutation matrix for the cyclic shift i ↦ i + 1 on ZMod r.
We define it using Equiv.Perm and relate it to the group algebra representation. -/

/-- The cyclic permutation on ZMod r: i ↦ i + 1. -/
def cyclicPerm (r : ℕ) [NeZero r] : Equiv.Perm (ZMod r) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := by ring
  right_inv i := by ring

/-- x as a permutation on M = ZMod ℓ × ZMod m: (a, b) ↦ (a + 1, b). -/
def permX : Equiv.Perm (M ℓ m) where
  toFun := fun p => (p.1 + 1, p.2)
  invFun := fun p => (p.1 - 1, p.2)
  left_inv := fun p => by ext <;> simp [sub_add_cancel]
  right_inv := fun p => by ext <;> simp [add_sub_cancel_right]

/-- y as a permutation on M = ZMod ℓ × ZMod m: (a, b) ↦ (a, b + 1). -/
def permY : Equiv.Perm (M ℓ m) where
  toFun := fun p => (p.1, p.2 + 1)
  invFun := fun p => (p.1, p.2 - 1)
  left_inv := fun p => by ext <;> simp [sub_add_cancel]
  right_inv := fun p => by ext <;> simp [add_sub_cancel_right]

/-- x and y commute as permutations. -/
theorem permX_permY_comm :
    (permX ℓ m).trans (permY ℓ m) = (permY ℓ m).trans (permX ℓ m) := by
  ext p <;> simp [permX, permY, Equiv.trans_apply]

/-- The permutation matrix of x is orthogonal: xᵀx = I. -/
theorem permX_transpose_mul [DecidableEq (M ℓ m)] :
    ((permX ℓ m).permMatrix (ZMod 2))ᵀ * (permX ℓ m).permMatrix (ZMod 2) = 1 := by
  rw [transpose_permMatrix]
  simp [← permMatrix_mul, permMatrix_refl]

/-- The permutation matrix of y is orthogonal: yᵀy = I. -/
theorem permY_transpose_mul [DecidableEq (M ℓ m)] :
    ((permY ℓ m).permMatrix (ZMod 2))ᵀ * (permY ℓ m).permMatrix (ZMod 2) = 1 := by
  rw [transpose_permMatrix]
  simp [← permMatrix_mul, permMatrix_refl]

end QEC1.BivariateBicycle
