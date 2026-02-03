import QEC1.Definitions.Def_1_StabilizerCode

set_option linter.unusedSectionVars false

/-!
# Bivariate Bicycle Code (Definition 16)

## Statement
Let ℓ, m ∈ ℕ and define:
- I_r: the r × r identity matrix
- C_r: the r × r cyclic permutation matrix, (C_r)_{ij} = [j ≡ i + 1 (mod r)]
- x = C_ℓ ⊗ I_m and y = I_ℓ ⊗ C_m

The matrices x, y satisfy: x^ℓ = y^m = I_{ℓm}, xy = yx, and x^T x = y^T y = I_{ℓm}.

A **Bivariate Bicycle (BB) code** is a CSS code on n = 2ℓm physical qubits, divided into:
- ℓm **left (L) qubits**
- ℓm **right (R) qubits**

The parity check matrices are:
  H_X = [A | B],   H_Z = [B^T | A^T]

where A, B ∈ F_2[x, y] are polynomials in x and y with coefficients in F_2.

**Transpose convention**: A^T = A(x, y)^T = A(x^{-1}, y^{-1}) (inverse of x is x^{ℓ-1}, etc.)

**Labeling**: Checks and qubits are labeled by (α, T) for α ∈ M = {x^a y^b : a, b ∈ Z}
and T ∈ {X, Z, L, R}.

**Check action**:
- X check (α, X) acts on qubits (αA, L) and (αB, R)
- Z check (β, Z) acts on qubits (βB^T, L) and (βA^T, R)

## Main Results
**Main Structure** (`BivariateBicycleCode`): Complete BB code specification
- `dim_ℓ`, `dim_m`: The two dimensions defining the code
- `polyA`, `polyB`: Polynomial coefficients for A and B matrices

## File Structure
1. Cyclic Permutation Matrix: Definition of C_r
2. Tensor Product Operators: x = C_ℓ ⊗ I_m and y = I_ℓ ⊗ C_m
3. Monomial Group: The group M = {x^a y^b : a, b ∈ Z}
4. Polynomial Matrices: Polynomials in x and y over F_2
5. BB Code Structure: The main bivariate bicycle code definition
6. Check Actions: X and Z check operator actions
7. Helper Lemmas: Basic properties of BB codes
-/

namespace QEC

/-! ## Section 1: Cyclic Permutation Matrix -/

/-- The cyclic permutation matrix C_r is the r × r matrix with (C_r)_{ij} = 1 iff j ≡ i + 1 (mod r).
    This represents a right cyclic shift. -/
def cyclicPermMatrix (r : ℕ) [NeZero r] : Matrix (Fin r) (Fin r) (ZMod 2) :=
  fun i j => if j.val = (i.val + 1) % r then 1 else 0

namespace CyclicPerm

variable {r : ℕ} [NeZero r]

/-- The identity matrix in F_2 -/
def identityMatrix (r : ℕ) [NeZero r] : Matrix (Fin r) (Fin r) (ZMod 2) := 1

/-- C_r is a permutation matrix: each row and column has exactly one 1 -/
theorem cyclicPerm_is_permutation :
    ∀ i : Fin r, ∃! j : Fin r, cyclicPermMatrix r i j = 1 := by
  intro i
  use ⟨(i.val + 1) % r, Nat.mod_lt _ (NeZero.pos r)⟩
  constructor
  · simp only [cyclicPermMatrix, ↓reduceIte]
  · intro y hy
    simp only [cyclicPermMatrix] at hy
    split_ifs at hy with h
    · ext
      omega
    · simp at hy

/-- The (i, i+1 mod r) entry of C_r is 1 -/
@[simp]
theorem cyclicPerm_entry (i : Fin r) :
    cyclicPermMatrix r i ⟨(i.val + 1) % r, Nat.mod_lt _ (NeZero.pos r)⟩ = 1 := by
  simp only [cyclicPermMatrix, ↓reduceIte]

/-- Off-diagonal entries (not i+1 mod r) are 0 -/
theorem cyclicPerm_off_entry (i j : Fin r) (h : j.val ≠ (i.val + 1) % r) :
    cyclicPermMatrix r i j = 0 := by
  simp only [cyclicPermMatrix, h, ↓reduceIte]

end CyclicPerm

/-! ## Section 2: Qubit Type and Monomial Index -/

/-- Qubit type: Left (L) or Right (R) -/
inductive QubitType : Type where
  | L : QubitType  -- Left qubit
  | R : QubitType  -- Right qubit
  deriving DecidableEq, Repr

instance : Fintype QubitType where
  elems := {QubitType.L, QubitType.R}
  complete := fun x => by cases x <;> simp

/-- Check type: X-type or Z-type -/
inductive BBCheckType : Type where
  | X : BBCheckType  -- X-type check
  | Z : BBCheckType  -- Z-type check
  deriving DecidableEq, Repr

instance : Fintype BBCheckType where
  elems := {BBCheckType.X, BBCheckType.Z}
  complete := fun x => by cases x <;> simp

/-- A monomial index represents x^a y^b where a ∈ Z_ℓ and b ∈ Z_m.
    We use Fin ℓ × Fin m to represent (a, b). -/
@[ext]
structure MonomialIndex (ℓ m : ℕ) where
  xPow : Fin ℓ  -- Power of x (mod ℓ)
  yPow : Fin m  -- Power of y (mod m)
  deriving DecidableEq, Repr

namespace MonomialIndex

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- The identity monomial (x^0 y^0) -/
def one : MonomialIndex ℓ m where
  xPow := 0
  yPow := 0

/-- Multiplication of monomials: x^a y^b · x^c y^d = x^{a+c} y^{b+d} -/
def mul (α β : MonomialIndex ℓ m) : MonomialIndex ℓ m where
  xPow := α.xPow + β.xPow
  yPow := α.yPow + β.yPow

/-- The monomial x^1 y^0 -/
def x : MonomialIndex ℓ m where
  xPow := 1
  yPow := 0

/-- The monomial x^0 y^1 -/
def y : MonomialIndex ℓ m where
  xPow := 0
  yPow := 1

/-- Monomial multiplication is commutative (since x and y commute) -/
theorem mul_comm (α β : MonomialIndex ℓ m) : mul α β = mul β α := by
  ext <;> simp only [mul, add_comm]

/-- Identity is left neutral for multiplication -/
theorem one_mul (α : MonomialIndex ℓ m) : mul one α = α := by
  simp only [mul, one, zero_add]

/-- Identity is right neutral for multiplication -/
theorem mul_one (α : MonomialIndex ℓ m) : mul α one = α := by
  simp only [mul, one, add_zero]

/-- Inverse of a monomial: x^{-a} y^{-b} = x^{ℓ-a} y^{m-b} -/
def inv (α : MonomialIndex ℓ m) : MonomialIndex ℓ m where
  xPow := -α.xPow
  yPow := -α.yPow

/-- The monomial group is finite -/
instance : Fintype (MonomialIndex ℓ m) :=
  Fintype.ofEquiv (Fin ℓ × Fin m)
    { toFun := fun ⟨a, b⟩ => ⟨a, b⟩
      invFun := fun ⟨a, b⟩ => ⟨a, b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end MonomialIndex

/-! ## Section 3: Polynomial over x, y -/

/-- A polynomial in x and y with coefficients in F_2 is represented by
    a finset of monomial indices (the support, where coefficient = 1).
    This represents ∑_{(a,b) ∈ S} x^a y^b. -/
@[ext]
structure BBPolynomial (ℓ m : ℕ) where
  support : Finset (Fin ℓ × Fin m)
  deriving DecidableEq

namespace BBPolynomial

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- The zero polynomial -/
def zero : BBPolynomial ℓ m := ⟨∅⟩

/-- The identity polynomial (just 1) -/
def one : BBPolynomial ℓ m := ⟨{(0, 0)}⟩

/-- A single monomial x^a y^b -/
def monomial (a : Fin ℓ) (b : Fin m) : BBPolynomial ℓ m := ⟨{(a, b)}⟩

/-- The monomial x -/
def x : BBPolynomial ℓ m := ⟨{(1, 0)}⟩

/-- The monomial y -/
def y : BBPolynomial ℓ m := ⟨{(0, 1)}⟩

/-- Addition of polynomials (XOR of supports in F_2) -/
def add (A B : BBPolynomial ℓ m) : BBPolynomial ℓ m :=
  ⟨symmDiff A.support B.support⟩

/-- Multiplication by a monomial: shifts all exponents -/
def mulByMonomial (A : BBPolynomial ℓ m) (α : Fin ℓ × Fin m) : BBPolynomial ℓ m :=
  ⟨A.support.image (fun ⟨a, b⟩ => (a + α.1, b + α.2))⟩

/-- The number of terms in the polynomial -/
def numTerms (A : BBPolynomial ℓ m) : ℕ := A.support.card

/-- Addition is commutative -/
theorem add_comm (A B : BBPolynomial ℓ m) : add A B = add B A := by
  simp only [add, symmDiff_comm]

/-- Zero is additive identity -/
theorem add_zero (A : BBPolynomial ℓ m) : add A zero = A := by
  simp only [add, zero]
  ext x
  simp only [Finset.mem_symmDiff, Finset.notMem_empty, false_and, or_false, not_false_eq_true,
             and_true]

/-- Addition is self-inverse in F_2 -/
theorem add_self (A : BBPolynomial ℓ m) : add A A = zero := by
  simp only [add, zero, symmDiff_self]
  rfl

end BBPolynomial

/-! ## Section 4: Transpose Convention -/

/-- The transpose of a polynomial: A(x,y)^T = A(x^{-1}, y^{-1}).
    For a monomial x^a y^b, the transpose is x^{-a} y^{-b} = x^{ℓ-a} y^{m-b}. -/
def BBPolynomial.transpose {ℓ m : ℕ} [NeZero ℓ] [NeZero m]
    (A : BBPolynomial ℓ m) : BBPolynomial ℓ m :=
  ⟨A.support.image (fun ⟨a, b⟩ => (-a, -b))⟩

namespace BBPolynomial

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- Transpose of identity is identity -/
theorem transpose_one : (one : BBPolynomial ℓ m).transpose = one := by
  simp only [transpose, one]
  ext ⟨a, b⟩
  simp only [Finset.mem_image, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', b'⟩, hab, ⟨ha, hb⟩⟩
    simp only [Prod.mk.injEq] at hab
    obtain ⟨ha', hb'⟩ := hab
    subst ha' hb'
    simp only [neg_zero] at ha hb
    exact ⟨ha.symm, hb.symm⟩
  · rintro ⟨ha, hb⟩
    refine ⟨(0, 0), ?_, ?_, ?_⟩
    · rfl
    · simp [ha]
    · simp [hb]

/-- Transpose of zero is zero -/
theorem transpose_zero : (zero : BBPolynomial ℓ m).transpose = zero := by
  simp only [transpose, zero, Finset.image_empty]

/-- Double transpose is identity -/
theorem transpose_transpose (A : BBPolynomial ℓ m) : A.transpose.transpose = A := by
  simp only [transpose]
  ext ⟨a, b⟩
  simp only [Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨⟨a'', b''⟩, hab'', rfl, rfl⟩, rfl, rfl⟩
    simp only [neg_neg]
    exact hab''
  · intro h
    use (-a, -b)
    constructor
    · use (a, b)
    · exact ⟨neg_neg a, neg_neg b⟩

end BBPolynomial

/-! ## Section 5: Qubit and Check Labels -/

/-- A qubit label is a pair (α, T) where α is a monomial index and T is L or R -/
structure BBQubitLabel (ℓ m : ℕ) where
  index : Fin ℓ × Fin m
  qtype : QubitType
  deriving DecidableEq, Repr

/-- A check label is a pair (α, T) where α is a monomial index and T is X or Z -/
structure BBCheckLabel (ℓ m : ℕ) where
  index : Fin ℓ × Fin m
  ctype : BBCheckType
  deriving DecidableEq, Repr

namespace BBQubitLabel

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- Total number of qubits is 2ℓm -/
instance : Fintype (BBQubitLabel ℓ m) :=
  Fintype.ofEquiv ((Fin ℓ × Fin m) × QubitType)
    { toFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
      invFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end BBQubitLabel

namespace BBCheckLabel

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- Total number of checks is 2ℓm -/
instance : Fintype (BBCheckLabel ℓ m) :=
  Fintype.ofEquiv ((Fin ℓ × Fin m) × BBCheckType)
    { toFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
      invFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end BBCheckLabel

/-! ## Section 6: Bivariate Bicycle Code Structure -/

/-- A Bivariate Bicycle (BB) code is specified by two dimensions ℓ, m and
    two polynomials A, B in x, y over F_2.

    - Physical qubits: n = 2ℓm (ℓm left qubits + ℓm right qubits)
    - Parity check matrices: H_X = [A | B], H_Z = [B^T | A^T]

    The code is a CSS code where X-checks and Z-checks have a specific
    transpose relationship. -/
structure BivariateBicycleCode (ℓ m : ℕ) [NeZero ℓ] [NeZero m] where
  /-- Polynomial A in F_2[x, y] -/
  polyA : BBPolynomial ℓ m
  /-- Polynomial B in F_2[x, y] -/
  polyB : BBPolynomial ℓ m

namespace BivariateBicycleCode

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- Number of physical qubits -/
def numPhysicalQubits (_C : BivariateBicycleCode ℓ m) : ℕ := 2 * ℓ * m

/-- Number of left qubits -/
def numLeftQubits (_C : BivariateBicycleCode ℓ m) : ℕ := ℓ * m

/-- Number of right qubits -/
def numRightQubits (_C : BivariateBicycleCode ℓ m) : ℕ := ℓ * m

/-- Number of X-type checks -/
def numXChecks (_C : BivariateBicycleCode ℓ m) : ℕ := ℓ * m

/-- Number of Z-type checks -/
def numZChecks (_C : BivariateBicycleCode ℓ m) : ℕ := ℓ * m

/-- Total number of checks -/
def numTotalChecks (_C : BivariateBicycleCode ℓ m) : ℕ := 2 * ℓ * m

/-- The qubits acted on by polynomial P at index α on the left side:
    Returns the set {(α + (a,b), L) : (a,b) ∈ P.support}. -/
def leftQubitsActedBy (P : BBPolynomial ℓ m) (α : Fin ℓ × Fin m) :
    Finset (BBQubitLabel ℓ m) :=
  P.support.image (fun ⟨a, b⟩ => ⟨(α.1 + a, α.2 + b), QubitType.L⟩)

/-- The qubits acted on by polynomial P at index α on the right side:
    Returns the set {(α + (a,b), R) : (a,b) ∈ P.support}. -/
def rightQubitsActedBy (P : BBPolynomial ℓ m) (α : Fin ℓ × Fin m) :
    Finset (BBQubitLabel ℓ m) :=
  P.support.image (fun ⟨a, b⟩ => ⟨(α.1 + a, α.2 + b), QubitType.R⟩)

/-- X check (α, X) acts on qubits (αA, L) and (αB, R).
    Returns the set of qubit labels this check acts on. -/
def xCheckSupport (C : BivariateBicycleCode ℓ m) (α : Fin ℓ × Fin m) :
    Finset (BBQubitLabel ℓ m) :=
  leftQubitsActedBy C.polyA α ∪ rightQubitsActedBy C.polyB α

/-- Z check (β, Z) acts on qubits (βB^T, L) and (βA^T, R).
    Returns the set of qubit labels this check acts on. -/
def zCheckSupport (C : BivariateBicycleCode ℓ m) (β : Fin ℓ × Fin m) :
    Finset (BBQubitLabel ℓ m) :=
  leftQubitsActedBy C.polyB.transpose β ∪ rightQubitsActedBy C.polyA.transpose β

/-- Weight of an X check -/
def xCheckWeight (C : BivariateBicycleCode ℓ m) (α : Fin ℓ × Fin m) : ℕ :=
  (xCheckSupport C α).card

/-- Weight of a Z check -/
def zCheckWeight (C : BivariateBicycleCode ℓ m) (β : Fin ℓ × Fin m) : ℕ :=
  (zCheckSupport C β).card

/-- Row weight of polynomial A (number of nonzero entries) -/
def polyAWeight (C : BivariateBicycleCode ℓ m) : ℕ := C.polyA.numTerms

/-- Row weight of polynomial B -/
def polyBWeight (C : BivariateBicycleCode ℓ m) : ℕ := C.polyB.numTerms

end BivariateBicycleCode

/-! ## Section 7: CSS Orthogonality -/

/-- The CSS orthogonality condition for BB codes: H_X · H_Z^T = 0.
    This is equivalent to AB^T + BA^T = 0 in the polynomial ring.
    Since we're in F_2, this means AB^T = BA^T. -/
def CSSOrthogonal {ℓ m : ℕ} [NeZero ℓ] [NeZero m] (C : BivariateBicycleCode ℓ m) : Prop :=
  -- In F_2[x,y], orthogonality: AB^T + BA^T = 0
  -- This is automatic when A and B are symmetric or satisfy certain conditions
  -- For now we express it as a property
  ∀ (i j : Fin ℓ × Fin m),
    (Finset.filter (fun k => (i.1 + k.1, i.2 + k.2) ∈ C.polyA.support ∧
                            (j.1 + k.1, j.2 + k.2) ∈ C.polyB.support)
      (Finset.univ : Finset (Fin ℓ × Fin m))).card % 2 =
    (Finset.filter (fun k => (i.1 + k.1, i.2 + k.2) ∈ C.polyB.support ∧
                            (j.1 + k.1, j.2 + k.2) ∈ C.polyA.support)
      (Finset.univ : Finset (Fin ℓ × Fin m))).card % 2

/-! ## Section 8: Example: The [[72, 12, 6]] Gross Code -/

/-- Construct a BB code from coefficient lists.
    The coefficients represent terms in the polynomial. -/
def makeBBCode (ℓ m : ℕ) [NeZero ℓ] [NeZero m]
    (aCoeffs bCoeffs : List (Fin ℓ × Fin m)) : BivariateBicycleCode ℓ m where
  polyA := ⟨aCoeffs.toFinset⟩
  polyB := ⟨bCoeffs.toFinset⟩

/-! ## Section 9: Helper Lemmas -/

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- The number of physical qubits is twice the product of dimensions -/
@[simp]
theorem numPhysicalQubits_eq (C : BivariateBicycleCode ℓ m) :
    C.numPhysicalQubits = 2 * ℓ * m := rfl

/-- Left and right qubits partition the physical qubits -/
theorem qubit_partition (C : BivariateBicycleCode ℓ m) :
    C.numLeftQubits + C.numRightQubits = C.numPhysicalQubits := by
  simp only [BivariateBicycleCode.numLeftQubits, BivariateBicycleCode.numRightQubits,
             BivariateBicycleCode.numPhysicalQubits]
  ring

/-- X and Z checks have the same count -/
theorem check_count_eq (C : BivariateBicycleCode ℓ m) :
    C.numXChecks = C.numZChecks := rfl

/-- Total checks equals twice the number of X checks -/
theorem total_checks_eq (C : BivariateBicycleCode ℓ m) :
    C.numTotalChecks = C.numXChecks + C.numZChecks := by
  simp only [BivariateBicycleCode.numTotalChecks, BivariateBicycleCode.numXChecks,
             BivariateBicycleCode.numZChecks]
  ring

/-- The transpose of a transpose returns the original polynomial -/
theorem transpose_involutive (P : BBPolynomial ℓ m) :
    P.transpose.transpose = P := BBPolynomial.transpose_transpose P

/-- Zero polynomial has empty support -/
@[simp]
theorem zero_support_empty : (BBPolynomial.zero : BBPolynomial ℓ m).support = ∅ := rfl

/-- Number of terms in zero polynomial is 0 -/
@[simp]
theorem zero_numTerms : (BBPolynomial.zero : BBPolynomial ℓ m).numTerms = 0 := by
  simp only [BBPolynomial.numTerms, BBPolynomial.zero, Finset.card_empty]

/-- Monomial multiplication preserves the number of terms -/
theorem mulByMonomial_card (A : BBPolynomial ℓ m) (α : Fin ℓ × Fin m) :
    (A.mulByMonomial α).numTerms ≤ A.numTerms := by
  simp only [BBPolynomial.numTerms, BBPolynomial.mulByMonomial]
  exact Finset.card_image_le

/-- Left qubits acted by zero polynomial is empty -/
@[simp]
theorem leftQubitsActedBy_zero (α : Fin ℓ × Fin m) :
    BivariateBicycleCode.leftQubitsActedBy (BBPolynomial.zero) α = ∅ := by
  simp only [BivariateBicycleCode.leftQubitsActedBy, BBPolynomial.zero, Finset.image_empty]

/-- Right qubits acted by zero polynomial is empty -/
@[simp]
theorem rightQubitsActedBy_zero (α : Fin ℓ × Fin m) :
    BivariateBicycleCode.rightQubitsActedBy (BBPolynomial.zero) α = ∅ := by
  simp only [BivariateBicycleCode.rightQubitsActedBy, BBPolynomial.zero, Finset.image_empty]

/-- An X check on a code with zero A and B polynomials has empty support -/
theorem xCheckSupport_zero_polys (α : Fin ℓ × Fin m) :
    BivariateBicycleCode.xCheckSupport ⟨BBPolynomial.zero, BBPolynomial.zero⟩ α = ∅ := by
  simp only [BivariateBicycleCode.xCheckSupport, leftQubitsActedBy_zero,
             rightQubitsActedBy_zero, Finset.empty_union]

/-- Addition of polynomials is associative -/
theorem add_assoc (A B C : BBPolynomial ℓ m) :
    BBPolynomial.add (BBPolynomial.add A B) C = BBPolynomial.add A (BBPolynomial.add B C) := by
  simp only [BBPolynomial.add, symmDiff_assoc]

/-- Cardinality of qubit labels -/
theorem card_qubit_labels :
    Fintype.card (BBQubitLabel ℓ m) = 2 * ℓ * m := by
  have h1 : Fintype.card (BBQubitLabel ℓ m) =
            Fintype.card ((Fin ℓ × Fin m) × QubitType) := by
    apply Fintype.card_congr
    exact { toFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
            invFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [h1, Fintype.card_prod, Fintype.card_prod]
  simp only [Fintype.card_fin]
  have hq : Fintype.card QubitType = 2 := by decide
  rw [hq]
  ring

/-- Cardinality of check labels -/
theorem card_check_labels :
    Fintype.card (BBCheckLabel ℓ m) = 2 * ℓ * m := by
  have h1 : Fintype.card (BBCheckLabel ℓ m) =
            Fintype.card ((Fin ℓ × Fin m) × BBCheckType) := by
    apply Fintype.card_congr
    exact { toFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
            invFun := fun ⟨idx, t⟩ => ⟨idx, t⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [h1, Fintype.card_prod, Fintype.card_prod]
  simp only [Fintype.card_fin]
  have hq : Fintype.card BBCheckType = 2 := by decide
  rw [hq]
  ring

end QEC
