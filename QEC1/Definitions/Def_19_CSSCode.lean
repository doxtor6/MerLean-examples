import QEC1.Definitions.Def_1_StabilizerCode

/-!
# CSS Code (Definition 19)

## Statement
A **CSS (Calderbank-Shor-Steane) code** is a stabilizer code where every stabilizer generator
is either purely X-type or purely Z-type.

Formally, an [[n, k, d]] CSS code is specified by two classical linear codes:
- C_X ⊆ F_2^n with parity check matrix H_X
- C_Z ⊆ F_2^n with parity check matrix H_Z

satisfying the **CSS condition**: H_X H_Z^T = 0 (equivalently, C_Z^⊥ ⊆ C_X).

**Stabilizer generators**:
- X-type: {∏_{i : (H_X)_{j,i} = 1} X_i} for each row j of H_X
- Z-type: {∏_{i : (H_Z)_{j,i} = 1} Z_i} for each row j of H_Z

**Code parameters**:
- n = number of physical qubits
- k = dim(C_X) + dim(C_Z) - n = number of logical qubits
- d = min(d_X, d_Z) where d_X = min{|c| : c ∈ C_X \ C_Z^⊥} and d_Z = min{|c| : c ∈ C_Z \ C_X^⊥}

## Main Results
**Main Structure** (`CSSCode`): CSS code with parity check matrices and CSS condition
- `H_X`: X-type parity check matrix
- `H_Z`: Z-type parity check matrix
- `css_condition`: H_X * H_Z^T = 0

## File Structure
1. Classical Linear Code: Representation via parity check matrix
2. CSS Condition: Orthogonality of X and Z parity check matrices
3. CSS Code Structure: Full CSS code definition
4. Stabilizer Generators: X-type and Z-type generators
5. Code Parameters: n, k, d for CSS codes
6. Helper Lemmas: Basic properties
-/

namespace QEC

open Matrix

/-! ## Section 1: Binary Vectors and Linear Codes -/

/-- A binary vector of length n -/
abbrev BinaryVector (n : ℕ) := Fin n → ZMod 2

/-- The Hamming weight (number of nonzero entries) of a binary vector -/
def hammingWeight {n : ℕ} (v : BinaryVector n) : ℕ :=
  Finset.card (Finset.filter (fun i => v i ≠ 0) Finset.univ)

/-- Zero vector has weight 0 -/
theorem hammingWeight_zero (n : ℕ) : hammingWeight (fun _ : Fin n => (0 : ZMod 2)) = 0 := by
  unfold hammingWeight
  simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty]

/-- A classical linear code over F_2 represented by its parity check matrix.
    The code C is the kernel of H: C = {v ∈ F_2^n : H v = 0} -/
structure ClassicalLinearCode (n r : ℕ) where
  /-- The parity check matrix with r rows and n columns -/
  parityCheckMatrix : Matrix (Fin r) (Fin n) (ZMod 2)

namespace ClassicalLinearCode

variable {n r : ℕ}

/-- A vector is a codeword if it's in the kernel of H -/
def isCodeword (C : ClassicalLinearCode n r) (v : BinaryVector n) : Prop :=
  C.parityCheckMatrix.mulVec v = 0

/-- The syndrome of a vector under the parity check matrix -/
def syndrome (C : ClassicalLinearCode n r) (v : BinaryVector n) : Fin r → ZMod 2 :=
  C.parityCheckMatrix.mulVec v

/-- Zero vector is always a codeword -/
theorem zero_isCodeword (C : ClassicalLinearCode n r) :
    C.isCodeword (fun _ => 0) := by
  simp only [isCodeword]
  funext i
  simp only [mulVec, dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Codewords have zero syndrome -/
theorem codeword_syndrome_zero (C : ClassicalLinearCode n r) (v : BinaryVector n)
    (h : C.isCodeword v) : C.syndrome v = 0 := h

end ClassicalLinearCode

/-! ## Section 2: Row Support and Stabilizer Generators -/

/-- The support of a row of a binary matrix (positions where entry is 1) -/
def rowSupport {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (j : Fin r) : Finset (Fin n) :=
  Finset.filter (fun i => H j i = 1) Finset.univ

/-- The support of a column of a binary matrix -/
def colSupport {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (i : Fin n) : Finset (Fin r) :=
  Finset.filter (fun j => H j i = 1) Finset.univ

/-- In ZMod 2, every element is either 0 or 1 -/
theorem ZMod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

/-- Row support is empty iff row is zero -/
theorem rowSupport_empty_iff {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (j : Fin r) :
    rowSupport H j = ∅ ↔ ∀ i, H j i = 0 := by
  simp only [rowSupport, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  constructor
  · intro hsupp k
    by_contra hne
    rcases ZMod2_eq_zero_or_one (H j k) with h0 | h1
    · exact hne h0
    · exact hsupp h1
  · intro hall k hk
    rw [hall k] at hk
    exact absurd hk (by decide : (0 : ZMod 2) ≠ 1)

/-! ## Section 3: CSS Condition -/

/-- The CSS condition: H_X * H_Z^T = 0
    This ensures that X-type and Z-type stabilizers commute. -/
def cssCondition {n rX rZ : ℕ}
    (H_X : Matrix (Fin rX) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin rZ) (Fin n) (ZMod 2)) : Prop :=
  H_X * H_Z.transpose = 0

/-- Alternative characterization: each row of H_X is orthogonal to each row of H_Z -/
theorem cssCondition_iff_orthogonal {n rX rZ : ℕ}
    (H_X : Matrix (Fin rX) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin rZ) (Fin n) (ZMod 2)) :
    cssCondition H_X H_Z ↔
    ∀ (i : Fin rX) (j : Fin rZ), ∑ k, H_X i k * H_Z j k = 0 := by
  unfold cssCondition
  constructor
  · intro h i j
    have h' := congr_fun (congr_fun h i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h'
    exact h'
  · intro h
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
    exact h i j

/-- The CSS condition implies each X-row is orthogonal to each Z-row -/
theorem cssCondition_row_orthogonal {n rX rZ : ℕ}
    (H_X : Matrix (Fin rX) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin rZ) (Fin n) (ZMod 2))
    (h : cssCondition H_X H_Z) (i : Fin rX) (j : Fin rZ) :
    ∑ k, H_X i k * H_Z j k = 0 := by
  rw [cssCondition_iff_orthogonal] at h
  exact h i j

/-! ## Section 4: CSS Code Structure -/

/-- A CSS (Calderbank-Shor-Steane) code.
    Parameters:
    - n: number of physical qubits
    - rX: number of X-type stabilizer generators (rows of H_X)
    - rZ: number of Z-type stabilizer generators (rows of H_Z) -/
structure CSSCode (n rX rZ : ℕ) where
  /-- X-type parity check matrix (rX × n) -/
  H_X : Matrix (Fin rX) (Fin n) (ZMod 2)
  /-- Z-type parity check matrix (rZ × n) -/
  H_Z : Matrix (Fin rZ) (Fin n) (ZMod 2)
  /-- The CSS condition: H_X * H_Z^T = 0 -/
  css_condition : cssCondition H_X H_Z

namespace CSSCode

variable {n rX rZ : ℕ}

/-! ## Section 5: Stabilizer Generators -/

/-- X-type stabilizer generator from row j of H_X.
    This is a pure X-type operator: ∏_{i : (H_X)_{j,i} = 1} X_i -/
def xGenerator (C : CSSCode n rX rZ) (j : Fin rX) : StabilizerCheck n where
  supportX := rowSupport C.H_X j
  supportZ := ∅
  phase := Phase.one

/-- Z-type stabilizer generator from row j of H_Z.
    This is a pure Z-type operator: ∏_{i : (H_Z)_{j,i} = 1} Z_i -/
def zGenerator (C : CSSCode n rX rZ) (j : Fin rZ) : StabilizerCheck n where
  supportX := ∅
  supportZ := rowSupport C.H_Z j
  phase := Phase.one

/-- X generators have empty Z support -/
@[simp]
theorem xGenerator_supportZ_empty (C : CSSCode n rX rZ) (j : Fin rX) :
    (C.xGenerator j).supportZ = ∅ := rfl

/-- Z generators have empty X support -/
@[simp]
theorem zGenerator_supportX_empty (C : CSSCode n rX rZ) (j : Fin rZ) :
    (C.zGenerator j).supportX = ∅ := rfl

/-- X generators have trivial phase -/
@[simp]
theorem xGenerator_phase (C : CSSCode n rX rZ) (j : Fin rX) :
    (C.xGenerator j).phase = Phase.one := rfl

/-- Z generators have trivial phase -/
@[simp]
theorem zGenerator_phase (C : CSSCode n rX rZ) (j : Fin rZ) :
    (C.zGenerator j).phase = Phase.one := rfl

/-! ## Section 6: Commutation -/

/-- Two X generators always commute (no XZ overlap) -/
theorem xGenerators_commute (C : CSSCode n rX rZ) (i j : Fin rX) :
    StabilizerCheck.commutes (C.xGenerator i) (C.xGenerator j) := by
  unfold StabilizerCheck.commutes xGenerator
  simp only [Finset.inter_empty, Finset.card_empty, Finset.empty_inter, Nat.add_zero, Nat.zero_mod]

/-- Two Z generators always commute (no XZ overlap) -/
theorem zGenerators_commute (C : CSSCode n rX rZ) (i j : Fin rZ) :
    StabilizerCheck.commutes (C.zGenerator i) (C.zGenerator j) := by
  unfold StabilizerCheck.commutes zGenerator
  simp only [Finset.empty_inter, Finset.card_empty, Finset.inter_empty, Nat.add_zero, Nat.zero_mod]

/-- X and Z generators commute due to CSS condition.
    The overlap |supp_X(X_i) ∩ supp_Z(Z_j)| = |{k : H_X(i,k)=1 ∧ H_Z(j,k)=1}|
    is even by the CSS condition. -/
theorem xz_generators_commute (C : CSSCode n rX rZ) (i : Fin rX) (j : Fin rZ) :
    StabilizerCheck.commutes (C.xGenerator i) (C.zGenerator j) := by
  unfold StabilizerCheck.commutes xGenerator zGenerator
  simp only [Finset.inter_empty, Finset.card_empty, Nat.add_zero]
  -- Need to show |rowSupport H_X i ∩ rowSupport H_Z j| % 2 = 0
  -- This follows from CSS condition: ∑_k H_X(i,k) * H_Z(j,k) = 0
  have hcss := cssCondition_row_orthogonal C.H_X C.H_Z C.css_condition i j
  -- The sum ∑_k H_X(i,k) * H_Z(j,k) equals the cardinality of the intersection mod 2
  -- First, show elements inside intersection contribute 1 each
  have h1 : ∀ k ∈ rowSupport C.H_X i ∩ rowSupport C.H_Z j, C.H_X i k * C.H_Z j k = 1 := by
    intro k hk
    simp only [rowSupport, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and] at hk
    simp only [hk.1, hk.2, mul_one]
  -- Elements outside the intersection contribute 0
  have h2 : ∀ k ∈ Finset.univ \ (rowSupport C.H_X i ∩ rowSupport C.H_Z j),
            C.H_X i k * C.H_Z j k = 0 := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_inter] at hk
    simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    push_neg at hk
    rcases ZMod2_eq_zero_or_one (C.H_X i k) with hX0 | hX1
    · simp only [hX0, zero_mul]
    · rcases ZMod2_eq_zero_or_one (C.H_Z j k) with hZ0 | hZ1
      · simp only [hZ0, mul_zero]
      · exfalso; exact hk hX1 hZ1
  -- The sum over all k equals sum over intersection
  let S := rowSupport C.H_X i ∩ rowSupport C.H_Z j
  have hsplit : ∑ k : Fin n, C.H_X i k * C.H_Z j k = ∑ k ∈ S, C.H_X i k * C.H_Z j k := by
    have hsubset : S ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_sdiff hsubset]
    have hzero : ∑ k ∈ Finset.univ \ S, C.H_X i k * C.H_Z j k = 0 := Finset.sum_eq_zero h2
    rw [hzero, zero_add]
  -- Sum over intersection equals cardinality
  have hcard_sum : ∑ k ∈ S, C.H_X i k * C.H_Z j k = (S.card : ZMod 2) := by
    have heq1 : ∑ k ∈ S, C.H_X i k * C.H_Z j k = ∑ _k ∈ S, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact h1 k hk
    rw [heq1, Finset.sum_const]
    simp only [nsmul_eq_mul, mul_one]
  -- Combine: sum = card
  have heq : (∑ k : Fin n, C.H_X i k * C.H_Z j k) = (S.card : ZMod 2) := by
    rw [hsplit, hcard_sum]
  -- CSS gives sum = 0, so card ≡ 0 (mod 2)
  rw [hcss] at heq
  have heq' : (S.card : ZMod 2) = 0 := heq.symm
  rw [ZMod.natCast_eq_zero_iff] at heq'
  exact Nat.mod_eq_zero_of_dvd heq'

/-- Z and X generators commute (symmetry) -/
theorem zx_generators_commute (C : CSSCode n rX rZ) (j : Fin rZ) (i : Fin rX) :
    StabilizerCheck.commutes (C.zGenerator j) (C.xGenerator i) := by
  rw [StabilizerCheck.commutes_symm]
  exact xz_generators_commute C i j

/-! ## Section 7: Code Parameters -/

/-- Number of physical qubits -/
def numQubits (_C : CSSCode n rX rZ) : ℕ := n

/-- Number of X-type generators -/
def numXGenerators (_C : CSSCode n rX rZ) : ℕ := rX

/-- Number of Z-type generators -/
def numZGenerators (_C : CSSCode n rX rZ) : ℕ := rZ

/-- Total number of stabilizer generators -/
def numGenerators (_C : CSSCode n rX rZ) : ℕ := rX + rZ

/-- Weight of X-type generator j -/
def xGeneratorWeight (C : CSSCode n rX rZ) (j : Fin rX) : ℕ :=
  (C.xGenerator j).weight

/-- Weight of Z-type generator j -/
def zGeneratorWeight (C : CSSCode n rX rZ) (j : Fin rZ) : ℕ :=
  (C.zGenerator j).weight

/-- X generator weight equals row support size -/
theorem xGeneratorWeight_eq_rowSupport (C : CSSCode n rX rZ) (j : Fin rX) :
    C.xGeneratorWeight j = (rowSupport C.H_X j).card := by
  unfold xGeneratorWeight StabilizerCheck.weight xGenerator
  simp only [Finset.union_empty]

/-- Z generator weight equals row support size -/
theorem zGeneratorWeight_eq_rowSupport (C : CSSCode n rX rZ) (j : Fin rZ) :
    C.zGeneratorWeight j = (rowSupport C.H_Z j).card := by
  unfold zGeneratorWeight StabilizerCheck.weight zGenerator
  simp only [Finset.empty_union]

/-! ## Section 8: X-distance and Z-distance -/

/-- X-type logical operator: a vector in ker(H_Z) \ C_Z^⊥
    Equivalently, a vector that satisfies Z parity checks but is not in the span of
    row space of H_X -/
def isXLogical (C : CSSCode n rX rZ) (v : BinaryVector n) : Prop :=
  -- v ∈ C_Z (satisfies Z parity checks)
  C.H_Z.mulVec v = 0 ∧
  -- v is not in the row space of H_X (has nontrivial X-logical action)
  ¬(∀ (u : BinaryVector n), C.H_X.mulVec u = 0 → ∑ k, v k * u k = 0)

/-- Z-type logical operator: a vector in ker(H_X) \ C_X^⊥ -/
def isZLogical (C : CSSCode n rX rZ) (v : BinaryVector n) : Prop :=
  -- v ∈ C_X (satisfies X parity checks)
  C.H_X.mulVec v = 0 ∧
  -- v is not in the row space of H_Z (has nontrivial Z-logical action)
  ¬(∀ (u : BinaryVector n), C.H_Z.mulVec u = 0 → ∑ k, v k * u k = 0)

/-- Minimum X-distance: infimum of weights of X-type logical operators -/
noncomputable def minXDistance (C : CSSCode n rX rZ) : ℕ :=
  ⨅ (v : BinaryVector n) (_ : C.isXLogical v), hammingWeight v

/-- Minimum Z-distance: infimum of weights of Z-type logical operators -/
noncomputable def minZDistance (C : CSSCode n rX rZ) : ℕ :=
  ⨅ (v : BinaryVector n) (_ : C.isZLogical v), hammingWeight v

/-- Code distance: minimum of X-distance and Z-distance -/
noncomputable def distance (C : CSSCode n rX rZ) : ℕ := min (C.minXDistance) (C.minZDistance)

end CSSCode

/-! ## Section 9: Helper Lemmas -/

/-- CSS condition is symmetric in a sense: H_X H_Z^T = 0 iff H_Z H_X^T = 0 -/
theorem cssCondition_symm {n rX rZ : ℕ}
    (H_X : Matrix (Fin rX) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin rZ) (Fin n) (ZMod 2)) :
    cssCondition H_X H_Z ↔ cssCondition H_Z H_X := by
  unfold cssCondition
  constructor
  · intro h
    ext i j
    have h' := congr_fun (congr_fun h j) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h' ⊢
    convert h' using 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro h
    ext i j
    have h' := congr_fun (congr_fun h j) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h' ⊢
    convert h' using 1
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- X generator is purely X-type -/
@[simp]
theorem CSSCode.xGenerator_isPureX {n rX rZ : ℕ} (C : CSSCode n rX rZ) (j : Fin rX) :
    (C.xGenerator j).supportZ = ∅ := rfl

/-- Z generator is purely Z-type -/
@[simp]
theorem CSSCode.zGenerator_isPureZ {n rX rZ : ℕ} (C : CSSCode n rX rZ) (j : Fin rZ) :
    (C.zGenerator j).supportX = ∅ := rfl

/-- Row support of zero matrix is empty -/
theorem rowSupport_zero {r n : ℕ} (j : Fin r) :
    rowSupport (0 : Matrix (Fin r) (Fin n) (ZMod 2)) j = ∅ := by
  simp only [rowSupport, Matrix.zero_apply]
  rw [Finset.filter_eq_empty_iff]
  intro i _
  decide

/-- CSS condition holds for zero matrices -/
theorem cssCondition_zero (n rX rZ : ℕ) :
    cssCondition (0 : Matrix (Fin rX) (Fin n) (ZMod 2))
                 (0 : Matrix (Fin rZ) (Fin n) (ZMod 2)) := by
  unfold cssCondition
  simp only [Matrix.zero_mul]

/-- A CSS code with zero X-matrix has X generators with empty support -/
theorem CSSCode.xGenerator_zero {n rX rZ : ℕ}
    (C : CSSCode n rX rZ) (h : C.H_X = 0) (j : Fin rX) :
    (C.xGenerator j).supportX = ∅ := by
  simp only [CSSCode.xGenerator, h, rowSupport_zero]

/-- Number of qubits is n -/
@[simp]
theorem CSSCode.numQubits_eq {n rX rZ : ℕ} (C : CSSCode n rX rZ) :
    C.numQubits = n := rfl

/-- Number of X generators is rX -/
@[simp]
theorem CSSCode.numXGenerators_eq {n rX rZ : ℕ} (C : CSSCode n rX rZ) :
    C.numXGenerators = rX := rfl

/-- Number of Z generators is rZ -/
@[simp]
theorem CSSCode.numZGenerators_eq {n rX rZ : ℕ} (C : CSSCode n rX rZ) :
    C.numZGenerators = rZ := rfl

/-- X and Z generators together span the stabilizer group -/
theorem CSSCode.all_generators_commute {n rX rZ : ℕ} (C : CSSCode n rX rZ)
    (s : StabilizerCheck n)
    (hs : (∃ i, s = C.xGenerator i) ∨ (∃ j, s = C.zGenerator j))
    (t : StabilizerCheck n)
    (ht : (∃ i, t = C.xGenerator i) ∨ (∃ j, t = C.zGenerator j)) :
    StabilizerCheck.commutes s t := by
  rcases hs with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rcases ht with ⟨i', rfl⟩ | ⟨j', rfl⟩
    · exact C.xGenerators_commute i i'
    · exact C.xz_generators_commute i j'
  · rcases ht with ⟨i', rfl⟩ | ⟨j', rfl⟩
    · exact C.zx_generators_commute j i'
    · exact C.zGenerators_commute j j'

end QEC
