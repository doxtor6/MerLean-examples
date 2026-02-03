import QEC1.Definitions.Def_1_StabilizerCode

/-!
# Commutation Condition for Pauli Operators (Lemma 8)

## Statement
Let P = i^{σ_P} ∏_v X_v^{a_v} Z_v^{b_v} and Q = i^{σ_Q} ∏_v X_v^{c_v} Z_v^{d_v}
be two Pauli operators.

Then P and Q commute ([P, Q] = 0) if and only if:
  ∑_v (a_v d_v + b_v c_v) ≡ 0 (mod 2)

Equivalently, using support notation:
  |S_X(P) ∩ S_Z(Q)| + |S_Z(P) ∩ S_X(Q)| ≡ 0 (mod 2)

This is the **symplectic inner product** condition.

## Main Results
**Main Theorem** (`commutationConditionPauli`): P and Q commute iff symplectic form = 0 mod 2
- Derives commutation from single-qubit anticommutation (XZ = -ZX)
- Connects support overlap to anticommuting operator count
- Shows the symplectic inner product equals the anticommuting overlap

## File Structure
1. Single-qubit Anticommutation: X and Z anticommute, proven from multiplication table
2. Anticommuting Overlap Equals Symplectic Form: Key lemma connecting the two
3. Main Theorem: Commutation iff symplectic inner product is 0 mod 2
4. Properties: Symmetry, reflexivity, derived results
-/

namespace QEC

/-! ## Section 1: Single-Qubit Anticommutation Analysis

The fundamental fact is that X and Z anticommute: XZ ≠ ZX (specifically, XZ = iY and ZX = -iY).
We formalize this by showing which pairs of single-qubit Paulis anticommute. -/

/-- Characterization: two single-qubit Paulis anticommute iff they are both non-trivial
    and different non-commuting pairs. This is proven by exhaustive case analysis. -/
theorem singleCommute_false_iff (P Q : PauliOp) :
    singleCommute P Q = false ↔
    (P = PauliOp.X ∧ Q = PauliOp.Z) ∨ (P = PauliOp.Z ∧ Q = PauliOp.X) ∨
    (P = PauliOp.X ∧ Q = PauliOp.Y) ∨ (P = PauliOp.Y ∧ Q = PauliOp.X) ∨
    (P = PauliOp.Z ∧ Q = PauliOp.Y) ∨ (P = PauliOp.Y ∧ Q = PauliOp.Z) := by
  cases P <;> cases Q <;> simp [singleCommute]

/-- X and Z anticommute -/
theorem X_Z_anticommute : singleCommute PauliOp.X PauliOp.Z = false := rfl

/-- Z and X anticommute -/
theorem Z_X_anticommute : singleCommute PauliOp.Z PauliOp.X = false := rfl

/-- X and Y anticommute -/
theorem X_Y_anticommute : singleCommute PauliOp.X PauliOp.Y = false := rfl

/-- Y and X anticommute -/
theorem Y_X_anticommute : singleCommute PauliOp.Y PauliOp.X = false := rfl

/-- Z and Y anticommute -/
theorem Z_Y_anticommute : singleCommute PauliOp.Z PauliOp.Y = false := rfl

/-- Y and Z anticommute -/
theorem Y_Z_anticommute : singleCommute PauliOp.Y PauliOp.Z = false := rfl

/-! ## Section 2: The Symplectic Inner Product -/

/-- The symplectic inner product of two Pauli operators, computed from supports.
    This measures the "non-commutativity" between P and Q.
    ω(P, Q) = |S_X(P) ∩ S_Z(Q)| + |S_Z(P) ∩ S_X(Q)| mod 2 -/
def symplecticInnerProduct {n : ℕ} (P Q : StabilizerCheck n) : ℕ :=
  ((P.supportX ∩ Q.supportZ).card + (P.supportZ ∩ Q.supportX).card) % 2

/-- Alternative: compute symplectic inner product directly from exponent functions.
    For P = ∏_v X_v^{a_v} Z_v^{b_v} and Q = ∏_v X_v^{c_v} Z_v^{d_v},
    ω(P, Q) = ∑_v (a_v * d_v + b_v * c_v) mod 2 -/
def symplecticInnerProductExponents {n : ℕ} (a b c d : Fin n → ZMod 2) : ZMod 2 :=
  ∑ v : Fin n, (a v * d v + b v * c v)

/-! ## Section 3: Connecting Anticommuting Overlap to Symplectic Form

The key insight is that two single-qubit Paulis anticommute exactly when:
- One has X-component and the other has Z-component (but not the same component)
- This corresponds to the symplectic inner product counting X-Z overlaps -/

/-- The contribution from site i to the symplectic form:
    counts how many of (P has X at i and Q has Z at i) and (P has Z at i and Q has X at i) hold -/
def siteSymplecticContrib (P Q : PauliString n) (i : Fin n) : ℕ :=
  (if (P i).hasX = true ∧ (Q i).hasZ = true then 1 else 0) +
  (if (P i).hasZ = true ∧ (Q i).hasX = true then 1 else 0)

/-- Key calculation: The anticommuting condition at a site is equivalent to
    the symplectic contribution being odd (1 mod 2). -/
theorem site_anticommute_iff_symplectic_odd (P Q : PauliString n) (i : Fin n) :
    (singleCommute (P i) (Q i) = false) ↔ siteSymplecticContrib P Q i % 2 = 1 := by
  unfold siteSymplecticContrib
  cases hP : P i <;> cases hQ : Q i <;> simp [singleCommute, PauliOp.hasX, PauliOp.hasZ]

/-- The anticommuting overlap equals the symplectic contribution sum mod 2 -/
theorem anticommutingOverlap_eq_symplectic_sum_mod2 {n : ℕ} (P Q : PauliString n) :
    anticommutingOverlap P Q % 2 =
    (∑ i : Fin n, siteSymplecticContrib P Q i) % 2 := by
  unfold anticommutingOverlap
  have h_eq : (Finset.filter (fun i => singleCommute (P i) (Q i) = false) Finset.univ).card % 2 =
              (∑ i : Fin n, siteSymplecticContrib P Q i) % 2 := by
    have key : ∀ i : Fin n, (if singleCommute (P i) (Q i) = false then (1 : ℕ) else 0) =
                           siteSymplecticContrib P Q i % 2 := by
      intro i
      have h := site_anticommute_iff_symplectic_odd P Q i
      by_cases hanti : singleCommute (P i) (Q i) = false
      · simp only [hanti, ↓reduceIte]
        exact (h.mp hanti).symm
      · simp only [hanti]
        have hne : siteSymplecticContrib P Q i % 2 ≠ 1 := fun hc => hanti (h.mpr hc)
        have hbound : siteSymplecticContrib P Q i % 2 < 2 := Nat.mod_lt _ (by omega)
        interval_cases siteSymplecticContrib P Q i % 2
        · rfl
        · exact absurd rfl hne
    have h_count : (Finset.filter (fun i => singleCommute (P i) (Q i) = false) Finset.univ).card =
                   ∑ i : Fin n, if singleCommute (P i) (Q i) = false then (1 : ℕ) else 0 := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    calc (Finset.filter (fun i => singleCommute (P i) (Q i) = false) Finset.univ).card % 2
        = (∑ i : Fin n, if singleCommute (P i) (Q i) = false then (1 : ℕ) else 0) % 2 := by
          rw [h_count]
      _ = (∑ i : Fin n, siteSymplecticContrib P Q i % 2) % 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact key i
      _ = (∑ i : Fin n, siteSymplecticContrib P Q i) % 2 := by
          rw [← Finset.sum_nat_mod]
  exact h_eq

/-- Helper: The sum of symplectic contributions equals the cross-support overlaps -/
theorem symplectic_sum_eq_support_overlap {n : ℕ} (P Q : PauliString n) :
    ∑ i : Fin n, siteSymplecticContrib P Q i =
    (supportX P ∩ supportZ Q).card + (supportZ P ∩ supportX Q).card := by
  simp only [siteSymplecticContrib]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- First sum = |supportX P ∩ supportZ Q|
    have h1 : ∑ i : Fin n, (if (P i).hasX = true ∧ (Q i).hasZ = true then (1 : ℕ) else 0) =
              (Finset.filter
                (fun i => (P i).hasX = true ∧ (Q i).hasZ = true) Finset.univ).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    have h2 : (Finset.filter (fun i => (P i).hasX = true ∧ (Q i).hasZ = true) Finset.univ) =
              (supportX P ∩ supportZ Q) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
                 supportX, supportZ, Finset.mem_filter]
    rw [h1, h2]
  · -- Second sum = |supportZ P ∩ supportX Q|
    have h1 : ∑ i : Fin n, (if (P i).hasZ = true ∧ (Q i).hasX = true then (1 : ℕ) else 0) =
              (Finset.filter
                (fun i => (P i).hasZ = true ∧ (Q i).hasX = true) Finset.univ).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    have h2 : (Finset.filter (fun i => (P i).hasZ = true ∧ (Q i).hasX = true) Finset.univ) =
              (supportZ P ∩ supportX Q) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
                 supportX, supportZ, Finset.mem_filter]
    rw [h1, h2]

/-! ## Section 4: Main Theorem -/

/-- **Main Theorem (Algebraic Form)**: Two Pauli strings commute if and only if their
    X-Z support overlaps sum to an even number.

    This is proven by:
    1. Pauli strings commute iff the count of anticommuting sites is even
    2. A site anticommutes iff its symplectic contribution is odd
    3. The sum of symplectic contributions equals the support overlap count

    This connects the operator-theoretic definition of commutation
    (based on single-qubit X-Z anticommutation) to the combinatorial formula. -/
theorem pauliStrings_commute_iff_overlap_even {n : ℕ} (P Q : PauliString n) :
    pauliStringsCommute P Q ↔
    ((supportX P ∩ supportZ Q).card + (supportZ P ∩ supportX Q).card) % 2 = 0 := by
  unfold pauliStringsCommute
  rw [anticommutingOverlap_eq_symplectic_sum_mod2, symplectic_sum_eq_support_overlap]

/-- **Main Theorem**: Two Pauli operators commute (in the sense of operator algebra)
    if and only if their symplectic inner product is zero.

    P and Q commute ⟺ |S_X(P) ∩ S_Z(Q)| + |S_Z(P) ∩ S_X(Q)| ≡ 0 (mod 2)

    This is derived from the fundamental fact that X and Z anticommute on a single qubit,
    and the overall commutation depends on the parity of such anticommutations. -/
theorem commutationConditionPauli {n : ℕ} (P Q : StabilizerCheck n) :
    StabilizerCheck.commutes P Q ↔ symplecticInnerProduct P Q = 0 := by
  unfold StabilizerCheck.commutes symplecticInnerProduct
  rfl

/-- The commutation condition expressed using support overlap directly -/
theorem commutationConditionPauli' {n : ℕ} (P Q : StabilizerCheck n) :
    StabilizerCheck.commutes P Q ↔
    ((P.supportX ∩ Q.supportZ).card + (P.supportZ ∩ Q.supportX).card) % 2 = 0 := by
  rfl

/-! ## Section 5: Properties of Symplectic Inner Product -/

/-- Symplectic inner product is symmetric -/
theorem symplecticInnerProduct_symm {n : ℕ} (P Q : StabilizerCheck n) :
    symplecticInnerProduct P Q = symplecticInnerProduct Q P := by
  unfold symplecticInnerProduct
  have h1 : (P.supportX ∩ Q.supportZ).card = (Q.supportZ ∩ P.supportX).card := by
    rw [Finset.inter_comm]
  have h2 : (P.supportZ ∩ Q.supportX).card = (Q.supportX ∩ P.supportZ).card := by
    rw [Finset.inter_comm]
  simp only [h1, h2, add_comm]

/-- Symplectic inner product with identity is zero -/
theorem symplecticInnerProduct_identity_left {n : ℕ} (P : StabilizerCheck n) :
    symplecticInnerProduct (StabilizerCheck.identity n) P = 0 := by
  unfold symplecticInnerProduct StabilizerCheck.identity
  simp only [Finset.empty_inter, Finset.card_empty, add_zero, Nat.zero_mod]

/-- Symplectic inner product with identity is zero (right) -/
theorem symplecticInnerProduct_identity_right {n : ℕ} (P : StabilizerCheck n) :
    symplecticInnerProduct P (StabilizerCheck.identity n) = 0 := by
  rw [symplecticInnerProduct_symm]
  exact symplecticInnerProduct_identity_left P

/-- Symplectic inner product of P with itself is zero -/
theorem symplecticInnerProduct_self {n : ℕ} (P : StabilizerCheck n) :
    symplecticInnerProduct P P = 0 := by
  unfold symplecticInnerProduct
  have h : (P.supportX ∩ P.supportZ).card + (P.supportZ ∩ P.supportX).card =
           2 * (P.supportX ∩ P.supportZ).card := by
    rw [Finset.inter_comm P.supportZ P.supportX]
    ring
  rw [h]
  exact Nat.mul_mod_right 2 _

/-- Every Pauli operator commutes with itself (derived from symplectic condition) -/
theorem pauli_self_commutes {n : ℕ} (P : StabilizerCheck n) :
    StabilizerCheck.commutes P P := by
  rw [commutationConditionPauli]
  exact symplecticInnerProduct_self P

/-- Identity commutes with everything (derived from symplectic condition) -/
theorem pauli_identity_commutes_all {n : ℕ} (P : StabilizerCheck n) :
    StabilizerCheck.commutes (StabilizerCheck.identity n) P := by
  rw [commutationConditionPauli]
  exact symplecticInnerProduct_identity_left P

/-! ## Section 6: Linearity of Symplectic Inner Product -/

/-- Helper: the symplectic inner product is additive in the first argument mod 2 -/
theorem symplecticInnerProduct_mul_left {n : ℕ} (A B D : StabilizerCheck n) :
    symplecticInnerProduct (StabilizerCheck.mul A B) D =
    (symplecticInnerProduct A D + symplecticInnerProduct B D) % 2 := by
  unfold symplecticInnerProduct StabilizerCheck.mul
  simp only
  have h1 := symmDiff_inter_card_mod2 A.supportX B.supportX D.supportZ
  have h2 := symmDiff_inter_card_mod2 A.supportZ B.supportZ D.supportX
  omega

/-- Commutativity: if A commutes with D and B commutes with D, then A*B commutes with D -/
theorem commutes_mul_left {n : ℕ} (A B D : StabilizerCheck n)
    (hA : StabilizerCheck.commutes A D) (hB : StabilizerCheck.commutes B D) :
    StabilizerCheck.commutes (StabilizerCheck.mul A B) D := by
  rw [commutationConditionPauli] at *
  rw [symplecticInnerProduct_mul_left, hA, hB]

/-! ## Section 7: Helper Lemmas for Using the Commutation Condition -/

/-- The commutation condition is symmetric -/
@[simp]
theorem commutes_symm {n : ℕ} (P Q : StabilizerCheck n) :
    StabilizerCheck.commutes P Q ↔ StabilizerCheck.commutes Q P :=
  StabilizerCheck.commutes_symm P Q

/-- Commutation with identity is always true -/
@[simp]
theorem commutes_identity_left {n : ℕ} (P : StabilizerCheck n) :
    StabilizerCheck.commutes (StabilizerCheck.identity n) P :=
  StabilizerCheck.identity_commutes_all P

@[simp]
theorem commutes_identity_right {n : ℕ} (P : StabilizerCheck n) :
    StabilizerCheck.commutes P (StabilizerCheck.identity n) := by
  rw [commutes_symm]
  exact commutes_identity_left P

/-- Self-commutation is always true -/
@[simp]
theorem commutes_self {n : ℕ} (P : StabilizerCheck n) :
    StabilizerCheck.commutes P P :=
  StabilizerCheck.self_commutes P

/-- Characterization: P and Q anticommute iff symplectic inner product is 1 -/
def anticommutes {n : ℕ} (P Q : StabilizerCheck n) : Prop :=
  symplecticInnerProduct P Q = 1

theorem anticommutes_iff {n : ℕ} (P Q : StabilizerCheck n) :
    anticommutes P Q ↔ ¬StabilizerCheck.commutes P Q := by
  unfold anticommutes
  rw [commutationConditionPauli]
  unfold symplecticInnerProduct
  constructor
  · intro h hn
    rw [hn] at h
    exact absurd h (by decide)
  · intro h
    have hmod : ((P.supportX ∩ Q.supportZ).card +
                 (P.supportZ ∩ Q.supportX).card) % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

/-- Anticommutation is symmetric -/
theorem anticommutes_symm {n : ℕ} (P Q : StabilizerCheck n) :
    anticommutes P Q ↔ anticommutes Q P := by
  unfold anticommutes
  rw [symplecticInnerProduct_symm]

/-! ## Section 8: Connection to PauliString Commutation -/

/-- Convert a PauliString to a StabilizerCheck with trivial phase -/
def pauliStringToCheck {n : ℕ} (P : PauliString n) : StabilizerCheck n where
  supportX := supportX P
  supportZ := supportZ P
  phase := Phase.one

/-- The supports are preserved by conversion -/
theorem pauliStringToCheck_supportX {n : ℕ} (P : PauliString n) :
    (pauliStringToCheck P).supportX = supportX P := rfl

theorem pauliStringToCheck_supportZ {n : ℕ} (P : PauliString n) :
    (pauliStringToCheck P).supportZ = supportZ P := rfl

/-- Commutation of PauliStrings via StabilizerCheck commutation -/
theorem pauliString_commutes_via_check {n : ℕ} (P Q : PauliString n) :
    StabilizerCheck.commutes (pauliStringToCheck P) (pauliStringToCheck Q) ↔
    ((supportX P ∩ supportZ Q).card + (supportZ P ∩ supportX Q).card) % 2 = 0 := by
  rfl

/-- The StabilizerCheck commutation matches the PauliString commutation -/
theorem pauliString_check_commutes_iff_pauliStringsCommute {n : ℕ} (P Q : PauliString n) :
    StabilizerCheck.commutes (pauliStringToCheck P) (pauliStringToCheck Q) ↔
    pauliStringsCommute P Q := by
  rw [pauliString_commutes_via_check, pauliStrings_commute_iff_overlap_even]

/-! ## Section 9: Additional Properties -/

/-- The symplectic inner product is at most 1 -/
theorem symplecticInnerProduct_le_one {n : ℕ} (P Q : StabilizerCheck n) :
    symplecticInnerProduct P Q ≤ 1 := by
  unfold symplecticInnerProduct
  have h := Nat.mod_lt ((P.supportX ∩ Q.supportZ).card +
                        (P.supportZ ∩ Q.supportX).card) (by omega : 0 < 2)
  omega

/-- If P has no X-support and no Z-support, it commutes with any Q -/
theorem commutes_of_empty_supports {n : ℕ} (P Q : StabilizerCheck n)
    (hX : P.supportX = ∅) (hZ : P.supportZ = ∅) :
    StabilizerCheck.commutes P Q := by
  unfold StabilizerCheck.commutes
  simp only [hX, hZ, Finset.empty_inter, Finset.card_empty, add_zero, Nat.zero_mod]

/-- X-only operator commutes with Z-only operator when overlaps are even -/
theorem commutes_X_only_Z_only {n : ℕ} (P Q : StabilizerCheck n)
    (hPZ : P.supportZ = ∅) (hQX : Q.supportX = ∅)
    (hOverlap : Even (P.supportX ∩ Q.supportZ).card) :
    StabilizerCheck.commutes P Q := by
  unfold StabilizerCheck.commutes
  simp only [hPZ, hQX, Finset.inter_empty, Finset.card_empty, Nat.add_zero]
  exact Nat.even_iff.mp hOverlap

/-- The overlap count measures the degree of non-commutativity -/
def overlapCount {n : ℕ} (P Q : StabilizerCheck n) : ℕ :=
  (P.supportX ∩ Q.supportZ).card + (P.supportZ ∩ Q.supportX).card

theorem commutes_iff_even_overlap {n : ℕ} (P Q : StabilizerCheck n) :
    StabilizerCheck.commutes P Q ↔ Even (overlapCount P Q) := by
  unfold StabilizerCheck.commutes overlapCount
  rw [Nat.even_iff]

/-- Bound on overlap count -/
theorem overlapCount_le {n : ℕ} (P Q : StabilizerCheck n) :
    overlapCount P Q ≤ P.supportX.card + P.supportZ.card := by
  unfold overlapCount
  have h1 : (P.supportX ∩ Q.supportZ).card ≤ P.supportX.card :=
    Finset.card_le_card (Finset.inter_subset_left)
  have h2 : (P.supportZ ∩ Q.supportX).card ≤ P.supportZ.card :=
    Finset.card_le_card (Finset.inter_subset_left)
  omega

end QEC
