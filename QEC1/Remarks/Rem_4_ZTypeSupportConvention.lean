import QEC1.Remarks.Rem_1_StabilizerCodeConvention
import Mathlib.Data.Finset.Card

/-!
# Rem_4: Z-Type Support Convention

## Statement
For a Pauli operator $P$, the **$Z$-type support** of $P$, denoted $\mathcal{S}_Z$, is the set of qubits
on which $P$ acts via $Y$ or $Z$ operators. Similarly, the **$X$-type support**, denoted $\mathcal{S}_X$,
is the set of qubits on which $P$ acts via $X$ or $Y$ operators. A Pauli operator $P$ can be written as
$P = i^{\sigma} \prod_{v \in \mathcal{S}_X} X_v \prod_{v \in \mathcal{S}_Z} Z_v$ for some phase
$\sigma \in \{0,1,2,3\}$. If $P$ commutes with an $X$-type logical operator $L = \prod_v X_v$, then
$|\mathcal{S}_Z| \equiv 0 \pmod{2}$ (the $Z$-type support has even cardinality).

## Main Definitions
The X-type and Z-type support definitions are in Rem_1_StabilizerCodeConvention.
This file focuses on the decomposition and commutation properties.

## Main Results
- `PauliOp.xzDecomposition` : P = i^σ ∏_{v ∈ S_X} X_v ∏_{v ∈ S_Z} Z_v
- `PauliOp.commutes_with_pureX_iff_zSupport_even` : P commutes with L = ∏_v X_v iff |S_Z ∩ supp(L)| is even
- `PauliOp.commutes_with_XTypeLogical_imp_zSupport_even` : If P commutes with X-type logical L,
  then |S_Z| restricted to supp(L) is even

## Corollaries
- The Z-type support has even cardinality when P commutes with an X-type logical over its full support
-/

/-! ## Recap of X-type and Z-type Support

The definitions are already in Rem_1:
- `PauliOp.xSupport P` : qubits where P acts as X or Y (X-type)
- `PauliOp.zSupport P` : qubits where P acts as Z or Y (Z-type)
- `StabPauliType.isXType p` : true if p is X or Y
- `StabPauliType.isZType p` : true if p is Z or Y
-/

namespace StabPauliType

/-- X and Y contribute to X-type support -/
@[simp] lemma X_isXType : isXType X = true := rfl
@[simp] lemma Y_isXType : isXType Y = true := rfl
@[simp] lemma Z_isXType : isXType Z = false := rfl
@[simp] lemma I_isXType : isXType I = false := rfl

/-- Z and Y contribute to Z-type support -/
@[simp] lemma X_isZType : isZType X = false := rfl
@[simp] lemma Y_isZType : isZType Y = true := rfl
@[simp] lemma Z_isZType : isZType Z = true := rfl
@[simp] lemma I_isZType : isZType I = false := rfl

/-- Y is both X-type and Z-type -/
lemma Y_isXType_and_isZType : isXType Y = true ∧ isZType Y = true := ⟨rfl, rfl⟩

/-- A Pauli is nontrivial iff it is X-type or Z-type (or both, i.e., Y) -/
lemma isNontrivial_iff_isXType_or_isZType (p : StabPauliType) :
    isNontrivial p = true ↔ isXType p = true ∨ isZType p = true := by
  cases p <;> simp [isNontrivial, isXType, isZType]

/-- The anticommutation rule: X and Z anticommute -/
lemma X_anticommutes_Z : commutes X Z = false := rfl
lemma Z_anticommutes_X : commutes Z X = false := rfl

/-- X and Y anticommute -/
lemma X_anticommutes_Y : commutes X Y = false := rfl
lemma Y_anticommutes_X : commutes Y X = false := rfl

/-- Z and Y anticommute -/
lemma Z_anticommutes_Y : commutes Z Y = false := rfl
lemma Y_anticommutes_Z : commutes Y Z = false := rfl

/-- Two Paulis anticommute iff one is purely X-type (X) and the other is purely Z-type (Z),
    or one involves both (Y) and the other involves just one component -/
lemma anticommutes_iff (p q : StabPauliType) :
    commutes p q = false ↔ (p = X ∧ q = Z) ∨ (p = Z ∧ q = X) ∨
                          (p = X ∧ q = Y) ∨ (p = Y ∧ q = X) ∨
                          (p = Z ∧ q = Y) ∨ (p = Y ∧ q = Z) := by
  cases p <;> cases q <;> simp [commutes]

/-- For pure X (not Y), anticommutes with Z-type but not X-type -/
lemma X_commutes_iff (q : StabPauliType) : commutes X q = true ↔ isZType q = false := by
  cases q <;> simp [commutes, isZType]

/-- For pure Z (not Y), anticommutes with X-type but not Z-type -/
lemma Z_commutes_iff (q : StabPauliType) : commutes Z q = true ↔ isXType q = false := by
  cases q <;> simp [commutes, isXType]

end StabPauliType

/-! ## Commutation of Multi-Qubit Pauli Operators -/

namespace PauliOp

variable {n : ℕ}

/-- The overlap between Z-type support of P and support of Q -/
def zSupportOverlap (P Q : PauliOp n) : Finset (Fin n) :=
  P.zSupport ∩ Q.support

/-- The anticommuting positions between P and a pure X operator on support S -/
def anticommutingPositionsWithPureX (P : PauliOp n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => (P.paulis i).isZType)

/-- Alternative characterization: positions where P is Z-type and S has X -/
lemma anticommutingPositionsWithPureX_eq (P : PauliOp n) (S : Finset (Fin n)) :
    P.anticommutingPositionsWithPureX S = P.zSupport ∩ S := by
  ext i
  simp only [anticommutingPositionsWithPureX, zSupport, Finset.mem_filter, Finset.mem_inter,
             Finset.mem_univ, true_and]
  tauto

/-- Helper: I commutes with everything -/
private lemma I_commutes_all (p : StabPauliType) : StabPauliType.commutes p StabPauliType.I = true := by
  cases p <;> rfl

/-- P commutes with pureX S iff the number of Z-type positions in S is even -/
theorem commutes_with_pureX_iff (P : PauliOp n) (S : Finset (Fin n)) :
    commutes P (pureX S) ↔ (P.zSupport ∩ S).card % 2 = 0 := by
  unfold commutes
  -- The anticommuting positions are exactly where P is Z-type and S has X
  have heq : Finset.filter (fun i => !(P.paulis i).commutes ((pureX S).paulis i)) Finset.univ
           = P.zSupport ∩ S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, zSupport, Finset.mem_inter, pureX]
    constructor
    · intro h
      split_ifs at h with hm
      · -- i ∈ S, so pureX S i = X, and P.paulis i doesn't commute with X
        constructor
        · -- P.paulis i is Z-type
          cases hp : P.paulis i <;> simp [hp, StabPauliType.commutes] at h ⊢
        · exact hm
      · -- i ∉ S, so pureX S i = I, which commutes with everything
        rw [I_commutes_all, Bool.not_true] at h
        cases h
    · intro ⟨hZ, hS⟩
      simp only [hS, ↓reduceIte]
      cases hp : P.paulis i
      · simp [hp, StabPauliType.isZType] at hZ
      · simp [hp, StabPauliType.isZType] at hZ
      · simp only [hp, StabPauliType.commutes, StabPauliType.Y_anticommutes_X, Bool.not_false]
      · simp only [hp, StabPauliType.commutes, StabPauliType.Z_anticommutes_X, Bool.not_false]
  rw [heq]

/-- If P commutes with pureX S, then |P.zSupport ∩ S| is even -/
theorem zSupport_inter_even_of_commutes_pureX (P : PauliOp n) (S : Finset (Fin n))
    (h : commutes P (pureX S)) : (P.zSupport ∩ S).card % 2 = 0 :=
  (commutes_with_pureX_iff P S).mp h

/-- Converse: if |P.zSupport ∩ S| is even, then P commutes with pureX S -/
theorem commutes_pureX_of_zSupport_inter_even (P : PauliOp n) (S : Finset (Fin n))
    (h : (P.zSupport ∩ S).card % 2 = 0) : commutes P (pureX S) :=
  (commutes_with_pureX_iff P S).mpr h

/-- Even cardinality characterization -/
def hasEvenCardinality (S : Finset (Fin n)) : Prop := S.card % 2 = 0

@[simp] lemma hasEvenCardinality_iff (S : Finset (Fin n)) :
    hasEvenCardinality S ↔ S.card % 2 = 0 := Iff.rfl

/-- Empty set has even cardinality -/
@[simp] lemma hasEvenCardinality_empty : hasEvenCardinality (∅ : Finset (Fin n)) := by
  simp [hasEvenCardinality]

end PauliOp

/-! ## The Main Theorem: Commutation with X-type Logical -/

namespace PauliOp

variable {C : StabilizerCode}

/-- Main theorem: If P commutes with an X-type logical operator L = ∏_{v ∈ supp(L)} X_v,
    then the Z-type support of P restricted to supp(L) has even cardinality.

    This is because:
    - L acts as X on each qubit in its support
    - P and L anticommute at position i iff P is Z-type at i and i ∈ supp(L)
    - For P and L to commute overall, the number of anticommuting positions must be even
    - Hence |S_Z(P) ∩ supp(L)| ≡ 0 (mod 2) -/
theorem commutes_with_XTypeLogical_imp_zSupport_even
    (P : PauliOp C.n) (L : XTypeLogical C)
    (h : commutes P L.toLogicalOp.op) :
    (P.zSupport ∩ L.support).card % 2 = 0 := by
  -- L.op has the same paulis as pureX L.support (by product_representation)
  have heq : L.toLogicalOp.op.paulis = (pureX L.support).paulis := L.product_representation
  -- The commutation check only depends on paulis, not phase
  have hcomm : commutes P L.toLogicalOp.op ↔ commutes P (pureX L.support) := by
    unfold commutes
    simp only [heq]
  rw [hcomm] at h
  exact zSupport_inter_even_of_commutes_pureX P L.support h

/-- When L has full support (acts on all n qubits), the condition becomes:
    P commutes with L implies |S_Z(P)| is even -/
theorem commutes_with_full_XLogical_imp_zSupport_card_even
    (P : PauliOp C.n) (L : XTypeLogical C)
    (hfull : L.support = Finset.univ)
    (h : commutes P L.toLogicalOp.op) :
    P.zSupport.card % 2 = 0 := by
  have := commutes_with_XTypeLogical_imp_zSupport_even P L h
  simp only [hfull, Finset.inter_univ] at this
  exact this

end PauliOp

/-! ## The X-Z Decomposition -/

namespace PauliOp

variable {n : ℕ}

/-- Every Pauli type can be written as X^a Z^b for a, b ∈ {0,1} (ignoring phase).
    I = X^0 Z^0, X = X^1 Z^0, Z = X^0 Z^1, Y = X^1 Z^1 (up to phase i) -/
def xzExponents (p : StabPauliType) : Fin 2 × Fin 2 :=
  match p with
  | StabPauliType.I => (0, 0)
  | StabPauliType.X => (1, 0)
  | StabPauliType.Y => (1, 1)
  | StabPauliType.Z => (0, 1)

@[simp] lemma xzExponents_I : xzExponents StabPauliType.I = (0, 0) := rfl
@[simp] lemma xzExponents_X : xzExponents StabPauliType.X = (1, 0) := rfl
@[simp] lemma xzExponents_Y : xzExponents StabPauliType.Y = (1, 1) := rfl
@[simp] lemma xzExponents_Z : xzExponents StabPauliType.Z = (0, 1) := rfl

/-- The X exponent is 1 iff the Pauli is X-type -/
lemma xzExponents_fst_eq_one_iff_isXType (p : StabPauliType) :
    (xzExponents p).1 = 1 ↔ p.isXType = true := by
  cases p <;> simp [xzExponents, StabPauliType.isXType]

/-- The Z exponent is 1 iff the Pauli is Z-type -/
lemma xzExponents_snd_eq_one_iff_isZType (p : StabPauliType) :
    (xzExponents p).2 = 1 ↔ p.isZType = true := by
  cases p <;> simp [xzExponents, StabPauliType.isZType]

/-- The X-Z decomposition of a Pauli operator:
    P = i^σ ∏_{v ∈ S_X} X_v ∏_{v ∈ S_Z} Z_v

    This structure captures that any Pauli operator factors into X-part and Z-part. -/
structure XZDecomposition (P : PauliOp n) where
  /-- The X-type support is exactly the qubits where P has X component -/
  xSupport_correct : P.xSupport = Finset.filter (fun i => (xzExponents (P.paulis i)).1 = 1) Finset.univ
  /-- The Z-type support is exactly the qubits where P has Z component -/
  zSupport_correct : P.zSupport = Finset.filter (fun i => (xzExponents (P.paulis i)).2 = 1) Finset.univ

/-- Every Pauli operator has an X-Z decomposition -/
theorem xzDecomposition (P : PauliOp n) : XZDecomposition P where
  xSupport_correct := by
    ext i
    simp only [xSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (xzExponents_fst_eq_one_iff_isXType (P.paulis i)).symm
  zSupport_correct := by
    ext i
    simp only [zSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (xzExponents_snd_eq_one_iff_isZType (P.paulis i)).symm

/-- X-type support equals {v : P.paulis v ∈ {X, Y}} -/
@[simp] lemma xSupport_eq_filter (P : PauliOp n) :
    P.xSupport = Finset.filter (fun i => P.paulis i = StabPauliType.X ∨ P.paulis i = StabPauliType.Y) Finset.univ := by
  ext i
  simp only [xSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hp : P.paulis i <;> simp [hp, StabPauliType.isXType]

/-- Z-type support equals {v : P.paulis v ∈ {Z, Y}} -/
@[simp] lemma zSupport_eq_filter (P : PauliOp n) :
    P.zSupport = Finset.filter (fun i => P.paulis i = StabPauliType.Z ∨ P.paulis i = StabPauliType.Y) Finset.univ := by
  ext i
  simp only [zSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hp : P.paulis i <;> simp [hp, StabPauliType.isZType]

end PauliOp

/-! ## Corollaries -/

namespace PauliOp

variable {n : ℕ}

/-- The Z-type support of a pure X operator is empty -/
@[simp] lemma pureX_zSupport_empty (S : Finset (Fin n)) : (pureX S).zSupport = ∅ := by
  ext i
  simp only [zSupport, Finset.mem_filter, Finset.mem_univ, true_and, pureX]
  split_ifs <;> simp [StabPauliType.isZType]

/-- A pure X operator always commutes with itself -/
@[simp] lemma pureX_commutes_self (S : Finset (Fin n)) : commutes (pureX S) (pureX S) := by
  rw [commutes_with_pureX_iff]
  simp only [pureX_zSupport_empty, Finset.empty_inter, Finset.card_empty, Nat.zero_mod]

/-- Two pure X operators always commute -/
theorem pureX_commutes_pureX (S T : Finset (Fin n)) : commutes (pureX S) (pureX T) := by
  rw [commutes_with_pureX_iff]
  simp only [pureX_zSupport_empty, Finset.empty_inter, Finset.card_empty, Nat.zero_mod]

/-- The intersection of X-type support and Z-type support gives qubits with Y -/
lemma xSupport_inter_zSupport (P : PauliOp n) :
    P.xSupport ∩ P.zSupport = Finset.filter (fun i => P.paulis i = StabPauliType.Y) Finset.univ := by
  ext i
  simp only [Finset.mem_inter, xSupport, zSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hp : P.paulis i <;> simp [hp, StabPauliType.isXType, StabPauliType.isZType]

/-- The support of P is the union of pure X positions and pure Z positions and Y positions -/
lemma support_eq_xSupport_union_zSupport (P : PauliOp n) :
    P.support = P.xSupport ∪ P.zSupport := by
  ext i
  simp only [support, xSupport, zSupport, Finset.mem_filter, Finset.mem_univ, true_and,
             Finset.mem_union]
  cases hp : P.paulis i <;> simp [hp, StabPauliType.isXType, StabPauliType.isZType]

end PauliOp

/-! ## Summary

The Z-type support convention establishes:

1. **X-type Support S_X**: Qubits where P acts as X or Y (has X component)
2. **Z-type Support S_Z**: Qubits where P acts as Z or Y (has Z component)
3. **Decomposition**: P = i^σ ∏_{v ∈ S_X} X_v ∏_{v ∈ S_Z} Z_v for some phase σ ∈ {0,1,2,3}

4. **Key Commutation Property**:
   If P commutes with an X-type logical operator L = ∏_{v ∈ supp(L)} X_v, then
   |S_Z ∩ supp(L)| ≡ 0 (mod 2)

   This is because:
   - P anticommutes with X at position i iff P is Z-type at i
   - P and L anticommute iff the number of such positions in supp(L) is odd
   - For commutation, this number must be even

This property is fundamental to the gauging construction: it ensures that
deformed operators (which must commute with the logical L) have edge-paths
with even boundary, making them well-defined.
-/
