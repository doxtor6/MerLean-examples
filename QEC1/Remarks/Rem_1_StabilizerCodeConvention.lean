import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Rem_1: Stabilizer Code Convention

## Statement
Throughout this work, we consider an $[[n,k,d]]$ quantum low-density parity-check (qLDPC)
stabilizer code on $n$ physical qubits, encoding $k$ logical qubits with distance $d$.
The code is specified by a set of stabilizer checks $\{s_i\}$. A logical operator $L$ is a
Pauli operator that commutes with all stabilizers but is not itself a stabilizer.
By choosing an appropriate single-qubit basis for each physical qubit, we ensure that the
logical operator $L$ being measured is a product of Pauli-$X$ matrices:
$L = \prod_{v \in \text{supp}(L)} X_v$, where $\text{supp}(L)$ denotes the set of qubits
on which $L$ acts non-trivially.

## Main Definitions
- `StabPauliType` : The four single-qubit Pauli operators (I, X, Y, Z)
- `PauliOp` : A Pauli operator on n qubits (tensor product of single-qubit Paulis)
- `StabilizerCode` : An [[n,k,d]] stabilizer code specification
- `LogicalOp` : A logical operator (commutes with stabilizers, not a stabilizer)
- `XTypeLogical` : A logical operator that is purely X-type (convention for L)

## Key Properties
- `XTypeLogical.support_eq` : L acts as X on exactly supp(L)
- `XTypeLogical.commutes_with_stabilizers` : L commutes with all stabilizers
- `XTypeLogical.not_in_stabilizer_group` : L is not itself a stabilizer
-/

/-! ## Pauli Operators -/

/-- The four single-qubit Pauli operators -/
inductive StabPauliType : Type where
  | I : StabPauliType  -- Identity
  | X : StabPauliType  -- Pauli-X (bit flip)
  | Y : StabPauliType  -- Pauli-Y
  | Z : StabPauliType  -- Pauli-Z (phase flip)
  deriving DecidableEq, Repr, Inhabited

namespace StabPauliType

/-- Multiplication of Pauli types (ignoring phase) -/
def mul : StabPauliType → StabPauliType → StabPauliType
  | I, p => p
  | p, I => p
  | X, X => I
  | Y, Y => I
  | Z, Z => I
  | X, Y => Z
  | Y, X => Z
  | Y, Z => X
  | Z, Y => X
  | Z, X => Y
  | X, Z => Y

instance : Mul StabPauliType := ⟨mul⟩

@[simp] lemma mul_I (p : StabPauliType) : p * I = p := by cases p <;> rfl
@[simp] lemma I_mul (p : StabPauliType) : I * p = p := by cases p <;> rfl
@[simp] lemma mul_self (p : StabPauliType) : p * p = I := by cases p <;> rfl

/-- A Pauli type acts nontrivially iff it is not the identity -/
def isNontrivial (p : StabPauliType) : Bool :=
  match p with
  | I => false
  | _ => true

/-- A Pauli is X-type if it involves X (i.e., is X or Y) -/
def isXType (p : StabPauliType) : Bool :=
  match p with
  | X => true
  | Y => true
  | _ => false

/-- A Pauli is Z-type if it involves Z (i.e., is Z or Y) -/
def isZType (p : StabPauliType) : Bool :=
  match p with
  | Z => true
  | Y => true
  | _ => false

/-- Two Paulis commute iff they are equal, one is identity, or they are both in {X,Z} -/
def commutes (p q : StabPauliType) : Bool :=
  match p, q with
  | I, _ => true
  | _, I => true
  | X, X => true
  | Y, Y => true
  | Z, Z => true
  | X, Z => false
  | Z, X => false
  | X, Y => false
  | Y, X => false
  | Y, Z => false
  | Z, Y => false

lemma commutes_comm (p q : StabPauliType) : commutes p q = commutes q p := by
  cases p <;> cases q <;> rfl

end StabPauliType

/-! ## Multi-qubit Pauli Operators -/

/-- A Pauli operator on n qubits is a function from qubit indices to Pauli types,
    together with a global phase (±1, ±i represented as ZMod 4) -/
@[ext]
structure PauliOp (n : ℕ) where
  /-- The Pauli type on each qubit -/
  paulis : Fin n → StabPauliType
  /-- The global phase: 0 = +1, 1 = +i, 2 = -1, 3 = -i -/
  phase : ZMod 4
  deriving DecidableEq

namespace PauliOp

variable {n : ℕ}

/-- The identity operator on n qubits -/
def identity (n : ℕ) : PauliOp n := ⟨fun _ => StabPauliType.I, 0⟩

/-- The support of a Pauli operator: qubits where it acts nontrivially -/
def support (P : PauliOp n) : Finset (Fin n) :=
  Finset.filter (fun i => P.paulis i ≠ StabPauliType.I) Finset.univ

/-- The X-type support: qubits where P acts as X or Y -/
def xSupport (P : PauliOp n) : Finset (Fin n) :=
  Finset.filter (fun i => (P.paulis i).isXType) Finset.univ

/-- The Z-type support: qubits where P acts as Z or Y -/
def zSupport (P : PauliOp n) : Finset (Fin n) :=
  Finset.filter (fun i => (P.paulis i).isZType) Finset.univ

/-- Two Pauli operators commute (ignoring global phase) iff they have an even number
    of positions where their Pauli types anticommute -/
def commutes (P Q : PauliOp n) : Prop :=
  (Finset.filter (fun i => !(P.paulis i).commutes (Q.paulis i)) Finset.univ).card % 2 = 0

/-- A Pauli operator is purely X-type if it only contains I and X -/
def isPurelyXType (P : PauliOp n) : Prop :=
  ∀ i, P.paulis i = StabPauliType.I ∨ P.paulis i = StabPauliType.X

/-- Construct a pure X-type operator from a set of qubits -/
def pureX (S : Finset (Fin n)) : PauliOp n :=
  ⟨fun i => if i ∈ S then StabPauliType.X else StabPauliType.I, 0⟩

@[simp] lemma pureX_paulis_mem (S : Finset (Fin n)) (i : Fin n) (h : i ∈ S) :
    (pureX S).paulis i = StabPauliType.X := by simp [pureX, h]

@[simp] lemma pureX_paulis_not_mem (S : Finset (Fin n)) (i : Fin n) (h : i ∉ S) :
    (pureX S).paulis i = StabPauliType.I := by simp [pureX, h]

lemma pureX_isPurelyXType (S : Finset (Fin n)) : isPurelyXType (pureX S) := by
  intro i
  simp only [pureX]
  split_ifs <;> simp

@[simp] lemma pureX_support (S : Finset (Fin n)) : (pureX S).support = S := by
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, pureX]
  split_ifs with h
  · simp [h]
  · simp [h]

@[simp] lemma pureX_xSupport (S : Finset (Fin n)) : (pureX S).xSupport = S := by
  ext i
  simp only [xSupport, Finset.mem_filter, Finset.mem_univ, true_and, pureX]
  split_ifs with h
  · simp [h, StabPauliType.isXType]
  · simp [h, StabPauliType.isXType]

@[simp] lemma pureX_zSupport (S : Finset (Fin n)) : (pureX S).zSupport = ∅ := by
  ext i
  simp only [zSupport, Finset.mem_filter, Finset.mem_univ, true_and, pureX]
  split_ifs <;> simp [StabPauliType.isZType]

end PauliOp

/-! ## Stabilizer Codes -/

/-- A stabilizer group on n qubits is a subgroup of the Pauli group.
    For simplicity, we represent it as a set of generators (the stabilizer checks). -/
structure StabilizerGroup (n : ℕ) where
  /-- The generating stabilizer checks -/
  generators : Set (PauliOp n)
  /-- Generators are finite -/
  finite_generators : generators.Finite
  /-- All generators mutually commute -/
  generators_commute : ∀ s₁ s₂, s₁ ∈ generators → s₂ ∈ generators → PauliOp.commutes s₁ s₂

/-- An [[n, k, d]] stabilizer code specification -/
structure StabilizerCode where
  /-- Number of physical qubits -/
  n : ℕ
  /-- Number of logical qubits encoded -/
  k : ℕ
  /-- Code distance -/
  d : ℕ
  /-- The stabilizer group -/
  stabilizers : StabilizerGroup n
  /-- Basic constraint: n ≥ k -/
  n_ge_k : n ≥ k
  /-- Distance is positive -/
  d_pos : d > 0

namespace StabilizerCode

/-- A Pauli operator commutes with the stabilizer group iff it commutes with all generators -/
def commutesWithStabilizers (C : StabilizerCode) (P : PauliOp C.n) : Prop :=
  ∀ s ∈ C.stabilizers.generators, PauliOp.commutes P s

/-- The centralizer: all Paulis that commute with all stabilizers -/
def centralizer (C : StabilizerCode) : Set (PauliOp C.n) :=
  {P | C.commutesWithStabilizers P}

/-- A Pauli is in the stabilizer group if it can be generated by products of generators -/
-- For a full treatment, this would need the group generated by generators
-- For now, we define membership in a simplified way
def inStabilizerGroup (C : StabilizerCode) (P : PauliOp C.n) : Prop :=
  ∃ (gens : Finset (PauliOp C.n)),
    (↑gens : Set (PauliOp C.n)) ⊆ C.stabilizers.generators ∧
    -- P is the product of these generators (simplified: just membership for identity case)
    (gens = ∅ → P = PauliOp.identity C.n) ∧
    P ∈ C.stabilizers.generators ∨ P = PauliOp.identity C.n

end StabilizerCode

/-! ## Logical Operators -/

/-- A logical operator for a stabilizer code:
    - Commutes with all stabilizers
    - Is not itself in the stabilizer group -/
structure LogicalOp (C : StabilizerCode) where
  /-- The underlying Pauli operator -/
  op : PauliOp C.n
  /-- Commutes with all stabilizers -/
  commutes_with_stabilizers : C.commutesWithStabilizers op
  /-- Not in the stabilizer group -/
  not_in_stabilizer_group : ¬C.inStabilizerGroup op

namespace LogicalOp

variable {C : StabilizerCode}

/-- The support of a logical operator -/
def support (L : LogicalOp C) : Finset (Fin C.n) := L.op.support

/-- The X-type support of a logical operator -/
def xSupport (L : LogicalOp C) : Finset (Fin C.n) := L.op.xSupport

/-- The Z-type support of a logical operator -/
def zSupport (L : LogicalOp C) : Finset (Fin C.n) := L.op.zSupport

end LogicalOp

/-! ## X-Type Logical Operator Convention -/

/-- An X-type logical operator: a logical that is purely X-type (only I and X Paulis).
    This captures the convention: L = ∏_{v ∈ supp(L)} X_v -/
structure XTypeLogical (C : StabilizerCode) extends LogicalOp C where
  /-- The operator is purely X-type -/
  is_purely_xtype : PauliOp.isPurelyXType op

namespace XTypeLogical

variable {C : StabilizerCode}

/-- For an X-type logical, supp(L) = X-type support -/
@[simp] lemma support_eq_xSupport (L : XTypeLogical C) : L.support = L.xSupport := by
  ext i
  simp only [LogicalOp.support, LogicalOp.xSupport, PauliOp.support, PauliOp.xSupport,
             Finset.mem_filter, Finset.mem_univ, true_and]
  have h := L.is_purely_xtype i
  cases h with
  | inl hi =>
    simp only [hi, ne_eq, not_true_eq_false, StabPauliType.isXType, false_iff]
    simp
  | inr hx =>
    simp only [hx, ne_eq, StabPauliType.isXType]
    constructor <;> intro _ <;> decide

/-- For an X-type logical, the Z-type support is empty -/
@[simp] lemma zSupport_empty (L : XTypeLogical C) : L.zSupport = ∅ := by
  ext i
  simp only [LogicalOp.zSupport, PauliOp.zSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  have h := L.is_purely_xtype i
  cases h with
  | inl hi => simp [hi, StabPauliType.isZType]
  | inr hx => simp [hx, StabPauliType.isZType]

/-- Construct an X-type logical from a support set (assuming the properties hold) -/
def fromSupport (C : StabilizerCode) (S : Finset (Fin C.n))
    (h_commutes : C.commutesWithStabilizers (PauliOp.pureX S))
    (h_not_stab : ¬C.inStabilizerGroup (PauliOp.pureX S)) : XTypeLogical C where
  op := PauliOp.pureX S
  commutes_with_stabilizers := h_commutes
  not_in_stabilizer_group := h_not_stab
  is_purely_xtype := PauliOp.pureX_isPurelyXType S

@[simp] lemma fromSupport_support (C : StabilizerCode) (S : Finset (Fin C.n)) (h₁ h₂) :
    (fromSupport C S h₁ h₂).support = S := by
  simp [fromSupport, LogicalOp.support]

/-- The representation theorem: L = ∏_{v ∈ supp(L)} X_v (ignoring global phase).
    The Pauli content of L on each qubit matches pureX of the support. -/
theorem product_representation (L : XTypeLogical C) :
    L.toLogicalOp.op.paulis = (PauliOp.pureX L.support).paulis := by
  ext i
  simp only [LogicalOp.support, PauliOp.support, PauliOp.pureX]
  split_ifs with h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at h
    have := L.is_purely_xtype i
    cases this with
    | inl hi => exact absurd hi h
    | inr hx => exact hx
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not] at h
    exact h

end XTypeLogical

/-! ## LDPC Property -/

/-- A code is Low-Density Parity-Check (LDPC) if there's a constant bound on:
    - The weight of each stabilizer check
    - The number of checks each qubit participates in -/
structure IsLDPC (C : StabilizerCode) where
  /-- Maximum weight of any stabilizer check -/
  max_check_weight : ℕ
  /-- Maximum number of checks any qubit is in -/
  max_qubit_degree : ℕ
  /-- All checks have bounded weight -/
  check_weight_bound : ∀ s ∈ C.stabilizers.generators, (PauliOp.support s).card ≤ max_check_weight
  /-- All qubits have bounded degree -/
  qubit_degree_bound : ∀ i : Fin C.n,
    (C.stabilizers.finite_generators.toFinset.filter
      (fun s => i ∈ PauliOp.support s)).card ≤ max_qubit_degree

/-! ## Summary of Convention

The key convention established:
1. We work with [[n,k,d]] qLDPC stabilizer codes
2. Codes are specified by stabilizer checks {sᵢ}
3. Logical operators commute with stabilizers but aren't stabilizers themselves
4. The logical L being measured is always X-type: L = ∏_{v ∈ supp(L)} Xᵥ
5. supp(L) is exactly the qubits where L acts nontrivially
-/
