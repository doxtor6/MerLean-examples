import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Notation: Pauli Operators

## Statement
For qubits labeled by vertices v of a graph or indices i, we denote by X_v (or X_i)
the Pauli-X operator acting on qubit v (or i), and similarly Z_v (or Z_i) for Pauli-Z.
A product of Pauli operators is written as ∏_{v ∈ S} X_v for a set S of qubit labels.
The identity operator is denoted 𝟙. For a Pauli operator P, we denote by S_X(P) the
X-type support (sites where P acts via X or Y) and S_Z(P) the Z-type support (sites
where P acts via Y or Z).

## Main Results
- `PauliOp`: multi-qubit Pauli operator as a pair of binary vectors (x, z) ∈ (ZMod 2)^V × (ZMod 2)^V
- `PauliOp.pauliX`, `PauliOp.pauliZ`: single-site Pauli-X and Pauli-Z operators
- `PauliOp.prodX`, `PauliOp.prodZ`: products of Pauli operators over a finset
- `PauliOp.supportX`, `PauliOp.supportZ`: X-type and Z-type supports
- `PauliOp.mul`: multiplication of Pauli operators (pointwise XOR of binary vectors)

## Corollaries
- Support characterization lemmas
- Product support lemmas
- Identity and single-site support computations
-/

variable {V : Type*}

/-! ## Definition of Pauli operators -/

/-- Pauli operators on qubits labeled by type V, represented as pairs of binary vectors
    (xVec, zVec) ∈ (ZMod 2)^V × (ZMod 2)^V.
    The pair (x, z) represents the Pauli operator ⊗_v X_v^{x_v} Z_v^{z_v}.
    - (0, 0) at site v means identity I
    - (1, 0) at site v means X
    - (0, 1) at site v means Z
    - (1, 1) at site v means Y (up to phase) -/
@[ext]
structure PauliOp (V : Type*) where
  xVec : V → ZMod 2
  zVec : V → ZMod 2

namespace PauliOp

/-! ## Identity operator -/

/-- The identity Pauli operator (acts as identity on all qubits). -/
def id (V : Type*) : PauliOp V := ⟨0, 0⟩

/-! ## Single-site Pauli operators -/

/-- Pauli-X operator acting on qubit v. -/
def pauliX [DecidableEq V] (v : V) : PauliOp V :=
  ⟨Pi.single v 1, 0⟩

/-- Pauli-Z operator acting on qubit v. -/
def pauliZ [DecidableEq V] (v : V) : PauliOp V :=
  ⟨0, Pi.single v 1⟩

/-- Pauli-Y operator acting on qubit v (= X_v Z_v up to phase). -/
def pauliY [DecidableEq V] (v : V) : PauliOp V :=
  ⟨Pi.single v 1, Pi.single v 1⟩

/-! ## Multiplication (pointwise XOR of binary vectors) -/

/-- Product of two Pauli operators (pointwise addition of binary vectors in ZMod 2).
    This captures the Pauli group multiplication up to phase. -/
def mul (P Q : PauliOp V) : PauliOp V :=
  ⟨P.xVec + Q.xVec, P.zVec + Q.zVec⟩

instance : Mul (PauliOp V) := ⟨mul⟩

instance : One (PauliOp V) := ⟨⟨0, 0⟩⟩

@[simp]
theorem one_xVec : (1 : PauliOp V).xVec = 0 := rfl

@[simp]
theorem one_zVec : (1 : PauliOp V).zVec = 0 := rfl

@[simp]
theorem mul_xVec (P Q : PauliOp V) : (P * Q).xVec = P.xVec + Q.xVec := rfl

@[simp]
theorem mul_zVec (P Q : PauliOp V) : (P * Q).zVec = P.zVec + Q.zVec := rfl

theorem mul_comm (P Q : PauliOp V) : P * Q = Q * P := by
  ext v <;> simp [add_comm]

theorem mul_assoc (P Q R : PauliOp V) : P * Q * R = P * (Q * R) := by
  ext v <;> simp [add_assoc]

theorem one_mul (P : PauliOp V) : 1 * P = P := by
  ext v <;> simp

theorem mul_one (P : PauliOp V) : P * 1 = P := by
  ext v <;> simp

theorem mul_self (P : PauliOp V) : P * P = 1 := by
  ext v <;> simp [CharTwo.add_self_eq_zero]

instance : CommGroup (PauliOp V) where
  mul := (· * ·)
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  inv := fun P => P
  inv_mul_cancel := mul_self
  mul_comm := mul_comm

@[simp]
theorem inv_eq_self (P : PauliOp V) : P⁻¹ = P := rfl

/-! ## Products of Pauli operators over finite sets -/

/-- Product of Pauli-X operators over a finset S of qubit labels:
    ∏_{v ∈ S} X_v -/
def prodX [DecidableEq V] (S : Finset V) : PauliOp V :=
  ⟨fun v => if v ∈ S then 1 else 0, 0⟩

/-- Product of Pauli-Z operators over a finset S of qubit labels:
    ∏_{v ∈ S} Z_v -/
def prodZ [DecidableEq V] (S : Finset V) : PauliOp V :=
  ⟨0, fun v => if v ∈ S then 1 else 0⟩

@[simp]
theorem prodX_empty [DecidableEq V] : prodX (∅ : Finset V) = 1 := by
  ext v <;> simp [prodX]

@[simp]
theorem prodZ_empty [DecidableEq V] : prodZ (∅ : Finset V) = 1 := by
  ext v <;> simp [prodZ]

/-! ## X-type and Z-type support -/

/-- X-type support: the set of sites where P acts via X or Y
    (i.e., where xVec is nonzero). -/
def supportX [DecidableEq V] [Fintype V] (P : PauliOp V) : Finset V :=
  Finset.filter (fun v => P.xVec v ≠ 0) Finset.univ

/-- Z-type support: the set of sites where P acts via Y or Z
    (i.e., where zVec is nonzero). -/
def supportZ [DecidableEq V] [Fintype V] (P : PauliOp V) : Finset V :=
  Finset.filter (fun v => P.zVec v ≠ 0) Finset.univ

/-- Full support: sites where P acts non-trivially (via X, Y, or Z). -/
def support [DecidableEq V] [Fintype V] (P : PauliOp V) : Finset V :=
  Finset.filter (fun v => P.xVec v ≠ 0 ∨ P.zVec v ≠ 0) Finset.univ

/-- Weight of a Pauli operator: number of qubits on which it acts non-trivially. -/
def weight [DecidableEq V] [Fintype V] (P : PauliOp V) : ℕ :=
  P.support.card

/-! ## Support membership characterizations -/

@[simp]
theorem mem_supportX [DecidableEq V] [Fintype V] (P : PauliOp V) (v : V) :
    v ∈ P.supportX ↔ P.xVec v ≠ 0 := by
  simp [supportX]

@[simp]
theorem mem_supportZ [DecidableEq V] [Fintype V] (P : PauliOp V) (v : V) :
    v ∈ P.supportZ ↔ P.zVec v ≠ 0 := by
  simp [supportZ]

@[simp]
theorem mem_support [DecidableEq V] [Fintype V] (P : PauliOp V) (v : V) :
    v ∈ P.support ↔ P.xVec v ≠ 0 ∨ P.zVec v ≠ 0 := by
  simp [support]

/-! ## In ZMod 2, nonzero means equal to 1 -/

private theorem zmod2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  fin_cases a <;> simp

@[simp]
theorem mem_supportX_iff [DecidableEq V] [Fintype V] (P : PauliOp V) (v : V) :
    v ∈ P.supportX ↔ P.xVec v = 1 := by
  rw [mem_supportX, zmod2_ne_zero_iff]

@[simp]
theorem mem_supportZ_iff [DecidableEq V] [Fintype V] (P : PauliOp V) (v : V) :
    v ∈ P.supportZ ↔ P.zVec v = 1 := by
  rw [mem_supportZ, zmod2_ne_zero_iff]

/-! ## Identity support -/

@[simp]
theorem supportX_one [DecidableEq V] [Fintype V] :
    (1 : PauliOp V).supportX = ∅ := by
  ext v; simp

@[simp]
theorem supportZ_one [DecidableEq V] [Fintype V] :
    (1 : PauliOp V).supportZ = ∅ := by
  ext v; simp

@[simp]
theorem support_one [DecidableEq V] [Fintype V] :
    (1 : PauliOp V).support = ∅ := by
  ext v; simp

@[simp]
theorem weight_one [DecidableEq V] [Fintype V] :
    (1 : PauliOp V).weight = 0 := by
  simp [weight]

/-! ## Single-site operator supports -/

@[simp]
theorem supportX_pauliX [DecidableEq V] [Fintype V] (v : V) :
    (pauliX v : PauliOp V).supportX = {v} := by
  ext w; simp [pauliX, Pi.single_apply]

@[simp]
theorem supportZ_pauliX [DecidableEq V] [Fintype V] (v : V) :
    (pauliX v : PauliOp V).supportZ = ∅ := by
  ext w; simp [pauliX]

@[simp]
theorem supportX_pauliZ [DecidableEq V] [Fintype V] (v : V) :
    (pauliZ v : PauliOp V).supportX = ∅ := by
  ext w; simp [pauliZ]

@[simp]
theorem supportZ_pauliZ [DecidableEq V] [Fintype V] (v : V) :
    (pauliZ v : PauliOp V).supportZ = {v} := by
  ext w; simp [pauliZ, Pi.single_apply]

@[simp]
theorem supportX_pauliY [DecidableEq V] [Fintype V] (v : V) :
    (pauliY v : PauliOp V).supportX = {v} := by
  ext w; simp [pauliY, Pi.single_apply]

@[simp]
theorem supportZ_pauliY [DecidableEq V] [Fintype V] (v : V) :
    (pauliY v : PauliOp V).supportZ = {v} := by
  ext w; simp [pauliY, Pi.single_apply]

/-! ## Product support characterizations -/

theorem supportX_prodX [DecidableEq V] [Fintype V] (S : Finset V) :
    (prodX S).supportX = S := by
  ext v; simp [prodX]

theorem supportZ_prodX [DecidableEq V] [Fintype V] (S : Finset V) :
    (prodX S).supportZ = ∅ := by
  ext v; simp [prodX]

theorem supportX_prodZ [DecidableEq V] [Fintype V] (S : Finset V) :
    (prodZ S).supportX = ∅ := by
  ext v; simp [prodZ]

theorem supportZ_prodZ [DecidableEq V] [Fintype V] (S : Finset V) :
    (prodZ S).supportZ = S := by
  ext v; simp [prodZ]

/-! ## Support union bound -/

theorem support_eq_supportX_union_supportZ [DecidableEq V] [Fintype V] (P : PauliOp V) :
    P.support = P.supportX ∪ P.supportZ := by
  ext v; simp [support, supportX, supportZ]

/-! ## Pauli-X single-site and product relationship -/

theorem pauliX_eq_prodX_singleton [DecidableEq V] (v : V) :
    pauliX v = prodX ({v} : Finset V) := by
  ext w <;> simp [pauliX, prodX, Pi.single_apply]

theorem pauliZ_eq_prodZ_singleton [DecidableEq V] (v : V) :
    pauliZ v = prodZ ({v} : Finset V) := by
  ext w <;> simp [pauliZ, prodZ, Pi.single_apply]

end PauliOp
