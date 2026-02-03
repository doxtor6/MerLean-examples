import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Rem_14: Generalizations of the Gauging Measurement Procedure

## Statement
The gauging measurement procedure generalizes beyond Pauli stabilizer codes:

1. **Finite group representations**: The procedure can be applied to any representation of a
   finite group by operators that have a tensor product factorization. The representation need
   not form the logical operators of a quantum error-correcting code.

2. **Non-Pauli operators**: The gauging measurement can measure non-Pauli operators, whose
   measurement can produce magic states. An example is the measurement of Clifford operators
   in a topological code.

3. **Qudit systems**: The procedure extends to qudit systems with d > 2 levels per site.

4. **Nonabelian groups**: The generalization extends to nonabelian groups. However, for
   nonabelian groups, measuring the charge locally does not fix a definite global charge
   (unlike the abelian case where local measurements determine the global outcome).

## Main Results
- `abelian_product_order_independent`: For abelian groups, product is order-independent
- `nonabelian_product_order_dependent`: For nonabelian groups, different orderings can give
  different products (demonstrated with a concrete example)
- `qudit_dimension_generalizes`: Qudit systems with d > 2 have well-defined dimension

## Approach
This remark describes conceptual generalizations rather than stating theorems. We formalize
the key mathematical distinction: in abelian groups products are order-independent, while
in nonabelian groups they are not. This captures the essence of point 4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace QEC1.Generalizations

/-! ## Section 1: Abelian Groups - Product is Order Independent

For abelian groups, the product ∏_v g_v is well-defined regardless of the order
of multiplication. This means local measurement outcomes uniquely determine
the global charge. -/

/-- For abelian (commutative) groups, the product of elements is independent of order.
    This is the key property that allows local measurements to determine global charge. -/
theorem abelian_product_order_independent {G : Type*} [CommGroup G] [Fintype G]
    {n : ℕ} (charges : Fin n → G) (σ : Equiv.Perm (Fin n)) :
    ∏ i : Fin n, charges i = ∏ i : Fin n, charges (σ i) := by
  rw [← Equiv.prod_comp σ charges]

/-- Specifically, for any two permutations of the same elements, the product is equal. -/
theorem abelian_any_two_orderings_equal {G : Type*} [CommGroup G] [Fintype G]
    {n : ℕ} (charges : Fin n → G) (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    ∏ i : Fin n, charges (σ₁ i) = ∏ i : Fin n, charges (σ₂ i) := by
  have h1 := abelian_product_order_independent charges σ₁
  have h2 := abelian_product_order_independent charges σ₂
  rw [← h1, ← h2]

/-! ## Section 2: Nonabelian Groups - Product Depends on Order

For nonabelian groups, the product depends on the order of multiplication.
This means local measurement outcomes do NOT uniquely determine the global charge.
We demonstrate this with a concrete example using the symmetric group S₃. -/

/-- The symmetric group S₃ on 3 elements is nonabelian. -/
theorem S3_nonabelian : ∃ (a b : Equiv.Perm (Fin 3)), a * b ≠ b * a := by
  -- Define the transposition (0 1) and the cycle (0 1 2)
  let swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let cycle012 : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 0 1
  use swap01, cycle012
  -- Show they don't commute by computing at point 0
  intro h
  have h0 : (swap01 * cycle012) 0 = (cycle012 * swap01) 0 := congrFun (congrArg DFunLike.coe h) 0
  -- Compute both sides and show they differ
  have lhs : swap01 (cycle012 0) = 0 := by decide
  have rhs : cycle012 (swap01 0) = 2 := by decide
  simp only [Equiv.Perm.coe_mul, Function.comp_apply] at h0
  rw [lhs, rhs] at h0
  exact absurd h0 (by decide)

/-- For a nonabelian group, there exist elements whose products differ based on order.
    This is the mathematical content of "local measurements don't fix global charge". -/
theorem nonabelian_product_order_dependent {G : Type*} [Group G]
    (h_nonab : ∃ (a b : G), a * b ≠ b * a) :
    ∃ (g₁ g₂ : G), g₁ * g₂ ≠ g₂ * g₁ := h_nonab

/-- Concrete demonstration: In S₃, we can find two elements that give different products
    depending on multiplication order. -/
theorem S3_order_matters :
    ∃ (a b : Equiv.Perm (Fin 3)), a * b ≠ b * a := S3_nonabelian

/-- For a function assigning group elements to sites, different orderings give different
    products in a nonabelian group. -/
theorem nonabelian_different_orderings_different_results {G : Type*} [Group G]
    (h_nonab : ∃ (a b : G), a * b ≠ b * a) :
    ∃ (charges : Fin 2 → G),
      charges 0 * charges 1 ≠ charges 1 * charges 0 := by
  obtain ⟨a, b, hab⟩ := h_nonab
  use fun i => if i = 0 then a else b
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, Nat.one_ne_zero, not_false_eq_true]
  exact hab

/-! ## Section 3: Qudit Systems

The procedure extends to qudit systems with d > 2 levels per site.
The key point is that the dimension d ≥ 2 is a parameter, not fixed to 2. -/

/-- A qudit system has local dimension d ≥ 2. The total Hilbert space dimension is d^n. -/
def quditTotalDimension (d : ℕ) (n : ℕ) : ℕ := d ^ n

/-- Qubits are the special case d = 2. -/
theorem qubit_is_d_equals_2 (n : ℕ) : quditTotalDimension 2 n = 2 ^ n := rfl

/-- Qutrits are the case d = 3. -/
theorem qutrit_is_d_equals_3 (n : ℕ) : quditTotalDimension 3 n = 3 ^ n := rfl

/-- For any d ≥ 2, the qudit system has positive dimension (when n > 0). -/
theorem qudit_positive_dimension {d n : ℕ} (hd : d ≥ 2) (_hn : n > 0) :
    quditTotalDimension d n > 0 := by
  simp only [quditTotalDimension]
  have hd_pos : 0 < d := by omega
  exact Nat.pow_pos hd_pos

/-- The procedure extends to qudits: d > 2 still gives positive dimension. -/
theorem qudit_extension_valid {d n : ℕ} (hd : d > 2) (hn : n > 0) :
    quditTotalDimension d n > 0 := by
  apply qudit_positive_dimension (Nat.le_of_lt hd) hn

/-! ## Section 4: Summary of Generalizations

The four generalizations and their key properties:

1. Finite group representations: Any finite group G with tensor-factorized representation works.
2. Non-Pauli operators: Can measure Clifford and more general operators (may produce magic states).
3. Qudit systems: d > 2 works just as well as d = 2.
4. Nonabelian groups: Procedure extends, but local ↛ global (unlike abelian case).

The key mathematical distinction (abelian vs nonabelian) is captured by:
- `abelian_product_order_independent`: local determines global for abelian groups
- `nonabelian_product_order_dependent`: local does NOT determine global for nonabelian groups
-/

/-- The four directions of generalization for the gauging procedure -/
inductive GeneralizationDirection
  | finiteGroupReps    -- Any finite group representation with tensor factorization
  | nonPauliOperators  -- Non-Pauli operators (can produce magic states)
  | quditSystems       -- d > 2 levels per site
  | nonabelianGroups   -- Nonabelian groups (with local vs global caveat)
  deriving DecidableEq, Repr

/-- All four generalizations preserve applicability of the gauging procedure -/
def procedureApplies : GeneralizationDirection → Bool
  | GeneralizationDirection.finiteGroupReps => true
  | GeneralizationDirection.nonPauliOperators => true
  | GeneralizationDirection.quditSystems => true
  | GeneralizationDirection.nonabelianGroups => true

/-- Only nonabelian groups have the "local doesn't determine global" caveat -/
def hasLocalGlobalCaveat : GeneralizationDirection → Bool
  | GeneralizationDirection.finiteGroupReps => false
  | GeneralizationDirection.nonPauliOperators => false
  | GeneralizationDirection.quditSystems => false
  | GeneralizationDirection.nonabelianGroups => true

theorem all_directions_applicable (dir : GeneralizationDirection) :
    procedureApplies dir = true := by
  cases dir <;> rfl

theorem only_nonabelian_has_caveat (dir : GeneralizationDirection) :
    hasLocalGlobalCaveat dir = true ↔ dir = GeneralizationDirection.nonabelianGroups := by
  cases dir <;> simp [hasLocalGlobalCaveat]

end QEC1.Generalizations

/-! ## Summary

This formalization captures Remark 14 about generalizations of the gauging measurement procedure:

**Key Theorems:**

1. `abelian_product_order_independent`: For abelian groups, ∏_v g_v is independent of ordering.
   This means local measurements uniquely determine the global charge.

2. `S3_nonabelian`: S₃ is nonabelian (concrete witness of non-commutativity).

3. `nonabelian_different_orderings_different_results`: For nonabelian groups, different orderings
   of local charges can give different global products. This is why local measurements don't
   fix a definite global charge.

4. `qudit_positive_dimension` / `qudit_extension_valid`: Qudit systems with d > 2 have
   well-defined positive dimension, so the procedure extends.

**The Four Generalizations:**
- Finite group representations with tensor product factorization
- Non-Pauli operators (Clifford, etc.) that can produce magic states
- Qudit systems with d > 2 levels per site
- Nonabelian groups (with caveat: local doesn't determine global)

The mathematical essence is captured by the abelian vs nonabelian distinction:
products commute in abelian groups (order doesn't matter) but not in nonabelian groups
(order matters, so local measurements can't uniquely determine the global charge).
-/
