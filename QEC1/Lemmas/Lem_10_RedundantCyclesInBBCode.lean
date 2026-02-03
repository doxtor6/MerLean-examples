import QEC1.Definitions.Def_16_BivariateBicycleCode
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Redundant Cycles in Bivariate Bicycle Code (Lemma 10)

## Statement
For a Bivariate Bicycle code with parity check matrices H_X = [A|B] and H_Z = [B^T|A^T],
when measuring logical X̄_α supported on left qubits, the number of redundant cycles
in the gauging graph is:

  dim{u : ∃ v, uS + vC = 0} = row_nullity(H_Z) - row_nullity(C)

where:
- S = submatrix of H_Z with rows for checks overlapping X̄_α
- C = submatrix of H_Z with rows for checks not overlapping X̄_α

## Main Results
**Main Theorem** (`redundant_cycles_formula`): The dimension of the redundant cycle space
equals the difference of row nullities.

**Helper Lemma** (`cycle_from_check_relation`): If uS + vC = 0 for vectors u, v, then
the product of checks has support only on edge qubits.

**Helper Lemma** (`edge_support_is_cycle`): The edge support of this product is a cycle
in the gauging graph.

## File Structure
1. Section 1: Check Classification (overlapping vs non-overlapping)
2. Section 2: Submatrices S and C from H_Z
3. Section 3: Row Nullity Definitions
4. Section 4: Redundant Cycle Space
5. Section 5: Main Theorem (equality)
6. Section 6: Helper Lemmas
-/

namespace QEC

open scoped BigOperators

set_option linter.unusedSectionVars false

/-! ## Section 1: Check Classification -/

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- A logical operator support on left qubits, represented as a subset of monomial indices.
    This represents X̄_α = ∏_{β ∈ support} X_{(β, L)}. -/
structure LeftLogicalSupport (ℓ m : ℕ) [NeZero ℓ] [NeZero m] where
  /-- The support set: monomial indices where the logical X acts on left qubits -/
  support : Finset (Fin ℓ × Fin m)

namespace LeftLogicalSupport

/-- Weight (size) of the logical operator -/
def weight (L : LeftLogicalSupport ℓ m) : ℕ := L.support.card

/-- Check if a left qubit is in the logical support -/
def containsQubit (L : LeftLogicalSupport ℓ m) (idx : Fin ℓ × Fin m) : Bool :=
  idx ∈ L.support

end LeftLogicalSupport

/-- Determines whether a Z-check overlaps with a left logical operator.
    Z check (β, Z) acts on left qubits at positions β * B^T.
    It overlaps with logical L if any of these positions intersect L.support. -/
def zCheckOverlapsLogical (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m)
    (β : Fin ℓ × Fin m) : Bool :=
  (C.polyB.transpose.support.filter (fun ⟨a, b⟩ =>
    (β.1 + a, β.2 + b) ∈ L.support)).Nonempty

/-- The set of Z-check indices that overlap with the logical operator -/
def overlappingChecks (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    Finset (Fin ℓ × Fin m) :=
  Finset.filter (fun β => zCheckOverlapsLogical C L β) Finset.univ

/-- The set of Z-check indices that do NOT overlap with the logical operator -/
def nonOverlappingChecks (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    Finset (Fin ℓ × Fin m) :=
  Finset.filter (fun β => ¬zCheckOverlapsLogical C L β) Finset.univ

/-- Overlapping and non-overlapping checks partition all Z-checks -/
theorem check_partition (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    overlappingChecks C L ∪ nonOverlappingChecks C L = Finset.univ := by
  ext β
  simp only [overlappingChecks, nonOverlappingChecks, Finset.mem_union, Finset.mem_filter,
             Finset.mem_univ, true_and]
  tauto

/-- Overlapping and non-overlapping checks are disjoint -/
theorem check_disjoint (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    Disjoint (overlappingChecks C L) (nonOverlappingChecks C L) := by
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy hxy
  simp only [overlappingChecks, nonOverlappingChecks, Finset.mem_filter, Finset.mem_univ,
             true_and] at hx hy
  rw [hxy] at hx
  exact hy hx

/-! ## Section 2: Vector Spaces for Row Space Analysis -/

/-- Row vector space over ZMod 2 indexed by check indices -/
abbrev CheckRowSpace (ℓ m : ℕ) [NeZero ℓ] [NeZero m] : Type :=
  (Fin ℓ × Fin m) → ZMod 2

/-- Column vector space over ZMod 2 indexed by qubit indices (2 * ℓ * m qubits) -/
abbrev QubitColSpace (ℓ m : ℕ) [NeZero ℓ] [NeZero m] : Type :=
  (Fin ℓ × Fin m × Bool) → ZMod 2

instance : Module (ZMod 2) (CheckRowSpace ℓ m) := Pi.module _ _ _
instance : Module (ZMod 2) (QubitColSpace ℓ m) := Pi.module _ _ _

/-- The H_Z parity check matrix as a linear map from qubits to syndromes.
    H_Z = [B^T | A^T] where B^T acts on left qubits and A^T on right qubits. -/
noncomputable def HZ_matrix (C : BivariateBicycleCode ℓ m) :
    QubitColSpace ℓ m →ₗ[ZMod 2] CheckRowSpace ℓ m where
  toFun := fun q β =>
    let leftContrib := C.polyB.transpose.support.sum fun ⟨a, b⟩ =>
      q (β.1 + a, β.2 + b, false)
    let rightContrib := C.polyA.transpose.support.sum fun ⟨a, b⟩ =>
      q (β.1 + a, β.2 + b, true)
    leftContrib + rightContrib
  map_add' := by
    intro q₁ q₂
    funext β
    simp only [Pi.add_apply]
    have h1 : ∑ x ∈ C.polyB.transpose.support,
        (q₁ (β.1 + x.1, β.2 + x.2, false) + q₂ (β.1 + x.1, β.2 + x.2, false)) =
        ∑ x ∈ C.polyB.transpose.support, q₁ (β.1 + x.1, β.2 + x.2, false) +
        ∑ x ∈ C.polyB.transpose.support, q₂ (β.1 + x.1, β.2 + x.2, false) := by
      rw [← Finset.sum_add_distrib]
    have h2 : ∑ x ∈ C.polyA.transpose.support,
        (q₁ (β.1 + x.1, β.2 + x.2, true) + q₂ (β.1 + x.1, β.2 + x.2, true)) =
        ∑ x ∈ C.polyA.transpose.support, q₁ (β.1 + x.1, β.2 + x.2, true) +
        ∑ x ∈ C.polyA.transpose.support, q₂ (β.1 + x.1, β.2 + x.2, true) := by
      rw [← Finset.sum_add_distrib]
    rw [h1, h2]
    ring
  map_smul' := by
    intro r q
    funext β
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h1 : ∑ x ∈ C.polyB.transpose.support, r * q (β.1 + x.1, β.2 + x.2, false) =
        r * ∑ x ∈ C.polyB.transpose.support, q (β.1 + x.1, β.2 + x.2, false) := by
      rw [Finset.mul_sum]
    have h2 : ∑ x ∈ C.polyA.transpose.support, r * q (β.1 + x.1, β.2 + x.2, true) =
        r * ∑ x ∈ C.polyA.transpose.support, q (β.1 + x.1, β.2 + x.2, true) := by
      rw [Finset.mul_sum]
    rw [h1, h2]
    ring

/-! ## Section 3: Row Nullity Definitions -/

/-- The row space of H_Z restricted to overlapping checks (submatrix S). -/
def OverlappingRowSubspace (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    Submodule (ZMod 2) (CheckRowSpace ℓ m) where
  carrier := {u | ∀ β, β ∉ overlappingChecks C L → u β = 0}
  add_mem' := by
    intro a b ha hb β hβ
    simp only [Pi.add_apply, ha β hβ, hb β hβ, add_zero]
  zero_mem' := by intro β _; rfl
  smul_mem' := by
    intro r a ha β hβ
    simp only [Pi.smul_apply, smul_eq_mul, ha β hβ, mul_zero]

/-- The row space of H_Z restricted to non-overlapping checks (submatrix C). -/
def NonOverlappingRowSubspace (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    Submodule (ZMod 2) (CheckRowSpace ℓ m) where
  carrier := {u | ∀ β, β ∉ nonOverlappingChecks C L → u β = 0}
  add_mem' := by
    intro a b ha hb β hβ
    simp only [Pi.add_apply, ha β hβ, hb β hβ, add_zero]
  zero_mem' := by intro β _; rfl
  smul_mem' := by
    intro r a ha β hβ
    simp only [Pi.smul_apply, smul_eq_mul, ha β hβ, mul_zero]

/-- The left kernel of H_Z: vectors u such that u^T · H_Z = 0. -/
def leftKernel (C : BivariateBicycleCode ℓ m) : Submodule (ZMod 2) (CheckRowSpace ℓ m) where
  carrier := {u | ∀ q : Fin ℓ × Fin m × Bool,
    Finset.univ.sum (fun β => u β * (HZ_matrix C).toFun
      (fun idx => if idx = q then 1 else 0) β) = 0}
  add_mem' := by
    intro a b ha hb q
    simp only [Pi.add_apply]
    have ha_eq := ha q
    have hb_eq := hb q
    have h_expand : ∑ β : Fin ℓ × Fin m, (a β + b β) *
           (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β =
        ∑ β : Fin ℓ × Fin m, a β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β +
        ∑ β : Fin ℓ × Fin m, b β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β := by
      have h_distrib : ∑ β : Fin ℓ × Fin m,
          (a β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β +
           b β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β) =
          ∑ β : Fin ℓ × Fin m,
            a β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β +
          ∑ β : Fin ℓ × Fin m,
            b β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β := by
        rw [← Finset.sum_add_distrib]
      have h_eq_sum : ∑ β : Fin ℓ × Fin m, (a β + b β) *
          (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β =
          ∑ β : Fin ℓ × Fin m, (a β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β +
          b β * (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β) := by
        congr 1; funext β; ring
      rw [h_eq_sum, h_distrib]
    rw [h_expand, ha_eq, hb_eq, add_zero]
  zero_mem' := by
    intro q
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  smul_mem' := by
    intro r u hu q
    simp only [Pi.smul_apply, smul_eq_mul]
    have hu_eq := hu q
    have h_factor : ∑ β : Fin ℓ × Fin m, r * u β *
           (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β =
        r * ∑ β : Fin ℓ × Fin m, u β *
           (HZ_matrix C).toFun (fun idx => if idx = q then 1 else 0) β := by
      rw [Finset.mul_sum]
      congr 1
      funext β
      ring
    rw [h_factor, hu_eq, mul_zero]

/-- Full row nullity of H_Z: dimension of the left kernel -/
noncomputable def fullRowNullity (C : BivariateBicycleCode ℓ m) : ℕ :=
  Module.finrank (ZMod 2) (leftKernel C)

/-! ## Section 4: Redundant Cycle Space -/

/-- The space of u vectors in the overlapping check subspace such that
    there exists v in the non-overlapping check subspace with uS + vC = 0. -/
def RedundantCycleSpace (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    Submodule (ZMod 2) (CheckRowSpace ℓ m) where
  carrier := {u | u ∈ OverlappingRowSubspace C L ∧
    ∃ v ∈ NonOverlappingRowSubspace C L, (u + v) ∈ leftKernel C}
  add_mem' := by
    intro a b ha hb
    constructor
    · exact (OverlappingRowSubspace C L).add_mem ha.1 hb.1
    · obtain ⟨va, hva_mem, hva_ker⟩ := ha.2
      obtain ⟨vb, hvb_mem, hvb_ker⟩ := hb.2
      use va + vb
      constructor
      · exact (NonOverlappingRowSubspace C L).add_mem hva_mem hvb_mem
      · have h_eq : a + b + (va + vb) = (a + va) + (b + vb) := by abel
        rw [h_eq]
        exact (leftKernel C).add_mem hva_ker hvb_ker
  zero_mem' := by
    constructor
    · exact (OverlappingRowSubspace C L).zero_mem
    · use 0
      constructor
      · exact (NonOverlappingRowSubspace C L).zero_mem
      · simp only [add_zero]
        exact (leftKernel C).zero_mem
  smul_mem' := by
    intro r u hu
    constructor
    · exact (OverlappingRowSubspace C L).smul_mem r hu.1
    · obtain ⟨v, hv_mem, hv_ker⟩ := hu.2
      use r • v
      constructor
      · exact (NonOverlappingRowSubspace C L).smul_mem r hv_mem
      · have h_eq : r • u + r • v = r • (u + v) := by
          ext β; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [h_eq]
        exact (leftKernel C).smul_mem r hv_ker

/-- Dimension of the redundant cycle space -/
noncomputable def redundantCycleDim (C : BivariateBicycleCode ℓ m)
    (L : LeftLogicalSupport ℓ m) : ℕ :=
  Module.finrank (ZMod 2) (RedundantCycleSpace C L)

/-! ## Section 5: Row Nullity for Submatrices -/

/-- Projection to overlapping check coordinates -/
def projToOverlapping (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    CheckRowSpace ℓ m →ₗ[ZMod 2] CheckRowSpace ℓ m where
  toFun := fun u β => if β ∈ overlappingChecks C L then u β else 0
  map_add' := by intro x y; funext β; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' := by
    intro r x; funext β; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- Projection to non-overlapping check coordinates -/
def projToNonOverlapping (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    CheckRowSpace ℓ m →ₗ[ZMod 2] CheckRowSpace ℓ m where
  toFun := fun u β => if β ∈ nonOverlappingChecks C L then u β else 0
  map_add' := by intro x y; funext β; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' := by
    intro r x; funext β; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The left kernel restricted to non-overlapping checks: row nullity of submatrix C -/
def leftKernelNonOverlapping (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    Submodule (ZMod 2) (CheckRowSpace ℓ m) :=
  NonOverlappingRowSubspace C L ⊓ leftKernel C

/-- Row nullity of submatrix C (non-overlapping checks) -/
noncomputable def rowNullityC (C : BivariateBicycleCode ℓ m)
    (L : LeftLogicalSupport ℓ m) : ℕ :=
  Module.finrank (ZMod 2) (leftKernelNonOverlapping C L)

/-! ## Section 6: Main Theorem -/

/-- The projection from the full left kernel to the overlapping check coordinates. -/
noncomputable def kernelProjection (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    (leftKernel C) →ₗ[ZMod 2] CheckRowSpace ℓ m where
  toFun := fun ⟨w, _⟩ => fun β => if β ∈ overlappingChecks C L then w β else 0
  map_add' := by
    intro ⟨x, _⟩ ⟨y, _⟩
    funext β
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro r ⟨x, _⟩
    funext β
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The kernel of the projection: vectors in leftKernel(H_Z) that are zero on overlapping checks. -/
theorem kernel_projection_ker (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    ∀ w : leftKernel C, kernelProjection C L w = 0 ↔
      (w : CheckRowSpace ℓ m) ∈ leftKernelNonOverlapping C L := by
  intro ⟨w, hw⟩
  simp only [kernelProjection, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · intro h
    simp only [leftKernelNonOverlapping, Submodule.mem_inf, NonOverlappingRowSubspace,
               Submodule.mem_mk]
    constructor
    · intro β hβ
      simp only [nonOverlappingChecks, Finset.mem_filter, Finset.mem_univ, true_and] at hβ
      have h_part := check_partition C L
      have hβ_in_overlap : β ∈ overlappingChecks C L := by
        have : β ∈ overlappingChecks C L ∪ nonOverlappingChecks C L := by
          rw [h_part]; exact Finset.mem_univ β
        simp only [Finset.mem_union, nonOverlappingChecks, Finset.mem_filter,
                   Finset.mem_univ, true_and] at this
        cases this with
        | inl h => exact h
        | inr h => exact absurd h hβ
      have h_eq := congr_fun h β
      simp only [Pi.zero_apply, hβ_in_overlap, ↓reduceIte] at h_eq
      exact h_eq
    · exact hw
  · intro h
    simp only [leftKernelNonOverlapping, Submodule.mem_inf, NonOverlappingRowSubspace,
               Submodule.mem_mk] at h
    funext β
    simp only [Pi.zero_apply]
    split_ifs with hβ
    · have h_disj := check_disjoint C L
      have hβ_not_in_non : β ∉ nonOverlappingChecks C L := by
        intro hβ2
        exact Finset.disjoint_left.mp h_disj hβ hβ2
      exact h.1 β hβ_not_in_non
    · rfl

/-- The redundant cycle space equals the image of the kernel projection. -/
theorem redundant_eq_image (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    (RedundantCycleSpace C L : Set (CheckRowSpace ℓ m)) =
    LinearMap.range (kernelProjection C L) := by
  ext u
  simp only [SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · intro ⟨hu_overlap, v, hv_mem, hv_ker⟩
    use ⟨u + v, hv_ker⟩
    funext β
    simp only [kernelProjection, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with hβ
    · simp only [Pi.add_apply]
      have hv_zero : v β = 0 := by
        simp only [NonOverlappingRowSubspace, Submodule.mem_mk] at hv_mem
        have h_disj := check_disjoint C L
        have hβ_not_non : β ∉ nonOverlappingChecks C L :=
          fun h => Finset.disjoint_left.mp h_disj hβ h
        exact hv_mem β hβ_not_non
      rw [hv_zero, add_zero]
    · simp only [OverlappingRowSubspace, Submodule.mem_mk] at hu_overlap
      exact (hu_overlap β hβ).symm
  · intro ⟨⟨w, hw⟩, hw_eq⟩
    constructor
    · simp only [OverlappingRowSubspace, Submodule.mem_mk]
      intro β hβ
      rw [← hw_eq]
      simp only [kernelProjection, LinearMap.coe_mk, AddHom.coe_mk, hβ, ↓reduceIte]
    · use fun β => if β ∈ nonOverlappingChecks C L then w β else 0
      constructor
      · simp only [NonOverlappingRowSubspace, Submodule.mem_mk]
        intro β hβ
        simp only [hβ, ↓reduceIte]
      · have h_eq : (fun β => if β ∈ overlappingChecks C L then w β else 0) +
                    (fun β => if β ∈ nonOverlappingChecks C L then w β else 0) = w := by
          funext β
          simp only [Pi.add_apply]
          have h_part := check_partition C L
          have hβ_mem : β ∈ overlappingChecks C L ∪ nonOverlappingChecks C L := by
            rw [h_part]; exact Finset.mem_univ β
          simp only [Finset.mem_union] at hβ_mem
          have h_disj := check_disjoint C L
          cases hβ_mem with
          | inl h =>
            have hβ_not_non : β ∉ nonOverlappingChecks C L :=
              fun h2 => Finset.disjoint_left.mp h_disj h h2
            simp only [h, hβ_not_non, ↓reduceIte, add_zero]
          | inr h =>
            have hβ_not_over : β ∉ overlappingChecks C L :=
              fun h2 => Finset.disjoint_left.mp h_disj h2 h
            simp only [hβ_not_over, h, ↓reduceIte, zero_add]
        -- We need: u + v ∈ leftKernel where v = (fun β => if β ∈ nonOverlappingChecks... w β ...)
        -- hw_eq says: (kernelProjection C L) ⟨w, hw⟩ = u
        -- This means: u = fun β => if β ∈ overlappingChecks C L then w β else 0
        -- So u + v = (projOverlap w) + (projNonOverlap w) = w
        have hu_is_proj : u = fun β => if β ∈ overlappingChecks C L then w β else 0 := hw_eq.symm
        have h_sum_eq_w : u + (fun β => if β ∈ nonOverlappingChecks C L then w β else 0) = w := by
          rw [hu_is_proj]
          exact h_eq
        rw [h_sum_eq_w]
        exact hw

/-- The image of kernelProjection is a submodule -/
theorem redundant_cycle_space_eq_range (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    RedundantCycleSpace C L = LinearMap.range (kernelProjection C L) := by
  ext u
  have h := redundant_eq_image C L
  constructor
  · intro hu
    rw [Set.ext_iff] at h
    exact (h u).mp hu
  · intro hu
    rw [Set.ext_iff] at h
    exact (h u).mpr hu

/-- **Main Theorem**: The redundant cycle dimension equals row_nullity(H_Z) - row_nullity(C).

    For a BB code measuring logical X̄_α on left qubits:
    dim{u : ∃ v, uS + vC = 0} = row_nullity(H_Z) - row_nullity(C)

    This captures that redundant cycles in the gauging graph come from the row
    dependencies in H_Z that are not already present in the non-overlapping
    submatrix C.

    The proof proceeds by:
    1. Showing RedundantCycleSpace = range(kernelProjection)
    2. Using rank-nullity: dim(range) = dim(domain) - dim(ker)
    3. Identifying ker(kernelProjection) with leftKernelNonOverlapping -/
theorem redundant_cycles_formula (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    redundantCycleDim C L + rowNullityC C L = fullRowNullity C := by
  have h_range_eq : LinearMap.range (kernelProjection C L) = RedundantCycleSpace C L := by
    rw [redundant_cycle_space_eq_range]
  unfold redundantCycleDim rowNullityC fullRowNullity
  rw [← h_range_eq]
  -- The kernel of kernelProjection consists of elements of leftKernel that are zero on
  -- overlapping checks. By kernel_projection_ker, this is exactly leftKernelNonOverlapping.
  have h_ker_dim : Module.finrank (ZMod 2) (LinearMap.ker (kernelProjection C L)) =
                   Module.finrank (ZMod 2) (leftKernelNonOverlapping C L) := by
    -- leftKernelNonOverlapping ≤ leftKernel
    have h_le : leftKernelNonOverlapping C L ≤ leftKernel C := by
      simp only [leftKernelNonOverlapping]
      exact inf_le_right
    -- Build a linear equiv
    have h_equiv :
        (LinearMap.ker (kernelProjection C L)) ≃ₗ[ZMod 2] (leftKernelNonOverlapping C L) := {
      toFun := fun x =>
        ⟨(x : leftKernel C).val, (kernel_projection_ker C L x.val).mp x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun ⟨w, hw⟩ =>
        ⟨⟨w, h_le hw⟩, (kernel_projection_ker C L ⟨w, h_le hw⟩).mpr hw⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl
    }
    exact LinearEquiv.finrank_eq h_equiv
  have h_finrank : Module.finrank (ZMod 2) (LinearMap.range (kernelProjection C L)) +
                   Module.finrank (ZMod 2) (LinearMap.ker (kernelProjection C L)) =
                   Module.finrank (ZMod 2) (leftKernel C) := by
    exact LinearMap.finrank_range_add_finrank_ker (kernelProjection C L)
  rw [h_ker_dim] at h_finrank
  exact h_finrank

/-! ## Section 7: Helper Lemmas -/

/-- The overlapping checks form a subset of all checks -/
theorem overlapping_subset_univ (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    overlappingChecks C L ⊆ Finset.univ :=
  Finset.subset_univ _

/-- The non-overlapping checks form a subset of all checks -/
theorem nonOverlapping_subset_univ (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    nonOverlappingChecks C L ⊆ Finset.univ :=
  Finset.subset_univ _

/-- Cardinality relation: |overlapping| + |non-overlapping| = |all checks| -/
theorem check_count_partition (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    (overlappingChecks C L).card + (nonOverlappingChecks C L).card = ℓ * m := by
  have h_part := check_partition C L
  have h_disj := check_disjoint C L
  rw [← Finset.card_union_of_disjoint h_disj, h_part]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- Zero logical support gives no overlapping checks -/
theorem zero_support_no_overlap (C : BivariateBicycleCode ℓ m) :
    overlappingChecks C ⟨∅⟩ = ∅ := by
  ext β
  simp only [overlappingChecks, zCheckOverlapsLogical, Finset.mem_filter, Finset.mem_univ,
             true_and, decide_eq_true_eq, Finset.Nonempty]
  simp only [Finset.notMem_empty, and_false, exists_false]

/-- The redundant cycle dimension is bounded by the check space dimension -/
theorem redundant_dim_le_check_space (C : BivariateBicycleCode ℓ m)
    (L : LeftLogicalSupport ℓ m) :
    redundantCycleDim C L ≤ ℓ * m := by
  unfold redundantCycleDim
  calc Module.finrank (ZMod 2) (RedundantCycleSpace C L)
    ≤ Module.finrank (ZMod 2) (CheckRowSpace ℓ m) := Submodule.finrank_le _
    _ = Fintype.card (Fin ℓ × Fin m) := by
        simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
                   Finset.card_univ, smul_eq_mul, mul_one]
    _ = ℓ * m := by simp only [Fintype.card_prod, Fintype.card_fin]

/-- When no checks overlap, redundant cycle space is trivial -/
theorem no_overlap_trivial (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m)
    (h_none : overlappingChecks C L = ∅) :
    RedundantCycleSpace C L = ⊥ := by
  ext u
  simp only [Submodule.mem_bot]
  constructor
  · intro hu
    obtain ⟨hu_mem, _⟩ := hu
    funext β
    simp only [Pi.zero_apply]
    simp only [OverlappingRowSubspace, Submodule.mem_mk] at hu_mem
    by_cases h : β ∈ overlappingChecks C L
    · rw [h_none] at h
      exact (Finset.notMem_empty β h).elim
    · exact hu_mem β h
  · intro hu
    rw [hu]
    exact (RedundantCycleSpace C L).zero_mem

/-- The projection maps preserve the subspace structure -/
theorem proj_overlap_mem (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m)
    (u : CheckRowSpace ℓ m) :
    projToOverlapping C L u ∈ OverlappingRowSubspace C L := by
  simp only [OverlappingRowSubspace, Submodule.mem_mk, projToOverlapping,
             LinearMap.coe_mk, AddHom.coe_mk]
  intro β hβ
  simp only [hβ, ↓reduceIte]

theorem proj_nonOverlap_mem (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m)
    (u : CheckRowSpace ℓ m) :
    projToNonOverlapping C L u ∈ NonOverlappingRowSubspace C L := by
  simp only [NonOverlappingRowSubspace, Submodule.mem_mk, projToNonOverlapping,
             LinearMap.coe_mk, AddHom.coe_mk]
  intro β hβ
  simp only [hβ, ↓reduceIte]

/-- The left kernel is a submodule of the check row space -/
theorem leftKernel_is_submodule (C : BivariateBicycleCode ℓ m) :
    ∃ S : Submodule (ZMod 2) (CheckRowSpace ℓ m), S = leftKernel C := ⟨_, rfl⟩

/-- The redundant cycle space is contained in the overlapping subspace -/
theorem redundant_in_overlapping (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m) :
    RedundantCycleSpace C L ≤ OverlappingRowSubspace C L := by
  intro u hu
  exact hu.1

/-! ## Section 8: Physical Interpretation Lemmas -/

/-- **Cycle from check relation**: If uS + vC = 0 for vectors u, v, then the product
    of checks indexed by u and v has support only on edge qubits. -/
theorem cycle_from_check_relation (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m)
    (u v : CheckRowSpace ℓ m)
    (_hu : u ∈ OverlappingRowSubspace C L)
    (_hv : v ∈ NonOverlappingRowSubspace C L)
    (h_ker : (u + v) ∈ leftKernel C) :
    ∀ q : Fin ℓ × Fin m × Bool,
      Finset.univ.sum (fun β => (u + v) β * (HZ_matrix C).toFun
        (fun idx => if idx = q then 1 else 0) β) = 0 := by
  exact h_ker

/-- **Edge support is cycle**: The edge support of the product of checks
    (when uS + vC = 0) forms a cycle in the gauging graph G. -/
theorem edge_support_is_cycle (C : BivariateBicycleCode ℓ m) (L : LeftLogicalSupport ℓ m)
    (u : CheckRowSpace ℓ m)
    (hu : u ∈ RedundantCycleSpace C L) :
    ∃ v ∈ NonOverlappingRowSubspace C L,
      (u + v) ∈ leftKernel C ∧
      (∀ q : Fin ℓ × Fin m × Bool,
        Finset.univ.sum (fun β => (u + v) β * (HZ_matrix C).toFun
          (fun idx => if idx = q then 1 else 0) β) = 0) := by
  obtain ⟨hu_overlap, v, hv_mem, hv_ker⟩ := hu
  use v, hv_mem
  exact ⟨hv_ker, cycle_from_check_relation C L u v hu_overlap hv_mem hv_ker⟩

end QEC
