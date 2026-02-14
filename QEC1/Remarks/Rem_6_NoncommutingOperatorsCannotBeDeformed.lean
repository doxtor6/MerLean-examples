import QEC1.Definitions.Def_3_DeformedOperator
import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Remarks.Rem_2_NotationPauliOperators
import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Remark 6: Noncommuting Operators Cannot Be Deformed

## Statement
A Pauli operator P that does not commute with L cannot be deformed to commute with all
Gauss's law operators A_v. The boundary condition ∂γ = S_Z(P)|_V has no solution when
CommutesWithLogical(P) fails, and multiplying P by Z_e operators or commuting stabilizers
cannot change this.

## Main Results
- `noncommuting_cannot_be_deformed` : ¬CommutesWithLogical(P) → ¬∃ γ, BoundaryCondition(G, P, γ)
- `zSupportOnVertices_sum_mul` : Z-support sum is additive under multiplication
- `mul_commuting_preserves_commutesWithLogical` : CommutesWithLogical is closed under mul
- `commutesWithLogical_mul_iff` : CommutesWithLogical(P*Q) ↔ CommutesWithLogical(P) when Q commutes
- `no_modification_helps` : ¬CommutesWithLogical(P) ∧ CommutesWithLogical(Q) → ¬CommutesWithLogical(P*Q)
- `no_modified_deformation_exists` : no boundary condition for P*Q either
- `zSupport_not_in_boundary_range` : zSupportOnVertices(P) ∉ range(∂)
- `boundaryCondition_exists_iff_in_image` : boundary condition ↔ membership in range(∂)

## Corollaries
- singleZ (pauliZ) flips CommutesWithLogical
- Stabilizers preserve non-commuting status
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace NoncommutingOperatorsCannotBeDeformed

open Finset PauliOp DeformedOperator GaussFlux GraphMaps

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## Main Theorem: Noncommuting Operators Cannot Be Deformed -/

/-- If ¬CommutesWithLogical(P), then no edge-path γ satisfies the boundary condition.
    This is the contrapositive of `boundaryCondition_implies_commutes`. -/
theorem noncommuting_cannot_be_deformed
    (P : PauliOp V) (hP : ¬ CommutesWithLogical P) :
    ¬ ∃ γ : G.edgeSet → ZMod 2, BoundaryCondition G P γ := by
  intro ⟨γ, hγ⟩
  exact hP (boundaryCondition_implies_commutes G P γ hγ)

/-! ## Z-Support Sum Additivity -/

/-- The sum of zSupportOnVertices is additive under Pauli multiplication. -/
theorem zSupportOnVertices_sum_mul (P Q : PauliOp V) :
    ∑ v : V, zSupportOnVertices (P * Q) v =
    ∑ v : V, zSupportOnVertices P v + ∑ v : V, zSupportOnVertices Q v := by
  rw [← Finset.sum_add_distrib]
  congr 1; ext v
  exact zSupportOnVertices_mul P Q v

/-! ## CommutesWithLogical Preserved Under Multiplication -/

/-- If CommutesWithLogical(P) and CommutesWithLogical(Q), then CommutesWithLogical(P * Q). -/
theorem mul_commuting_preserves_commutesWithLogical
    (P Q : PauliOp V) (hP : CommutesWithLogical P) (hQ : CommutesWithLogical Q) :
    CommutesWithLogical (P * Q) := by
  unfold CommutesWithLogical at *
  rw [zSupportOnVertices_sum_mul, hP, hQ, add_zero]

/-- Contrapositive: if ¬CommutesWithLogical(P * Q) and CommutesWithLogical(Q),
    then ¬CommutesWithLogical(P). -/
theorem mul_commuting_contrapositive
    (P Q : PauliOp V) (hPQ : ¬ CommutesWithLogical (P * Q))
    (hQ : CommutesWithLogical Q) : ¬ CommutesWithLogical P := by
  intro hP
  exact hPQ (mul_commuting_preserves_commutesWithLogical P Q hP hQ)

/-! ## singleZ (pauliZ) and CommutesWithLogical -/

/-- The sum of zSupportOnVertices of pauliZ(v) is 1. -/
lemma zSupportOnVertices_singleZ_sum (v : V) :
    ∑ w : V, zSupportOnVertices (pauliZ v) w = 1 := by
  unfold zSupportOnVertices
  -- Goal: (∑ w, if (pauliZ v).zVec w ≠ 0 then 1 else 0) = 1
  have h_eq : ∀ w : V, (if (pauliZ v).zVec w ≠ 0 then (1 : ZMod 2) else 0) =
      if w = v then 1 else 0 := by
    intro w
    simp only [pauliZ, ne_eq]
    by_cases hw : w = v
    · subst hw; simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hw, hw]
  simp_rw [h_eq]
  simp [Finset.sum_ite_eq']

/-- pauliZ(v) does not commute with L. -/
theorem singleZ_not_commutesWithLogical (v : V) :
    ¬ CommutesWithLogical (pauliZ v) := by
  unfold CommutesWithLogical
  rw [zSupportOnVertices_singleZ_sum v]
  exact one_ne_zero

/-- Multiplying by pauliZ(v) flips CommutesWithLogical. -/
theorem singleZ_flips_commutesWithLogical (P : PauliOp V) (v : V) :
    CommutesWithLogical (P * pauliZ v) ↔ ¬ CommutesWithLogical P := by
  unfold CommutesWithLogical
  rw [zSupportOnVertices_sum_mul, zSupportOnVertices_singleZ_sum]
  constructor
  · intro h hP
    rw [hP, zero_add] at h
    exact one_ne_zero h
  · intro hP
    -- In ZMod 2, every element is 0 or 1. Since sum ≠ 0, sum = 1.
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
      intro a; fin_cases a <;> simp
    cases h01 (∑ v : V, zSupportOnVertices P v) with
    | inl h => exact absurd h hP
    | inr h => rw [h]; exact CharTwo.add_self_eq_zero 1

/-! ## Z-Support Restricted to Vertices on the Extended System -/

/-- The Z-support sum restricted to vertex qubits of a Pauli operator on the extended
    system V ⊕ G.edgeSet. This captures CommutesWithLogical for the extended system. -/
def zSupportRestricted (P : PauliOp (ExtQubit G)) : ZMod 2 :=
  ∑ v : V, if P.zVec (Sum.inl v) ≠ 0 then 1 else 0

/-- CommutesWithLogical on the extended system, restricted to vertex qubits. -/
def CommutesWithLogical' (P : PauliOp (ExtQubit G)) : Prop :=
  zSupportRestricted G P = 0

/-- Multiplying a Pauli operator on the extended system V ⊕ E by Z on an edge qubit
    does not change the CommutesWithLogical' condition. This is because pauliZ on an
    edge qubit (Sum.inr e) has zero Z-support on vertex qubits (Sum.inl v). -/
theorem singleZ_edge_preserves_commutesWithLogical'
    (P : PauliOp (ExtQubit G)) (e : G.edgeSet) :
    CommutesWithLogical' G (P * pauliZ (Sum.inr e)) ↔ CommutesWithLogical' G P := by
  unfold CommutesWithLogical' zSupportRestricted
  suffices h : ∀ v : V, (if (P * pauliZ (Sum.inr e)).zVec (Sum.inl v) ≠ 0 then (1 : ZMod 2) else 0) =
      (if P.zVec (Sum.inl v) ≠ 0 then 1 else 0) by
    simp_rw [h]
  intro v
  have : (pauliZ (Sum.inr e)).zVec (Sum.inl v) = 0 := by
    simp [pauliZ, Pi.single_eq_of_ne (Sum.inl_ne_inr)]
  simp only [mul_zVec, Pi.add_apply, this, add_zero]

/-! ## Stabilizer Preserves Non-Commuting Status -/

/-- If ¬CommutesWithLogical(P) and CommutesWithLogical(s), then ¬CommutesWithLogical(P * s). -/
theorem stabilizer_preserves_noncommuting
    (P s : PauliOp V) (hP : ¬ CommutesWithLogical P) (hs : CommutesWithLogical s) :
    ¬ CommutesWithLogical (P * s) := by
  intro hPs
  have : CommutesWithLogical P := by
    have hss : P * s * s = P := by
      rw [PauliOp.mul_assoc, PauliOp.mul_self, PauliOp.mul_one]
    rw [← hss]
    exact mul_commuting_preserves_commutesWithLogical (P * s) s hPs hs
  exact hP this

/-! ## No Deformation Exists -/

/-- For every edge-path γ, the boundary condition fails when ¬CommutesWithLogical(P). -/
theorem no_deformation_exists
    (P : PauliOp V) (hP : ¬ CommutesWithLogical P)
    (γ : G.edgeSet → ZMod 2) : ¬ BoundaryCondition G P γ := by
  intro hγ
  exact hP (boundaryCondition_implies_commutes G P γ hγ)

/-! ## CommutesWithLogical Invariant Under Commuting Multiplication -/

/-- CommutesWithLogical(P * Q) ↔ CommutesWithLogical(P) when CommutesWithLogical(Q). -/
theorem commutesWithLogical_mul_iff
    (P Q : PauliOp V) (hQ : CommutesWithLogical Q) :
    CommutesWithLogical (P * Q) ↔ CommutesWithLogical P := by
  constructor
  · intro hPQ
    have hQQ : P * Q * Q = P := by
      rw [PauliOp.mul_assoc, PauliOp.mul_self, PauliOp.mul_one]
    rw [← hQQ]
    exact mul_commuting_preserves_commutesWithLogical (P * Q) Q hPQ hQ
  · intro hP
    exact mul_commuting_preserves_commutesWithLogical P Q hP hQ

/-! ## No Modification Helps -/

/-- If ¬CommutesWithLogical(P) and CommutesWithLogical(Q), then ¬CommutesWithLogical(P * Q).
    No product of Z_e operators and commuting stabilizers can help. -/
theorem no_modification_helps
    (P Q : PauliOp V) (hP : ¬ CommutesWithLogical P) (hQ : CommutesWithLogical Q) :
    ¬ CommutesWithLogical (P * Q) := by
  rwa [commutesWithLogical_mul_iff P Q hQ]

/-! ## No Modified Deformation Exists -/

/-- If ¬CommutesWithLogical(P) and CommutesWithLogical(Q), then no boundary condition
    holds for P * Q either. -/
theorem no_modified_deformation_exists
    (P Q : PauliOp V) (hP : ¬ CommutesWithLogical P) (hQ : CommutesWithLogical Q)
    (γ : G.edgeSet → ZMod 2) : ¬ BoundaryCondition G (P * Q) γ := by
  intro hγ
  exact no_modification_helps P Q hP hQ (boundaryCondition_implies_commutes G (P * Q) γ hγ)

/-! ## Z-Support Not in Range of Boundary Map -/

/-- The boundary condition for P and γ is equivalent to zSupportOnVertices(P) being
    in the image of the boundary map applied to γ. -/
lemma boundaryCondition_exists_iff_in_image (P : PauliOp V) :
    (∃ γ : G.edgeSet → ZMod 2, BoundaryCondition G P γ) ↔
    zSupportOnVertices P ∈ LinearMap.range (boundaryMap G) := by
  unfold BoundaryCondition
  constructor
  · rintro ⟨γ, hγ⟩
    exact LinearMap.mem_range.mpr ⟨γ, hγ⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, hγ⟩

/-- If ¬CommutesWithLogical(P), then zSupportOnVertices(P) ∉ range(∂). -/
theorem zSupport_not_in_boundary_range
    (P : PauliOp V) (hP : ¬ CommutesWithLogical P) :
    zSupportOnVertices P ∉ LinearMap.range (boundaryMap G) := by
  rw [← boundaryCondition_exists_iff_in_image G P]
  exact noncommuting_cannot_be_deformed G P hP

end NoncommutingOperatorsCannotBeDeformed
