import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Remarks.Rem_2_NotationPauliOperators
import Mathlib.Tactic

/-!
# Remark 9: Circuit Implementation

## Statement
The gauging measurement procedure can be implemented by a quantum circuit with
no additional qubits beyond the edge qubits:

1. Initialize each edge qubit e in state |0⟩_e.
2. Apply the entangling circuit ∏_v ∏_{e ∋ v} CX_{v → e}.
3. Measure X_v on all vertex qubits v ∈ V.
4. Apply the same entangling circuit again.
5. Measure Z_e on all edge qubits and discard them.
6. Apply byproduct corrections as in Definition 5.

**Why this works:** The entangling circuit transforms A_v = X_v ∏_{e ∋ v} X_e
into X_v (since CX_{v → e} conjugates X_v → X_v X_e and X_e → X_e).
So measuring X_v after the circuit is equivalent to measuring A_v before it.

## Main Results
- `cxConjugate` : the CX conjugation action on Pauli operators
- `cxConjugate_involutive` : CX conjugation is involutive
- `cxConjugate_mul` : CX conjugation distributes over multiplication
- `entanglingCircuitAction` : conjugation by the full entangling circuit
- `entanglingCircuitAction_involutive` : applying the circuit twice = identity
- `entanglingCircuit_transforms_gaussLaw` : the circuit transforms A_v to X_v
- `entanglingCircuit_transforms_pauliX_to_gaussLaw` : inverse direction
- `entanglingCircuit_preserves_symplecticInner` : circuit preserves commutation
- `transformed_gaussLaw_product` : ∏_v X_v = L (consistency check)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CircuitImplementation

open Finset PauliOp GaussFlux

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## CX Gate Conjugation on Pauli Operators -/

/-- The conjugation action of CX_{control → target} on a Pauli operator. -/
def cxConjugate {W : Type*} [DecidableEq W] (c t : W) (_hne : c ≠ t) (P : PauliOp W) :
    PauliOp W where
  xVec := fun q => if q = t then P.xVec q + P.xVec c else P.xVec q
  zVec := fun q => if q = c then P.zVec q + P.zVec t else P.zVec q

@[simp]
theorem cxConjugate_xVec_control {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) (P : PauliOp W) :
    (cxConjugate c t hne P).xVec c = P.xVec c := by
  simp [cxConjugate, hne]

@[simp]
theorem cxConjugate_xVec_target {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) (P : PauliOp W) :
    (cxConjugate c t hne P).xVec t = P.xVec t + P.xVec c := by
  simp [cxConjugate]

@[simp]
theorem cxConjugate_zVec_control {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) (P : PauliOp W) :
    (cxConjugate c t hne P).zVec c = P.zVec c + P.zVec t := by
  simp [cxConjugate]

@[simp]
theorem cxConjugate_zVec_target {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) (P : PauliOp W) :
    (cxConjugate c t hne P).zVec t = P.zVec t := by
  simp [cxConjugate, hne.symm]

/-- CX conjugation is involutive. -/
theorem cxConjugate_involutive {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) (P : PauliOp W) :
    cxConjugate c t hne (cxConjugate c t hne P) = P := by
  ext q
  · simp only [cxConjugate]
    split
    · next hqt => subst hqt; simp [hne, add_assoc, CharTwo.add_self_eq_zero]
    · rfl
  · simp only [cxConjugate]
    split
    · next hqc => subst hqc; simp [hne.symm, add_assoc, CharTwo.add_self_eq_zero]
    · rfl

/-- CX conjugation distributes over Pauli multiplication. -/
theorem cxConjugate_mul {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) (P Q : PauliOp W) :
    cxConjugate c t hne (P * Q) = cxConjugate c t hne P * cxConjugate c t hne Q := by
  ext q
  · simp only [cxConjugate, PauliOp.mul, mul_xVec, Pi.add_apply]
    split <;> ring
  · simp only [cxConjugate, PauliOp.mul, mul_zVec, Pi.add_apply]
    split <;> ring

@[simp]
theorem cxConjugate_one {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) :
    cxConjugate c t hne (1 : PauliOp W) = 1 := by
  ext q
  · simp [cxConjugate, one_xVec]
  · simp [cxConjugate, one_zVec]

/-! ## CX conjugation of basic Pauli operators -/

/-- CX_{c→t} maps X_c to X_c · X_t. -/
theorem cxConjugate_pauliX_control {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) :
    cxConjugate c t hne (pauliX c) = pauliX c * pauliX t := by
  ext q
  · simp only [cxConjugate, PauliOp.mul, pauliX, mul_xVec, Pi.add_apply, Pi.single_apply]
    split
    · next hqt => subst hqt; simp [hne.symm]
    · next hqt => simp [hqt]
  · simp only [cxConjugate, PauliOp.mul, pauliX, mul_zVec, Pi.add_apply, Pi.zero_apply, add_zero]
    split <;> rfl

/-- CX_{c→t} maps X_t to X_t (unchanged). -/
theorem cxConjugate_pauliX_target {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) :
    cxConjugate c t hne (pauliX t) = pauliX t := by
  ext q
  · simp only [cxConjugate, pauliX, Pi.single_apply]
    split
    · next hqt => subst hqt; simp [hne.symm]
    · rfl
  · simp only [cxConjugate, pauliX, Pi.zero_apply]
    split <;> simp

/-- CX_{c→t} maps Z_c to Z_c (unchanged). -/
theorem cxConjugate_pauliZ_control {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) :
    cxConjugate c t hne (pauliZ c) = pauliZ c := by
  ext q
  · simp only [cxConjugate, pauliZ, Pi.zero_apply, add_zero]
    split <;> rfl
  · simp only [cxConjugate, pauliZ, Pi.single_apply]
    split
    · next hqc => subst hqc; rw [if_neg (Ne.symm hne)]; simp
    · rfl

/-- CX_{c→t} maps Z_t to Z_c · Z_t. -/
theorem cxConjugate_pauliZ_target {W : Type*} [DecidableEq W]
    (c t : W) (hne : c ≠ t) :
    cxConjugate c t hne (pauliZ t) = pauliZ c * pauliZ t := by
  ext q
  · simp only [cxConjugate, PauliOp.mul, pauliZ, mul_xVec, Pi.add_apply, Pi.zero_apply, add_zero]
    split <;> rfl
  · simp only [cxConjugate, PauliOp.mul, pauliZ, mul_zVec, Pi.add_apply, Pi.single_apply]
    split
    · next hqc => subst hqc; simp [hne]
    · next hqc => simp [hqc]

/-! ## The Full Entangling Circuit Action -/

/-- The conjugation action of the full entangling circuit ∏_v ∏_{e ∋ v} CX_{v→e}. -/
noncomputable def entanglingCircuitAction (P : PauliOp (ExtQubit G)) :
    PauliOp (ExtQubit G) where
  xVec := fun q => match q with
    | Sum.inl w => P.xVec (Sum.inl w)
    | Sum.inr e => P.xVec (Sum.inr e) +
        ∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0
  zVec := fun q => match q with
    | Sum.inl w => P.zVec (Sum.inl w) +
        ∑ e ∈ incidentEdges G w, P.zVec (Sum.inr e)
    | Sum.inr e => P.zVec (Sum.inr e)

@[simp]
theorem entanglingCircuitAction_xVec_vertex (P : PauliOp (ExtQubit G)) (w : V) :
    (entanglingCircuitAction G P).xVec (Sum.inl w) = P.xVec (Sum.inl w) := by
  simp [entanglingCircuitAction]

@[simp]
theorem entanglingCircuitAction_xVec_edge (P : PauliOp (ExtQubit G)) (e : G.edgeSet) :
    (entanglingCircuitAction G P).xVec (Sum.inr e) =
      P.xVec (Sum.inr e) +
        ∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0 := by
  simp [entanglingCircuitAction]

@[simp]
theorem entanglingCircuitAction_zVec_vertex (P : PauliOp (ExtQubit G)) (w : V) :
    (entanglingCircuitAction G P).zVec (Sum.inl w) =
      P.zVec (Sum.inl w) + ∑ e ∈ incidentEdges G w, P.zVec (Sum.inr e) := by
  simp [entanglingCircuitAction]

@[simp]
theorem entanglingCircuitAction_zVec_edge (P : PauliOp (ExtQubit G)) (e : G.edgeSet) :
    (entanglingCircuitAction G P).zVec (Sum.inr e) = P.zVec (Sum.inr e) := by
  simp [entanglingCircuitAction]

-- Helper: in ZMod 2, a + b + b = a
private lemma zmod2_add_add_cancel (a b : ZMod 2) : a + b + b = a := by
  have : b + b = 0 := CharTwo.add_self_eq_zero b
  rw [add_assoc, this, add_zero]

/-- The entangling circuit action is involutive: applying it twice gives the identity. -/
theorem entanglingCircuitAction_involutive (P : PauliOp (ExtQubit G)) :
    entanglingCircuitAction G (entanglingCircuitAction G P) = P := by
  ext q
  · cases q with
    | inl w => simp
    | inr e =>
      simp only [entanglingCircuitAction_xVec_edge, entanglingCircuitAction_xVec_vertex]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · cases q with
    | inl w =>
      simp only [entanglingCircuitAction_zVec_vertex, entanglingCircuitAction_zVec_edge]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    | inr e => simp

/-- The entangling circuit action distributes over Pauli multiplication. -/
theorem entanglingCircuitAction_mul (P Q : PauliOp (ExtQubit G)) :
    entanglingCircuitAction G (P * Q) =
      entanglingCircuitAction G P * entanglingCircuitAction G Q := by
  ext q
  · cases q with
    | inl w =>
      simp only [entanglingCircuitAction_xVec_vertex, mul_xVec, Pi.add_apply]
    | inr e =>
      simp only [entanglingCircuitAction_xVec_edge, mul_xVec, Pi.add_apply]
      -- LHS: (P.x(e) + Q.x(e)) + ∑_v [v∈e] · (P.x(v) + Q.x(v))
      -- RHS: (P.x(e) + ∑_v [v∈e]·P.x(v)) + (Q.x(e) + ∑_v [v∈e]·Q.x(v))
      rw [show ∀ a b c d : ZMod 2, (a + b) + (c + d) = (a + c) + (b + d) from
        fun a b c d => by ring]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      split
      · rfl
      · simp
  · cases q with
    | inl w =>
      simp only [entanglingCircuitAction_zVec_vertex, mul_zVec, Pi.add_apply]
      rw [show ∀ a b c d : ZMod 2, (a + b) + (c + d) = (a + c) + (b + d) from
        fun a b c d => by ring]
      congr 1
      rw [← Finset.sum_add_distrib]
    | inr e =>
      simp only [entanglingCircuitAction_zVec_edge, mul_zVec, Pi.add_apply]

@[simp]
theorem entanglingCircuitAction_one :
    entanglingCircuitAction G (1 : PauliOp (ExtQubit G)) = 1 := by
  ext q
  · cases q with
    | inl w => simp [entanglingCircuitAction, one_xVec]
    | inr e => simp [entanglingCircuitAction, one_xVec]
  · cases q with
    | inl w => simp [entanglingCircuitAction, one_zVec]
    | inr e => simp [entanglingCircuitAction, one_zVec]

/-! ## Entangling circuit preserves symplectic inner product -/

/-- The entangling circuit preserves the symplectic inner product. -/
theorem entanglingCircuit_preserves_symplecticInner (P Q : PauliOp (ExtQubit G)) :
    symplecticInner (entanglingCircuitAction G P) (entanglingCircuitAction G Q) =
    symplecticInner P Q := by
  simp only [symplecticInner]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [entanglingCircuitAction_xVec_vertex, entanglingCircuitAction_zVec_vertex,
    entanglingCircuitAction_xVec_edge, entanglingCircuitAction_zVec_edge]
  -- Vertex contribution: ∑_v [x_P(v) · (z_Q(v) + ∑_e z_Q(e)) + (z_P(v) + ∑_e z_P(e)) · x_Q(v)]
  -- = ∑_v [x_P(v)·z_Q(v) + z_P(v)·x_Q(v)] + ∑_v [x_P(v)·∑_e z_Q(e) + (∑_e z_P(e))·x_Q(v)]
  -- Edge contribution: ∑_e [(x_P(e) + ∑_v x_P(v)) · z_Q(e) + z_P(e) · (x_Q(e) + ∑_v x_Q(v))]
  -- = ∑_e [x_P(e)·z_Q(e) + z_P(e)·x_Q(e)] + ∑_e [(∑_v x_P(v))·z_Q(e) + z_P(e)·(∑_v x_Q(v))]
  -- Cross terms cancel because a*b + b*a = 0 in ZMod 2 and ∑_v∑_{e∋v} = ∑_e∑_{v∈e}
  -- Strategy: show the cross terms from vertices and edges each individually sum to 0
  have hv_eq : ∀ v : V,
      P.xVec (Sum.inl v) * (Q.zVec (Sum.inl v) + ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e)) +
      (P.zVec (Sum.inl v) + ∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v) =
      P.xVec (Sum.inl v) * Q.zVec (Sum.inl v) + P.zVec (Sum.inl v) * Q.xVec (Sum.inl v) +
      (P.xVec (Sum.inl v) * ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e) +
       (∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v)) := by
    intro v; ring
  have he_eq : ∀ e : G.edgeSet,
      (P.xVec (Sum.inr e) + ∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) *
          Q.zVec (Sum.inr e) +
      P.zVec (Sum.inr e) *
          (Q.xVec (Sum.inr e) + ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0) =
      P.xVec (Sum.inr e) * Q.zVec (Sum.inr e) + P.zVec (Sum.inr e) * Q.xVec (Sum.inr e) +
      ((∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) * Q.zVec (Sum.inr e) +
       P.zVec (Sum.inr e) * ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0) := by
    intro e; ring
  have lhs_v : ∑ v : V,
      (P.xVec (Sum.inl v) * (Q.zVec (Sum.inl v) + ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e)) +
      (P.zVec (Sum.inl v) + ∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v)) =
      ∑ v : V, (P.xVec (Sum.inl v) * Q.zVec (Sum.inl v) + P.zVec (Sum.inl v) * Q.xVec (Sum.inl v)) +
      ∑ v : V, (P.xVec (Sum.inl v) * ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e) +
       (∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v)) := by
    rw [show ∑ v : V,
        (P.xVec (Sum.inl v) * (Q.zVec (Sum.inl v) + ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e)) +
        (P.zVec (Sum.inl v) + ∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v)) =
        ∑ v : V, (P.xVec (Sum.inl v) * Q.zVec (Sum.inl v) + P.zVec (Sum.inl v) * Q.xVec (Sum.inl v) +
        (P.xVec (Sum.inl v) * ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e) +
         (∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v))) from
      Finset.sum_congr rfl (fun v _ => hv_eq v)]
    rw [← Finset.sum_add_distrib]
  have lhs_e : ∑ e : G.edgeSet,
      ((P.xVec (Sum.inr e) + ∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) *
          Q.zVec (Sum.inr e) +
      P.zVec (Sum.inr e) *
          (Q.xVec (Sum.inr e) + ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0)) =
      ∑ e : G.edgeSet, (P.xVec (Sum.inr e) * Q.zVec (Sum.inr e) + P.zVec (Sum.inr e) * Q.xVec (Sum.inr e)) +
      ∑ e : G.edgeSet, ((∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) * Q.zVec (Sum.inr e) +
       P.zVec (Sum.inr e) * ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0) := by
    rw [show ∑ e : G.edgeSet,
        ((P.xVec (Sum.inr e) + ∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) *
            Q.zVec (Sum.inr e) +
        P.zVec (Sum.inr e) *
            (Q.xVec (Sum.inr e) + ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0)) =
        ∑ e : G.edgeSet, (P.xVec (Sum.inr e) * Q.zVec (Sum.inr e) + P.zVec (Sum.inr e) * Q.xVec (Sum.inr e) +
        ((∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) * Q.zVec (Sum.inr e) +
         P.zVec (Sum.inr e) * ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0)) from
      Finset.sum_congr rfl (fun e _ => he_eq e)]
    rw [← Finset.sum_add_distrib]
  rw [lhs_v, lhs_e]
  -- Goal: (∑_v main + ∑_v cross) + (∑_e main + ∑_e cross) = ∑_v main + ∑_e main
  -- Suffices to show cross_v + cross_e = 0
  suffices hcross :
      ∑ v : V, (P.xVec (Sum.inl v) * ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e) +
       (∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v)) +
      ∑ e : G.edgeSet, ((∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) * Q.zVec (Sum.inr e) +
       P.zVec (Sum.inr e) * ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0) = 0 by
    have h4 : ∀ a b c d : ZMod 2, (a + b) + (c + d) = (a + c) + (b + d) := fun a b c d => by ring
    rw [h4]; rw [hcross]; ring
  -- Expand vertex cross
  have hv_expand : ∑ v : V,
      (P.xVec (Sum.inl v) * ∑ e ∈ incidentEdges G v, Q.zVec (Sum.inr e) +
       (∑ e ∈ incidentEdges G v, P.zVec (Sum.inr e)) * Q.xVec (Sum.inl v)) =
      ∑ v : V, ∑ e ∈ incidentEdges G v,
        (P.xVec (Sum.inl v) * Q.zVec (Sum.inr e) +
         P.zVec (Sum.inr e) * Q.xVec (Sum.inl v)) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  -- Expand edge cross
  have he_expand : ∑ e : G.edgeSet,
      ((∑ v : V, if v ∈ (e : Sym2 V) then P.xVec (Sum.inl v) else 0) * Q.zVec (Sum.inr e) +
       P.zVec (Sum.inr e) * ∑ v : V, if v ∈ (e : Sym2 V) then Q.xVec (Sum.inl v) else 0) =
      ∑ e : G.edgeSet, ∑ v : V,
        if v ∈ (e : Sym2 V) then
          P.xVec (Sum.inl v) * Q.zVec (Sum.inr e) +
          P.zVec (Sum.inr e) * Q.xVec (Sum.inl v)
        else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split <;> ring
  rw [hv_expand, he_expand]
  -- The two cross sums are equal by double counting (swapping summation order),
  -- so their sum in ZMod 2 is X + X = 0.
  -- First, rewrite the vertex sum to use indicator functions over all edges:
  have hv_rewrite : ∑ v : V, ∑ e ∈ incidentEdges G v,
      (P.xVec (Sum.inl v) * Q.zVec (Sum.inr e) +
       P.zVec (Sum.inr e) * Q.xVec (Sum.inl v)) =
      ∑ v : V, ∑ e : G.edgeSet,
        if v ∈ (e : Sym2 V) then
          P.xVec (Sum.inl v) * Q.zVec (Sum.inr e) +
          P.zVec (Sum.inr e) * Q.xVec (Sum.inl v)
        else 0 := by
    apply Finset.sum_congr rfl; intro v _
    rw [← Finset.sum_filter]
    congr 1
  -- Swap summation order in vertex sum
  have hswap : ∑ v : V, ∑ e : G.edgeSet,
      (if v ∈ (e : Sym2 V) then
        P.xVec (Sum.inl v) * Q.zVec (Sum.inr e) +
        P.zVec (Sum.inr e) * Q.xVec (Sum.inl v)
      else 0) =
      ∑ e : G.edgeSet, ∑ v : V,
      (if v ∈ (e : Sym2 V) then
        P.xVec (Sum.inl v) * Q.zVec (Sum.inr e) +
        P.zVec (Sum.inr e) * Q.xVec (Sum.inl v)
      else 0) := Finset.sum_comm
  rw [hv_rewrite, hswap]
  exact CharTwo.add_self_eq_zero _

/-- The entangling circuit preserves Pauli commutation. -/
theorem entanglingCircuit_preserves_commutation (P Q : PauliOp (ExtQubit G)) :
    PauliCommute (entanglingCircuitAction G P) (entanglingCircuitAction G Q) ↔
    PauliCommute P Q := by
  simp only [PauliCommute]
  rw [entanglingCircuit_preserves_symplecticInner]

/-! ## Main Theorem: Entangling Circuit Transforms A_v to X_v -/

/-- **Key result**: The entangling circuit transforms A_v to X_v. -/
theorem entanglingCircuit_transforms_gaussLaw (v : V) :
    entanglingCircuitAction G (gaussLawOp G v) = pauliX (Sum.inl v) := by
  ext q
  · cases q with
    | inl w =>
      simp only [entanglingCircuitAction_xVec_vertex, gaussLawOp, pauliX, Pi.single_apply,
        Sum.inl.injEq]
    | inr e =>
      simp only [entanglingCircuitAction_xVec_edge, gaussLawOp, pauliX, Pi.single_apply]
      -- Need: [v∈e] + ∑_w [w∈e]·[w=v] = 0 on Sum.inr
      -- Since Sum.inl v ≠ Sum.inr e, the RHS = 0
      -- The sum ∑_w [w∈e]·[w=v] = [v∈e]
      -- So LHS = [v∈e] + [v∈e] = 0
      have hsum : ∑ w : V,
          (if w ∈ (e : Sym2 V) then (if w = v then (1 : ZMod 2) else 0) else 0) =
          if v ∈ (e : Sym2 V) then 1 else 0 := by
        rw [show ∑ w : V,
            (if w ∈ (e : Sym2 V) then (if w = v then (1 : ZMod 2) else 0) else 0) =
            ∑ w : V, (if w = v then (if v ∈ (e : Sym2 V) then 1 else 0) else 0) from by
          apply Finset.sum_congr rfl; intro w _
          by_cases hw : w = v <;> by_cases hwe : w ∈ (e : Sym2 V) <;> simp_all]
        rw [Finset.sum_ite_eq' Finset.univ v (fun _ => if v ∈ (e : Sym2 V) then 1 else 0)]
        simp
      rw [hsum]
      by_cases hve : v ∈ (e : Sym2 V) <;> simp [hve, CharTwo.add_self_eq_zero]
  · cases q with
    | inl w =>
      simp only [entanglingCircuitAction_zVec_vertex, gaussLawOp, pauliX, Pi.zero_apply]
      simp
    | inr e =>
      simp only [entanglingCircuitAction_zVec_edge, gaussLawOp, pauliX, Pi.zero_apply]

/-- The inverse direction: the circuit transforms X_v back to A_v. -/
theorem entanglingCircuit_transforms_pauliX_to_gaussLaw (v : V) :
    entanglingCircuitAction G (pauliX (Sum.inl v)) = gaussLawOp G v := by
  rw [← entanglingCircuit_transforms_gaussLaw G v, entanglingCircuitAction_involutive]

/-- Measuring X_v after the entangling circuit is equivalent to measuring A_v before it. -/
theorem measuring_Xv_after_circuit_eq_Av (v : V) :
    entanglingCircuitAction G (gaussLawOp G v) = pauliX (Sum.inl v) :=
  entanglingCircuit_transforms_gaussLaw G v

/-! ## Effect on edge Z operators -/

/-- The entangling circuit transforms Z_e into Z on e and both its endpoints. -/
theorem entanglingCircuit_transforms_edgeZ (e : G.edgeSet) :
    entanglingCircuitAction G (pauliZ (Sum.inr e)) =
      PauliOp.mk 0 (fun q => match q with
        | Sum.inl w => if w ∈ (e : Sym2 V) then 1 else 0
        | Sum.inr e' => if e' = e then 1 else 0) := by
  ext q
  · cases q with
    | inl w =>
      simp [entanglingCircuitAction, pauliZ, Pi.single_apply]
    | inr e' =>
      simp [entanglingCircuitAction, pauliZ, Pi.single_apply]
  · cases q with
    | inl w =>
      simp only [entanglingCircuitAction_zVec_vertex, pauliZ, Pi.single_apply, Pi.zero_apply]
      simp only [Sum.inr.injEq]
      have : (if Sum.inl w = Sum.inr e then (1 : ZMod 2) else 0) = 0 := by simp
      rw [this, zero_add]
      rw [show ∑ e' ∈ incidentEdges G w, (if e' = e then (1 : ZMod 2) else 0) =
        if e ∈ incidentEdges G w then 1 else 0 from
        Finset.sum_ite_eq' (incidentEdges G w) e (fun _ => 1)]
      simp [mem_incidentEdges]
    | inr e' =>
      simp [entanglingCircuitAction, pauliZ, Pi.single_apply]

/-! ## Circuit Protocol Steps -/

/-- Step 2: The entangling circuit transforms A_v to X_v. -/
theorem circuit_step2_transforms_Av_to_Xv (v : V) :
    entanglingCircuitAction G (gaussLawOp G v) = pauliX (Sum.inl v) :=
  entanglingCircuit_transforms_gaussLaw G v

/-- Step 4: Applying the entangling circuit again undoes the transformation. -/
theorem circuit_step4_undoes_step2 (P : PauliOp (ExtQubit G)) :
    entanglingCircuitAction G (entanglingCircuitAction G P) = P :=
  entanglingCircuitAction_involutive G P

/-- Steps 2+3+4: Measuring X_v in the CX frame = measuring A_v in the original frame. -/
theorem steps234_equivalent_to_measuring_Av (v : V) :
    entanglingCircuitAction G (pauliX (Sum.inl v)) = gaussLawOp G v :=
  entanglingCircuit_transforms_pauliX_to_gaussLaw G v

/-- After step 4, edge Z measurements are back in the original frame. -/
theorem circuit_edge_measurement_in_original_frame (e : G.edgeSet) :
    entanglingCircuitAction G (entanglingCircuitAction G (pauliZ (Sum.inr e))) =
      pauliZ (Sum.inr e) :=
  entanglingCircuitAction_involutive G (pauliZ (Sum.inr e))

/-! ## Simultaneous transformation of all Gauss operators -/

/-- All Gauss operators are simultaneously transformed to X_v. -/
theorem entanglingCircuit_transforms_all_gaussLaw :
    ∀ v : V, entanglingCircuitAction G (gaussLawOp G v) = pauliX (Sum.inl v) :=
  fun v => entanglingCircuit_transforms_gaussLaw G v

-- Re-prove the product lemma locally since it's private in Def_2
private lemma prod_pauliOp_xVec' {α : Type*} [DecidableEq α]
    {W : Type*} [Fintype W] [DecidableEq W]
    (S : Finset α) (f : α → PauliOp W) (q : W) :
    (∏ a ∈ S, f a).xVec q = ∑ a ∈ S, (f a).xVec q := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert _ _ ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    simp only [mul_xVec, Pi.add_apply]
    rw [ih]

private lemma prod_pauliOp_zVec' {α : Type*} [DecidableEq α]
    {W : Type*} [Fintype W] [DecidableEq W]
    (S : Finset α) (f : α → PauliOp W) (q : W) :
    (∏ a ∈ S, f a).zVec q = ∑ a ∈ S, (f a).zVec q := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert _ _ ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    simp only [mul_zVec, Pi.add_apply]
    rw [ih]

/-- The product of all transformed operators ∏_v X_v equals L (logical operator). -/
theorem transformed_gaussLaw_product :
    (∏ v : V, pauliX (Sum.inl v : ExtQubit G)) = logicalOp G := by
  ext q
  · rw [show (∏ v : V, pauliX (Sum.inl v : ExtQubit G)).xVec q =
        (∏ v ∈ Finset.univ, pauliX (Sum.inl v : ExtQubit G)).xVec q by simp]
    rw [prod_pauliOp_xVec']
    cases q with
    | inl w =>
      simp only [pauliX, Pi.single_apply, logicalOp, Sum.inl.injEq]
      -- Goal: (∑ x, if w = x then 1 else 0) = 1
      rw [show ∑ x : V, (if w = x then (1 : ZMod 2) else 0) =
        ∑ x ∈ Finset.univ, (if w = x then 1 else 0) from by simp]
      rw [Finset.sum_ite_eq Finset.univ w]
      simp
    | inr e =>
      simp only [pauliX, Pi.single_apply, logicalOp]
      apply Finset.sum_eq_zero
      intro v _
      simp
  · rw [show (∏ v : V, pauliX (Sum.inl v : ExtQubit G)).zVec q =
        (∏ v ∈ Finset.univ, pauliX (Sum.inl v : ExtQubit G)).zVec q by simp]
    rw [prod_pauliOp_zVec']
    simp [pauliX, logicalOp]

/-- The entangling circuit applied to L gives L. -/
theorem entanglingCircuit_preserves_logical :
    entanglingCircuitAction G (logicalOp G) = logicalOp G := by
  ext q
  · cases q with
    | inl w =>
      simp [entanglingCircuitAction, logicalOp]
    | inr e =>
      simp only [entanglingCircuitAction_xVec_edge, logicalOp]
      -- Need: 0 + ∑_v [v ∈ e] · 1 = 0
      -- ∑_v [v ∈ e] = 2 = 0 mod 2 (edge has 2 endpoints)
      obtain ⟨e_val, he⟩ := e
      induction e_val using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := by
          intro h; subst h; exact G.loopless a (G.mem_edgeSet.mp he)
        have hsum : ∑ v : V,
            (if v ∈ (⟨s(a, b), he⟩ : G.edgeSet).val then (1 : ZMod 2) else 0) =
            ∑ v : V, ((if v = a then 1 else 0) + (if v = b then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro v _
          simp only [Sym2.mem_iff]
          by_cases hva : v = a
          · subst hva; simp [hab]
          · by_cases hvb : v = b
            · subst hvb; simp [hva]
            · simp [hva, hvb]
        rw [hsum, Finset.sum_add_distrib]
        simp [CharTwo.add_self_eq_zero]
  · cases q with
    | inl w => simp [entanglingCircuitAction, logicalOp]
    | inr e => simp [entanglingCircuitAction, logicalOp]

end CircuitImplementation
