import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Data.Fintype.Powerset

import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_8_Detector

/-!
# Def_9: Syndrome

## Statement
The **syndrome** of a spacetime fault F is the set of detectors violated by F. Formally:
$$\text{syndrome}(F) = \{D : D \text{ is a detector and } D \text{ reports } -1 \text{ in the presence of } F\}$$

Equivalently, the syndrome is the binary vector over the set of all detectors, where entry D is 1
if detector D is violated and 0 otherwise.

Key properties:
1. The syndrome function is Z₂-linear: syndrome(F₁ · F₂) = syndrome(F₁) + syndrome(F₂) (symmetric difference).
2. A spacetime stabilizer (trivial fault) has empty syndrome.
3. A **logical fault** is a non-trivial fault with empty syndrome.

## Main Definitions
- `Syndrome` : The syndrome of a spacetime fault (set of violated detectors)
- `syndrome` : Function computing the syndrome of a fault
- `syndromeVector` : Binary vector representation of the syndrome
- `hasEmptySyndrome` : Predicate for faults with no violated detectors

## Key Properties
- `syndrome_identity` : Identity fault has empty syndrome
- `syndrome_mul` : Syndrome is Z₂-linear (symmetric difference under composition)
- `syndrome_inv` : Syndrome of inverse equals syndrome of original
- `isLogicalFault_iff` : A logical fault is non-trivial with empty syndrome
-/

open Finset

set_option linter.unusedSectionVars false

variable {V E M : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq M]

/-! ## Syndrome Definition

The syndrome of a spacetime fault is the set of detectors it violates.
We use Finset directly rather than a wrapper type. -/

/-- The syndrome of a spacetime fault: the set of detectors violated by the fault.
    A detector is violated if the observed parity differs from expected parity. -/
abbrev Syndrome (V E M : Type*) [DecidableEq V] [DecidableEq E] [DecidableEq M] :=
  Finset (Detector V E M)

namespace Syndrome

/-- The empty syndrome (no detectors violated) -/
def empty : Syndrome V E M := ∅

/-- Combine two syndromes via symmetric difference (Z₂ addition) -/
def add (s₁ s₂ : Syndrome V E M) : Syndrome V E M := symmDiff s₁ s₂

@[simp] lemma empty_eq : (empty : Syndrome V E M) = ∅ := rfl

@[simp] lemma add_eq (s₁ s₂ : Syndrome V E M) : add s₁ s₂ = symmDiff s₁ s₂ := rfl

/-- Syndrome addition is commutative -/
theorem add_comm' (s₁ s₂ : Syndrome V E M) : add s₁ s₂ = add s₂ s₁ :=
  symmDiff_comm s₁ s₂

/-- Syndrome addition is associative -/
theorem add_assoc' (s₁ s₂ s₃ : Syndrome V E M) : add (add s₁ s₂) s₃ = add s₁ (add s₂ s₃) :=
  symmDiff_assoc s₁ s₂ s₃

/-- Empty syndrome is additive identity (right) -/
@[simp] theorem add_empty' (s : Syndrome V E M) : add s empty = s := by
  simp only [add_eq, empty_eq, ← Finset.bot_eq_empty, symmDiff_bot]

/-- Empty syndrome is additive identity (left) -/
@[simp] theorem empty_add' (s : Syndrome V E M) : add empty s = s := by
  simp only [add_eq, empty_eq, ← Finset.bot_eq_empty, bot_symmDiff]

/-- Every syndrome is its own inverse (self-inverse in Z₂) -/
@[simp] theorem add_self' (s : Syndrome V E M) : add s s = empty := by
  simp only [add_eq, empty_eq, symmDiff_self, Finset.bot_eq_empty]

/-- The cardinality of the syndrome (number of violated detectors) -/
def card (s : Syndrome V E M) : ℕ := Finset.card s

@[simp] lemma card_empty' : card (empty : Syndrome V E M) = 0 := rfl

/-- A syndrome is empty iff its cardinality is 0 -/
lemma isEmpty_iff_card_zero (s : Syndrome V E M) : s = empty ↔ card s = 0 := by
  simp [card, empty_eq, Finset.card_eq_zero]

end Syndrome

/-! ## Computing the Syndrome

Given a detector collection and measurement outcomes, compute which detectors are violated. -/

/-- Apply a spacetime fault to measurement outcomes.
    Time-faults flip the classical measurement outcome. -/
def applyFaultToOutcomes'
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) : OutcomeAssignment M :=
  fun m t => if fault.timeErrors m t then baseOutcomes m t + 1 else baseOutcomes m t

/-- Compute the syndrome of a spacetime fault given a detector collection.
    Returns the set of detectors violated by the fault. -/
def syndrome
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) : Syndrome V E M :=
  DC.detectors.filter fun D => D.isViolated (applyFaultToOutcomes' baseOutcomes fault)

/-- A fault has empty syndrome if it violates no detectors -/
def hasEmptySyndrome'
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) : Prop :=
  syndrome DC baseOutcomes fault = ∅

instance decHasEmptySyndrome'
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) :
    Decidable (hasEmptySyndrome' DC baseOutcomes fault) :=
  inferInstanceAs (Decidable (_ = ∅))

/-! ## Syndrome as Binary Vector

The syndrome can equivalently be viewed as a binary vector indexed by detectors. -/

/-- The syndrome as a function to ZMod 2: 1 if violated, 0 if satisfied -/
def syndromeVector
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M)
    (D : Detector V E M) : ZMod 2 :=
  if D ∈ syndrome DC baseOutcomes fault then 1 else 0

@[simp] lemma syndromeVector_violated
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M)
    (D : Detector V E M)
    (hD : D ∈ DC.detectors)
    (hviol : D.isViolated (applyFaultToOutcomes' baseOutcomes fault)) :
    syndromeVector DC baseOutcomes fault D = 1 := by
  simp only [syndromeVector, syndrome, Finset.mem_filter, hD, hviol, and_self, ↓reduceIte]

@[simp] lemma syndromeVector_satisfied
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M)
    (D : Detector V E M)
    (hsat : ¬D.isViolated (applyFaultToOutcomes' baseOutcomes fault)) :
    syndromeVector DC baseOutcomes fault D = 0 := by
  simp only [syndromeVector, syndrome, Finset.mem_filter]
  split_ifs with h
  · exact absurd h.2 hsat
  · rfl

/-- Syndrome vector is 1 iff detector is violated -/
theorem syndromeVector_eq_one_iff
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M)
    (D : Detector V E M)
    (hD : D ∈ DC.detectors) :
    syndromeVector DC baseOutcomes fault D = 1 ↔
    D.isViolated (applyFaultToOutcomes' baseOutcomes fault) := by
  constructor
  · intro h
    simp only [syndromeVector, syndrome, Finset.mem_filter] at h
    split_ifs at h with hmem
    · exact hmem.2
    · simp at h
  · intro hviol
    exact syndromeVector_violated DC baseOutcomes fault D hD hviol

/-! ## Key Properties -/

section Properties

variable (DC : DetectorCollection V E M)
variable (baseOutcomes : OutcomeAssignment M)

/-- The identity fault has empty syndrome when base outcomes satisfy all detectors -/
theorem syndrome_identity
    (h_base : DC.allSatisfied baseOutcomes) :
    syndrome DC baseOutcomes (1 : SpacetimeFault V E M) = ∅ := by
  simp only [syndrome, Finset.filter_eq_empty_iff]
  intro D hD
  have heq : applyFaultToOutcomes' baseOutcomes (1 : SpacetimeFault V E M) = baseOutcomes := by
    funext m t
    simp only [applyFaultToOutcomes', SpacetimeFault.one_timeErrors]
    -- if false then baseOutcomes m t + 1 else baseOutcomes m t = baseOutcomes m t
    rfl
  rw [heq, ← Detector.satisfied_iff_not_violated]
  rw [DetectorCollection.allSatisfied_iff] at h_base
  exact h_base D hD

/-- Empty syndrome iff all detectors in the collection are satisfied -/
theorem hasEmptySyndrome'_iff
    (fault : SpacetimeFault V E M) :
    hasEmptySyndrome' DC baseOutcomes fault ↔
    ∀ D ∈ DC.detectors, D.isSatisfied (applyFaultToOutcomes' baseOutcomes fault) := by
  unfold hasEmptySyndrome' syndrome
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h D hD
    rw [Detector.satisfied_iff_not_violated]
    exact h hD
  · intro h D hD
    rw [← Detector.satisfied_iff_not_violated]
    exact h D hD

end Properties

/-! ## Z₂-Linearity of Syndrome

The key property: syndrome(F₁ · F₂) = syndrome(F₁) + syndrome(F₂) (symmetric difference).

This holds when faults only affect detectors through time-faults (measurement flips),
and each detector monitors a fixed set of measurements. -/

section Linearity

variable (DC : DetectorCollection V E M)
variable (baseOutcomes : OutcomeAssignment M)

/-- Helper: symmetric difference cardinality has the same parity as the sum of cardinalities -/
private lemma card_symmDiff_mod_two [DecidableEq α] (A B : Finset α) :
    (symmDiff A B).card % 2 = (A.card + B.card) % 2 := by
  -- symmDiff A B = (A \ B) ∪ (B \ A) and these are disjoint
  have h_eq : symmDiff A B = (A \ B) ∪ (B \ A) := by
    ext x
    simp only [mem_symmDiff, mem_union, mem_sdiff]
  rw [h_eq, card_union_of_disjoint (disjoint_sdiff_sdiff)]
  -- Use card_sdiff: #(t \ s) = #t - #(s ∩ t)
  have hA : (A \ B).card = A.card - (B ∩ A).card := card_sdiff (t := A) (s := B)
  have hB : (B \ A).card = B.card - (A ∩ B).card := card_sdiff (t := B) (s := A)
  rw [hA, hB]
  have h_inter_comm : (A ∩ B).card = (B ∩ A).card := by rw [inter_comm]
  rw [← h_inter_comm]
  -- Now we have: (A.card - (A ∩ B).card) + (B.card - (A ∩ B).card)
  have h_sub_A : (A ∩ B).card ≤ A.card := card_le_card inter_subset_left
  have h_sub_B : (A ∩ B).card ≤ B.card := card_le_card inter_subset_right
  omega

set_option linter.unusedDecidableInType false
/-- Helper: applying two faults in sequence -/
lemma applyFaultToOutcomes_mul
    (f g : SpacetimeFault V E M) (m : M) (t : TimeStep) :
    applyFaultToOutcomes' (V := V) (E := E) baseOutcomes (f * g) m t =
    if xor (f.timeErrors m t) (g.timeErrors m t)
    then baseOutcomes m t + 1
    else baseOutcomes m t := by
  simp only [applyFaultToOutcomes', SpacetimeFault.mul_timeErrors]

/-- Condition for Z₂-linearity: detectors depend only on time-faults in a simple way.
    Specifically, each detector's violation status depends on the XOR of time-faults
    over its measurement events. -/
structure SyndromeLinearCondition
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M) : Prop where
  /-- Each detector's violation only depends on time-faults at its measurement events -/
  localDependence : ∀ (f g : SpacetimeFault V E M) (D : Detector V E M),
    D ∈ DC.detectors →
    (∀ e ∈ D.measEvents, f.timeErrors e.measurement e.time = g.timeErrors e.measurement e.time) →
    (D.isViolated (applyFaultToOutcomes' baseOutcomes f) ↔
     D.isViolated (applyFaultToOutcomes' baseOutcomes g))
  /-- Violation is determined by parity of time-faults on measurement events -/
  parityDetermines : ∀ (f : SpacetimeFault V E M) (D : Detector V E M),
    D ∈ DC.detectors →
    (D.isViolated (applyFaultToOutcomes' baseOutcomes f) ↔
     (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time)).card % 2 = 1)

/-- Under linearity conditions, syndrome respects multiplication (symmetric difference) -/
theorem syndrome_mul
    (hlin : SyndromeLinearCondition DC baseOutcomes)
    (f g : SpacetimeFault V E M) :
    syndrome DC baseOutcomes (f * g) = symmDiff (syndrome DC baseOutcomes f) (syndrome DC baseOutcomes g) := by
  ext D
  simp only [syndrome, Finset.mem_filter, Finset.mem_symmDiff]
  constructor
  · intro ⟨hD, hviol⟩
    rw [hlin.parityDetermines (f * g) D hD] at hviol
    rw [hlin.parityDetermines f D hD, hlin.parityDetermines g D hD]
    have h_xor : ∀ e ∈ D.measEvents,
      (f * g).timeErrors e.measurement e.time = xor (f.timeErrors e.measurement e.time) (g.timeErrors e.measurement e.time) := by
      intro e _
      simp [SpacetimeFault.mul_timeErrors]
    have h_symmDiff :
      D.measEvents.filter (fun e => (f * g).timeErrors e.measurement e.time) =
      symmDiff (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time))
               (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_symmDiff, h_xor]
      constructor
      · intro ⟨he, hxor⟩
        cases hf : f.timeErrors e.measurement e.time <;>
        cases hg : g.timeErrors e.measurement e.time <;>
        simp_all
      · intro hcase
        cases hcase with
        | inl hcase =>
          have hg_false : g.timeErrors e.measurement e.time = false := by
            by_contra hg_true
            have : g.timeErrors e.measurement e.time = true := Bool.eq_true_of_not_eq_false hg_true
            exact hcase.2 ⟨hcase.1.1, this⟩
          exact ⟨hcase.1.1, by simp [hcase.1.2, hg_false]⟩
        | inr hcase =>
          have hf_false : f.timeErrors e.measurement e.time = false := by
            by_contra hf_true
            have : f.timeErrors e.measurement e.time = true := Bool.eq_true_of_not_eq_false hf_true
            exact hcase.2 ⟨hcase.1.1, this⟩
          exact ⟨hcase.1.1, by simp [hf_false, hcase.1.2]⟩
    rw [h_symmDiff] at hviol
    have card_symmDiff_mod2 :
      (symmDiff (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time))
                (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time))).card % 2 =
      ((D.measEvents.filter (fun e => f.timeErrors e.measurement e.time)).card +
       (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time)).card) % 2 :=
      card_symmDiff_mod_two _ _
    rw [card_symmDiff_mod2] at hviol
    -- hviol : (f_card + g_card) % 2 = 1
    -- Goal: (hD ∧ f_parity=1) ∧ ¬(hD ∧ g_parity=1) ∨ (hD ∧ g_parity=1) ∧ ¬(hD ∧ f_parity=1)
    let f_card := (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time)).card
    let g_card := (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time)).card
    have h_sum : (f_card + g_card) % 2 = 1 := hviol
    -- Sum is odd means exactly one is odd
    have h_xor_parity : (f_card % 2 = 1 ∧ g_card % 2 = 0) ∨ (f_card % 2 = 0 ∧ g_card % 2 = 1) := by omega
    cases h_xor_parity with
    | inl hcase =>
      left
      refine ⟨⟨hD, hcase.1⟩, ?_⟩
      intro ⟨_, hg_odd⟩
      omega
    | inr hcase =>
      right
      refine ⟨⟨hD, hcase.2⟩, ?_⟩
      intro ⟨_, hf_odd⟩
      omega
  · intro h
    cases h with
    | inl h =>
      constructor
      · exact h.1.1
      · rw [hlin.parityDetermines (f * g) D h.1.1]
        rw [hlin.parityDetermines f D h.1.1] at h
        rw [hlin.parityDetermines g D h.1.1] at h
        have h_xor : ∀ e ∈ D.measEvents,
          (f * g).timeErrors e.measurement e.time =
            xor (f.timeErrors e.measurement e.time) (g.timeErrors e.measurement e.time) := by
          intro e _
          simp [SpacetimeFault.mul_timeErrors]
        have h_symmDiff :
          D.measEvents.filter (fun e => (f * g).timeErrors e.measurement e.time) =
          symmDiff (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time))
                   (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time)) := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_symmDiff, h_xor]
          constructor
          · intro ⟨he, hxor⟩
            cases hf : f.timeErrors e.measurement e.time <;>
            cases hg : g.timeErrors e.measurement e.time <;>
            simp_all
          · intro hh
            cases hh with
            | inl hh =>
              have hg_false : g.timeErrors e.measurement e.time = false := by
                by_contra hg_true
                push_neg at hg_true
                exact hh.2 ⟨hh.1.1, Bool.eq_true_of_not_eq_false hg_true⟩
              exact ⟨hh.1.1, by simp [hh.1.2, hg_false]⟩
            | inr hh =>
              have hf_false : f.timeErrors e.measurement e.time = false := by
                by_contra hf_true
                push_neg at hf_true
                exact hh.2 ⟨hh.1.1, Bool.eq_true_of_not_eq_false hf_true⟩
              exact ⟨hh.1.1, by simp [hf_false, hh.1.2]⟩
        rw [h_symmDiff]
        have card_symmDiff_mod2 :
          (symmDiff (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time))
                    (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time))).card % 2 =
          ((D.measEvents.filter (fun e => f.timeErrors e.measurement e.time)).card +
           (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time)).card) % 2 :=
          card_symmDiff_mod_two _ _
        rw [card_symmDiff_mod2]
        have hf_viol := h.1.2
        have hg_sat : ¬(D.measEvents.filter fun e => g.timeErrors e.measurement e.time).card % 2 = 1 := by
          intro hcontra
          exact h.2 ⟨h.1.1, hcontra⟩
        omega
    | inr h =>
      constructor
      · exact h.1.1
      · rw [hlin.parityDetermines (f * g) D h.1.1]
        rw [hlin.parityDetermines f D h.1.1] at h
        rw [hlin.parityDetermines g D h.1.1] at h
        have h_xor : ∀ e ∈ D.measEvents,
          (f * g).timeErrors e.measurement e.time =
            xor (f.timeErrors e.measurement e.time) (g.timeErrors e.measurement e.time) := by
          intro e _
          simp [SpacetimeFault.mul_timeErrors]
        have h_symmDiff :
          D.measEvents.filter (fun e => (f * g).timeErrors e.measurement e.time) =
          symmDiff (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time))
                   (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time)) := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_symmDiff, h_xor]
          constructor
          · intro ⟨he, hxor⟩
            cases hf : f.timeErrors e.measurement e.time <;>
            cases hg : g.timeErrors e.measurement e.time <;>
            simp_all
          · intro hh
            cases hh with
            | inl hh =>
              have hg_false : g.timeErrors e.measurement e.time = false := by
                by_contra hg_true
                push_neg at hg_true
                exact hh.2 ⟨hh.1.1, Bool.eq_true_of_not_eq_false hg_true⟩
              exact ⟨hh.1.1, by simp [hh.1.2, hg_false]⟩
            | inr hh =>
              have hf_false : f.timeErrors e.measurement e.time = false := by
                by_contra hf_true
                push_neg at hf_true
                exact hh.2 ⟨hh.1.1, Bool.eq_true_of_not_eq_false hf_true⟩
              exact ⟨hh.1.1, by simp [hf_false, hh.1.2]⟩
        rw [h_symmDiff]
        have card_symmDiff_mod2 :
          (symmDiff (D.measEvents.filter (fun e => f.timeErrors e.measurement e.time))
                    (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time))).card % 2 =
          ((D.measEvents.filter (fun e => f.timeErrors e.measurement e.time)).card +
           (D.measEvents.filter (fun e => g.timeErrors e.measurement e.time)).card) % 2 :=
          card_symmDiff_mod_two _ _
        rw [card_symmDiff_mod2]
        have hf_sat : ¬(D.measEvents.filter fun e => f.timeErrors e.measurement e.time).card % 2 = 1 := by
          intro hcontra
          exact h.2 ⟨h.1.1, hcontra⟩
        have hg_viol := h.1.2
        omega

/-- Syndrome of inverse equals syndrome of original (since XOR is self-inverse) -/
theorem syndrome_inv
    (hlin : SyndromeLinearCondition DC baseOutcomes)
    (f : SpacetimeFault V E M) :
    syndrome DC baseOutcomes f⁻¹ = syndrome DC baseOutcomes f := by
  ext D
  simp only [syndrome, Finset.mem_filter]
  constructor
  · intro ⟨hD, hviol⟩
    refine ⟨hD, ?_⟩
    rw [hlin.parityDetermines f⁻¹ D hD] at hviol
    rw [hlin.parityDetermines f D hD]
    convert hviol using 2
  · intro ⟨hD, hviol⟩
    refine ⟨hD, ?_⟩
    rw [hlin.parityDetermines f D hD] at hviol
    rw [hlin.parityDetermines f⁻¹ D hD]
    convert hviol using 2

end Linearity

/-! ## Spacetime Stabilizers and Logical Faults

Based on the syndrome definition, we can characterize:
- Spacetime stabilizers: trivial faults with empty syndrome
- Logical faults: non-trivial faults with empty syndrome -/

/-- A spacetime stabilizer has empty syndrome by definition -/
def IsSpacetimeStabilizer'
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (isTrivial : SpacetimeFault V E M → Prop)
    (fault : SpacetimeFault V E M) : Prop :=
  hasEmptySyndrome' DC baseOutcomes fault ∧ isTrivial fault

/-- A logical fault is non-trivial with empty syndrome -/
def IsLogicalFault
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (isTrivial : SpacetimeFault V E M → Prop)
    (fault : SpacetimeFault V E M) : Prop :=
  hasEmptySyndrome' DC baseOutcomes fault ∧ ¬isTrivial fault

/-- Stabilizers and logical faults partition empty-syndrome faults -/
theorem emptySyndrome_dichotomy
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (isTrivial : SpacetimeFault V E M → Prop)
    (fault : SpacetimeFault V E M)
    (h_empty : hasEmptySyndrome' DC baseOutcomes fault) :
    IsSpacetimeStabilizer' DC baseOutcomes isTrivial fault ∨
    IsLogicalFault DC baseOutcomes isTrivial fault := by
  by_cases htrivial : isTrivial fault
  · left; exact ⟨h_empty, htrivial⟩
  · right; exact ⟨h_empty, htrivial⟩

/-- Stabilizers and logical faults are mutually exclusive -/
theorem stabilizer_logicalFault_exclusive
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (isTrivial : SpacetimeFault V E M → Prop)
    (fault : SpacetimeFault V E M) :
    ¬(IsSpacetimeStabilizer' DC baseOutcomes isTrivial fault ∧
      IsLogicalFault DC baseOutcomes isTrivial fault) := by
  intro ⟨hstab, hlog⟩
  exact hlog.2 hstab.2

/-- A logical fault is characterized as non-trivial with empty syndrome -/
theorem isLogicalFault_iff
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (isTrivial : SpacetimeFault V E M → Prop)
    (fault : SpacetimeFault V E M) :
    IsLogicalFault DC baseOutcomes isTrivial fault ↔
    (hasEmptySyndrome' DC baseOutcomes fault ∧ ¬isTrivial fault) :=
  Iff.rfl

/-! ## Syndrome Membership Characterization -/

/-- A detector is in the syndrome iff it is violated by the fault -/
theorem mem_syndrome_iff
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M)
    (D : Detector V E M)
    (hD : D ∈ DC.detectors) :
    D ∈ syndrome DC baseOutcomes fault ↔
    D.isViolated (applyFaultToOutcomes' baseOutcomes fault) := by
  simp only [syndrome, Finset.mem_filter, hD, true_and]

/-- Syndrome is a subset of the detector collection -/
theorem syndrome_subset
    (DC : DetectorCollection V E M)
    (baseOutcomes : OutcomeAssignment M)
    (fault : SpacetimeFault V E M) :
    syndrome DC baseOutcomes fault ⊆ DC.detectors := by
  intro D hD
  simp only [syndrome, Finset.mem_filter] at hD
  exact hD.1

/-! ## Summary

This formalization captures the syndrome concept from fault-tolerant quantum error correction:

1. **Syndrome Definition**: The syndrome of a fault F is the set of detectors violated by F.
   Equivalently, it's a binary vector where entry D is 1 iff detector D is violated.

2. **Z₂-Linearity**: Under appropriate conditions, the syndrome function satisfies:
   - syndrome(F₁ · F₂) = syndrome(F₁) + syndrome(F₂) (symmetric difference)
   - syndrome(F⁻¹) = syndrome(F)
   - syndrome(1) = ∅

3. **Partition of Empty-Syndrome Faults**:
   - Spacetime stabilizers: trivial faults with empty syndrome
   - Logical faults: non-trivial faults with empty syndrome
   - These are mutually exclusive and exhaustive

Key properties proven:
- Syndrome addition (symmetric difference) is commutative, associative, has identity
- Every syndrome is self-inverse
- Identity fault has empty syndrome
- Syndrome respects fault composition (Z₂-linear)
- Empty-syndrome faults partition into stabilizers and logical faults
-/
