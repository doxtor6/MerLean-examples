import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_10_FaultTolerantGaugingProcedure
import QEC1.Definitions.Def_11_SpacetimeLogicalFault
import QEC1.Definitions.Def_12_SpacetimeFaultDistance
import QEC1.Lemmas.Lem_1_DeformedCodeChecks
import QEC1.Lemmas.Lem_4_SpacetimeCodeDetectors
import QEC1.Lemmas.Lem_5_SpacetimeStabilizers
import QEC1.Lemmas.Lem_6_TimeFaultDistance
import Mathlib.Tactic

/-!
# Lemma 7: Space-Time Decoupling

## Statement
Any spacetime logical fault (Def_11) is equivalent, up to multiplication by spacetime
stabilizers (Def_11), to the product of a space-only logical fault and a time-only logical fault.

Formally: Let F be a spacetime logical fault in the fault-tolerant gauging measurement
procedure (Def_10). Then there exist:
- A space logical fault F_S: a spacetime fault consisting solely of Pauli errors at
  time t_i, such that F_S is a logical operator of the deformed code (Def_4).
- A time logical fault F_T: a spacetime fault consisting solely of time-faults
  (measurement/initialization errors), with no Pauli errors.
- A spacetime stabilizer S (Def_11).

such that F = F_S · F_T · S (composition via symmetric difference of fault sets).

## Main Results
- `FullOutcomePreserving`: The full outcome predicate (sign + code state)
- `IsSpaceLogicalFault`: A space-only fault at t_i that is a logical of the deformed code
- `IsTimeLogicalFault`: A pure-time fault that flips the gauging sign
- `spaceTime_decomposition`: The main decomposition theorem F = F_S · F_T · S
- `space_time_independent_effects`: F_S and F_T affect different aspects of the outcome

## Proof Outline
1. Move all space-faults to time t_i using time-propagating stabilizers (Lem 5)
2. Convert boundary init/readout faults to space-faults at t_i using Lem 5 generators
3. Separate the remaining time-faults into A_v strings (logical) or stabilizer generators
4. Verify independence: space affects code state, time affects measurement sign
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset PauliOp GaussFlux DeformedCode DeformedOperator
open FaultTolerantGaugingProcedure SpacetimeLogicalFault SpacetimeStabilizers
open SpacetimeFaultDistance TimeFaultDistance
open scoped symmDiff

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  {cycles : C → Set G.edgeSet} [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  {checks : J → PauliOp V}

namespace SpaceTimeDecoupling

variable (proc : FaultTolerantGaugingProcedure G cycles checks)

/-! ## Part I: Full Outcome Predicate

The paper's Def_11 says a spacetime logical fault "changes the outcome" in EITHER of two ways:
1. Flipping the inferred measurement sign σ (time-type logical), OR
2. Applying a nontrivial logical operator to the post-measurement code state (space-type logical).

A fault is outcome-preserving if NEITHER occurs: the sign is preserved AND the
net Pauli error at t_i is in the deformed stabilizer group (not a nontrivial logical). -/

/-- The deformed stabilizer code at the gauging time, constructed from proc's data. -/
noncomputable def theDeformedCode :=
  DeformedCodeChecks.deformedStabilizerCode G cycles checks proc.deformedData
    proc.cycleParity proc.checks_commute

/-- The full outcome-preserving predicate for the fault-tolerant gauging procedure.
    A fault preserves the outcome if BOTH:
    (1) The gauging sign σ is preserved (no time-logical effect), AND
    (2) The net Pauli error at t_i is in the deformed stabilizer group (no space-logical effect).

    This captures the paper's Def_11: a spacetime stabilizer leaves both the classical
    measurement record and the quantum code state unchanged. -/
def FullOutcomePreserving
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  PreservesGaugingSign proc F ∧
  F.pauliErrorAt proc.phase2Start ∈ (theDeformedCode proc).stabilizerGroup

/-- A spacetime logical fault under the full outcome predicate:
    syndrome-free AND changes the outcome (either flips sign or applies nontrivial logical). -/
abbrev IsFullGaugingLogicalFault
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  IsGaugingLogicalFault proc proc.detectorOfIndex (FullOutcomePreserving proc) F

/-- A spacetime stabilizer under the full outcome predicate:
    syndrome-free AND preserves both the sign and code state. -/
abbrev IsFullGaugingStabilizer
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  IsGaugingStabilizer proc proc.detectorOfIndex (FullOutcomePreserving proc) F

/-- A logical fault changes the outcome: ¬(sign preserved ∧ Pauli in stabilizer group).
    Equivalently: either the sign is flipped, or the Pauli error is a nontrivial logical. -/
theorem logicalFault_outcome_change
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hlog : IsFullGaugingLogicalFault proc F) :
    FlipsGaugingSign proc F ∨
    F.pauliErrorAt proc.phase2Start ∉ (theDeformedCode proc).stabilizerGroup := by
  have hnotpres := hlog.2
  rw [FullOutcomePreserving] at hnotpres
  push_neg at hnotpres
  rcases flipsOrPreserves proc F with hflip | hpres
  · left; exact hflip
  · right; exact hnotpres hpres

/-! ## Part II: Space-Only and Time-Only Fault Definitions -/

/-- A space-only logical fault: all space-faults are concentrated at t_i, no time-faults,
    and the composite Pauli error at t_i is a nontrivial logical of the deformed code. -/
def IsSpaceLogicalFault
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  F.isPureSpace ∧
  (∀ t, t ≠ proc.phase2Start → F.spaceFaultsAt t = ∅) ∧
  (theDeformedCode proc).isLogicalOp (F.pauliErrorAt proc.phase2Start)

/-- A time-only logical fault: no space-faults, syndrome-free, and flips the gauging sign σ. -/
def IsTimeLogicalFault
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  F.isPureTime ∧
  IsSyndromeFreeGauging proc proc.detectorOfIndex F ∧
  FlipsGaugingSign proc F

/-! ## Part III: Z₂ Algebra of Symmetric Differences

The key algebraic fact: sums of ZMod 2 indicators over symmetric differences decompose
additively. This underlies all composition properties of the gauging procedure. -/

/-- Core Z₂ algebra: sums over symmetric differences decompose additively.
    This uses the inclusion-exclusion decomposition S ∆ T = (S \ T) ∪ (T \ S)
    and the fact that the intersection terms cancel in characteristic 2. -/
private theorem zmod2_sum_finset_symmDiff {α : Type*} [DecidableEq α]
    (S T : Finset α) (g : α → ZMod 2) :
    (∑ a ∈ S ∆ T, g a) = (∑ a ∈ S, g a) + (∑ a ∈ T, g a) := by
  rw [symmDiff_def, Finset.sup_eq_union, Finset.sum_union disjoint_sdiff_sdiff]
  conv_rhs =>
    rw [show ∑ a ∈ S, g a = ∑ a ∈ S \ T, g a + ∑ a ∈ S ∩ T, g a from by
          rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S T)]
          congr 1; exact (Finset.sdiff_union_inter S T).symm]
    rw [show ∑ a ∈ T, g a = ∑ a ∈ T \ S, g a + ∑ a ∈ T ∩ S, g a from by
          rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T S)]
          congr 1; exact (Finset.sdiff_union_inter T S).symm]
  rw [show ∑ a ∈ S ∩ T, g a = ∑ a ∈ T ∩ S, g a from by
    congr 1; exact Finset.inter_comm S T]
  set a := ∑ x ∈ S \ T, g x
  set b := ∑ x ∈ T \ S, g x
  set c := ∑ x ∈ T ∩ S, g x
  have hcc : c + c = 0 := CharTwo.add_self_eq_zero _
  have : (a + c) + (b + c) = a + b + (c + c) := by ring
  rw [this, hcc, add_zero]

/-- Z₂ indicator sums over an index set decompose additively for symmDiff.
    For any function g : β → α mapping indices to elements, the indicator sum
    ∑ b, [g b ∈ S ∆ T] = (∑ b, [g b ∈ S]) + (∑ b, [g b ∈ T]) in ZMod 2. -/
private theorem zmod2_sum_indicator_symmDiff {α β : Type*} [DecidableEq α]
    (S T : Finset α) (U : Finset β) (g : β → α) :
    (∑ b ∈ U, if g b ∈ S ∆ T then (1 : ZMod 2) else 0) =
    (∑ b ∈ U, if g b ∈ S then 1 else 0) + (∑ b ∈ U, if g b ∈ T then 1 else 0) := by
  rw [← Finset.sum_add_distrib]
  congr 1; ext b
  simp only [Finset.mem_symmDiff]
  by_cases hS : g b ∈ S <;> by_cases hT : g b ∈ T <;> simp_all [CharTwo.add_self_eq_zero]

/-- Filter distributes over symmetric difference. -/
private theorem filter_symmDiff_eq {α : Type*} [DecidableEq α]
    (S T : Finset α) (p : α → Prop) [DecidablePred p] :
    (S ∆ T).filter p = (S.filter p) ∆ (T.filter p) := by
  ext a; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto

/-! ## Part III-A: Composition Properties — gaussSignFlip

The gaussSignFlip is a double sum of ZMod 2 indicators over timeFaults.
Since composition takes the symmetric difference of timeFaults, the Z₂ additivity
of indicators gives additivity of gaussSignFlip. -/

/-- The gaussSignFlip is Z₂-additive under composition:
    sign(F₁ · F₂) = sign(F₁) + sign(F₂) in ZMod 2.
    This follows from the fact that timeFaults of the composition is the
    symmetric difference, and the indicator function is additive over Z₂. -/
theorem gaussSignFlip_compose_additive
    (F₁ F₂ : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) :
    gaussSignFlip proc (F₁.compose F₂) = gaussSignFlip proc F₁ + gaussSignFlip proc F₂ := by
  simp only [gaussSignFlip, SpacetimeFault.compose]
  rw [← Finset.sum_add_distrib]
  congr 1; ext v
  exact zmod2_sum_indicator_symmDiff F₁.timeFaults F₂.timeFaults _ _

/-! ## Part III-B: Composition Properties — pauliErrorAt

The Pauli error at time t is defined via sums over spaceFaultsAt t.
Since composition takes the symmetric difference of spaceFaults, and filter
distributes over symmDiff, the Z₂ sum additivity gives multiplicativity of PauliOp. -/

/-- The net Pauli error at t is multiplicative under composition:
    pauliErrorAt(F₁ · F₂, t) = pauliErrorAt(F₁, t) * pauliErrorAt(F₂, t).
    This follows because spaceFaults of the composition is the symmetric difference,
    filter distributes over symmDiff, and Z₂ sums are additive = Pauli product. -/
theorem pauliErrorAt_compose_mul
    (F₁ F₂ : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) (t : ℕ) :
    (F₁.compose F₂).pauliErrorAt t = F₁.pauliErrorAt t * F₂.pauliErrorAt t := by
  ext q
  · -- xVec component
    simp only [PauliOp.mul_xVec, Pi.add_apply]
    simp only [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt,
      SpacetimeFault.compose]
    rw [filter_symmDiff_eq]
    exact zmod2_sum_finset_symmDiff _ _
      (fun (f : SpaceFault (ExtQubit G) ℕ) => if f.qubit = q then f.xComponent else 0)
  · -- zVec component
    simp only [PauliOp.mul_zVec, Pi.add_apply]
    simp only [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt,
      SpacetimeFault.compose]
    rw [filter_symmDiff_eq]
    exact zmod2_sum_finset_symmDiff _ _
      (fun (f : SpaceFault (ExtQubit G) ℕ) => if f.qubit = q then f.zComponent else 0)

/-! ## Part III-C: Composition Properties — Syndrome-Freeness

Detector violation depends on flipParity, which is a ZMod 2 sum of indicators
over timeFaults. By the same Z₂ additivity, composing two syndrome-free faults
preserves syndrome-freeness. -/

/-- flipParity is Z₂-additive under symmetric difference of fault sets. -/
private theorem flipParity_symmDiff
    (D : Detector proc.MeasLabel)
    (faults₁ faults₂ : Finset (TimeFault proc.MeasLabel)) :
    D.flipParity (faults₁ ∆ faults₂) = D.flipParity faults₁ + D.flipParity faults₂ := by
  simp only [Detector.flipParity]
  exact zmod2_sum_indicator_symmDiff faults₁ faults₂ _ _

/-- Composing two syndrome-free faults preserves syndrome-freeness.
    Both faults have empty syndrome, so the composed fault (symmetric difference
    of timeFaults) also has empty syndrome by Z₂ additivity of flipParity. -/
theorem compose_syndromeFree_syndromeFree
    (F S : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hF : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hS : IsSyndromeFreeGauging proc proc.detectorOfIndex S) :
    IsSyndromeFreeGauging proc proc.detectorOfIndex (F.compose S) := by
  intro idx
  rw [Detector.isViolated_iff_flipParity]
  simp only [SpacetimeFault.compose]
  rw [flipParity_symmDiff]
  have hF_free : ¬(proc.detectorOfIndex idx).isViolated F.timeFaults := hF idx
  have hS_free : ¬(proc.detectorOfIndex idx).isViolated S.timeFaults := hS idx
  rw [Detector.isViolated_iff_flipParity] at hF_free hS_free
  push_neg at hF_free hS_free
  have zmod2_ne1 : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide +revert
  have hF0 : (proc.detectorOfIndex idx).flipParity F.timeFaults = 0 :=
    zmod2_ne1 _ hF_free
  have hS0 : (proc.detectorOfIndex idx).flipParity S.timeFaults = 0 :=
    zmod2_ne1 _ hS_free
  rw [hF0, hS0, add_zero]
  exact zero_ne_one

/-- Composing with a full stabilizer preserves syndrome-freeness. -/
theorem compose_preserves_syndromeFree
    (F S : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hF : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hS : IsFullGaugingStabilizer proc S) :
    IsSyndromeFreeGauging proc proc.detectorOfIndex (F.compose S) :=
  compose_syndromeFree_syndromeFree proc F S hF hS.1

/-! ## Part III-D: Composition Properties — Full Stabilizer Closure

Combining the above: the composition of two full stabilizers is a full stabilizer.
Syndrome-freeness, sign preservation, and stabilizer group membership all transfer. -/

/-- The composition of two full gauging stabilizers is a full gauging stabilizer.
    Syndrome-freeness and outcome preservation are both additive over Z₂. -/
theorem compose_fullGaugingStabilizer
    (F₁ F₂ : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (h₁ : IsFullGaugingStabilizer proc F₁)
    (h₂ : IsFullGaugingStabilizer proc F₂) :
    IsFullGaugingStabilizer proc (F₁.compose F₂) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Syndrome-free: follows from compose_preserves_syndromeFree
    exact compose_preserves_syndromeFree proc F₁ F₂ h₁.1 ⟨h₂.1, h₂.2⟩
  · -- Preserves sign: gaussSignFlip(F₁ · F₂) = sign(F₁) + sign(F₂) = 0 + 0 = 0
    rw [PreservesGaugingSign, gaussSignFlip_compose_additive]
    have h1sign : PreservesGaugingSign proc F₁ := h₁.2.1
    have h2sign : PreservesGaugingSign proc F₂ := h₂.2.1
    rw [h1sign, h2sign, add_zero]
  · -- Pauli in stabilizer group: product of stabilizer elements is in the group
    rw [pauliErrorAt_compose_mul]
    exact (theDeformedCode proc).stabilizerGroup.mul_mem h₁.2.2 h₂.2.2

/-! ## Part IV: Time-Propagating Stabilizers Move Space-Faults

The time-propagating generators from Lem_5 allow moving a Pauli error from time t
to time t+1 (or t-1). By composing these, we can move any space-fault to the
gauging time t_i = phase2Start. -/

/-! ### The Empty Fault is a Full Gauging Stabilizer

The empty fault (no space-faults, no time-faults) trivially satisfies all stabilizer
conditions: empty syndrome, zero sign flip, and the identity Pauli is in the stabilizer group. -/

/-- The empty fault is a full gauging stabilizer. -/
theorem empty_isFullGaugingStabilizer :
    IsFullGaugingStabilizer proc SpacetimeFault.empty := by
  refine ⟨?_, ?_, ?_⟩
  · -- Syndrome-free: no time-faults means no detector violations
    intro idx
    exact Detector.not_isViolated_no_faults _
  · -- Preserves sign: no time-faults means zero gaussSignFlip
    rw [PreservesGaugingSign, gaussSignFlip]
    simp [SpacetimeFault.empty]
  · -- Pauli error is 1, which is in the stabilizer group
    rw [SpacetimeFault.pauliErrorAt_empty]
    exact (theDeformedCode proc).stabilizerGroup.one_mem

/-- Boundary faults can be absorbed: if space-faults are already concentrated at t_i,
    the empty fault serves as a trivial stabilizer preserving this property.
    Steps 1 and 4 of the paper are subsumed by `space_fault_cleaning` (Lem 5),
    which handles both time-propagation and boundary absorption in one step. -/
theorem boundary_faults_trivially_absorbed
    (F' : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (_hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F')
    (hconc : ∀ t, t ≠ proc.phase2Start → F'.spaceFaultsAt t = ∅) :
    ∃ S₂ : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel,
      IsFullGaugingStabilizer proc S₂ ∧
      (∀ t, t ≠ proc.phase2Start → (F'.compose S₂).spaceFaultsAt t = ∅) := by
  refine ⟨SpacetimeFault.empty, empty_isFullGaugingStabilizer proc, ?_⟩
  intro t ht
  rw [SpacetimeFault.compose_empty_right]
  exact hconc t ht

/-! ### Space-Fault Cleaning and Centralizer Membership

Using the space_fault_cleaning and syndromeFree_pureSpace_inCentralizer axioms from Lem 5,
we prove the two key constructive lemmas needed for the main decomposition:
1. Any syndrome-free fault can be cleaned to have space-faults only at t_i
2. A pure-space fault concentrated at t_i has its Pauli error in the centralizer -/

/-- **Space-fault cleaning (Steps 1+4):** Any syndrome-free spacetime fault can be
    composed with a full gauging stabilizer to concentrate all space-faults at t_i.
    This uses the time-propagating and boundary generators from Lem 5. -/
theorem space_fault_cleaning_fullStabilizer
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F) :
    ∃ S₁ : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel,
      IsFullGaugingStabilizer proc S₁ ∧
      ∀ t, t ≠ proc.phase2Start → (F.compose S₁).spaceFaultsAt t = ∅ := by
  obtain ⟨S₁, hS₁_free, hS₁_sign, hS₁_pauli, hS₁_clean⟩ :=
    space_fault_cleaning proc F hfree
  exact ⟨S₁, ⟨hS₁_free, hS₁_sign, hS₁_pauli⟩, hS₁_clean⟩

/-- **Centralizer membership (Step 3):** A syndrome-free pure-space fault concentrated
    at t_i has its Pauli error in the centralizer of the deformed code.
    This encodes the quantum-mechanical fact that the deformed code checks are
    the active checks at t_i, and the cleaning process preserves commutation. -/
theorem centralizer_of_syndromeFree_pureSpace
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hconc : ∀ t, t ≠ proc.phase2Start → F.spaceFaultsAt t = ∅)
    (hpure : F.isPureSpace) :
    (theDeformedCode proc).inCentralizer (F.pauliErrorAt proc.phase2Start) :=
  syndromeFree_pureSpace_inCentralizer proc F hfree hconc hpure

/-! ## Part V: Time-Fault Classification

After cleaning, the time-faults form a pure-time fault. By Lem 6, syndrome-free
pure-time faults either flip σ (logical time-fault = A_v string) or decompose
into stabilizer generators (trivial). -/

/-- The cleaned time-faults of a syndrome-free fault either flip the sign or are stabilizers.
    This is the content of Lem 6's `pureTime_syndromeFree_logical_or_stabilizer_generators`. -/
theorem time_faults_dichotomy
    (F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : IsPureTimeFault proc F_T)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F_T) :
    FlipsGaugingSign proc F_T ∨
    IsGaugingStabilizer proc proc.detectorOfIndex (PreservesGaugingSign proc) F_T :=
  (pureTime_syndromeFree_logical_or_stabilizer_generators proc F_T hpure hfree).elim
    (fun h => Or.inl h)
    (fun ⟨hpres, _⟩ => Or.inr ⟨hfree, hpres⟩)

/-! ## Part VI: Independence of Space and Time Effects

The space fault F_S and time fault F_T affect the procedure outcome independently:
- F_S acts on the code Hilbert space (applies a Pauli logical operator)
- F_T acts on the classical measurement record (flips σ) -/

/-- The gauging sign depends only on time-faults (measurement errors on Gauss checks).
    Space-faults do not affect the gauging sign directly. -/
theorem gaussSignFlip_depends_only_on_timeFaults
    (F₁ F₂ : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (heq : F₁.timeFaults = F₂.timeFaults) :
    gaussSignFlip proc F₁ = gaussSignFlip proc F₂ := by
  simp only [gaussSignFlip]
  congr 1
  ext v
  congr 1
  ext r
  simp only [heq]

/-- A pure-space fault preserves the gauging sign. -/
theorem pureSpace_preservesSign
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureSpace) :
    PreservesGaugingSign proc F := by
  rw [PreservesGaugingSign, gaussSignFlip]
  rw [SpacetimeFault.isPureSpace] at hpure
  simp only [hpure, Finset.notMem_empty, ↓reduceIte, Finset.sum_const_zero]

/-- The Pauli error at any time depends only on space-faults.
    Two faults with the same spaceFaults have the same pauliErrorAt. -/
theorem pauliErrorAt_depends_only_on_spaceFaults
    (F₁ F₂ : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (heq : F₁.spaceFaults = F₂.spaceFaults) (t : ℕ) :
    F₁.pauliErrorAt t = F₂.pauliErrorAt t := by
  ext q
  · simp [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt, heq]
  · simp [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt, heq]

/-- A pure-time fault does not change the Pauli error at any time. -/
theorem pureTime_pauliError_trivial
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureTime) (t : ℕ) :
    F.pauliErrorAt t = 1 := by
  rw [SpacetimeFault.isPureTime] at hpure
  ext q
  · simp only [one_xVec, Pi.zero_apply]
    simp only [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt, hpure,
      Finset.filter_empty, Finset.sum_empty]
  · simp only [one_zVec, Pi.zero_apply]
    simp only [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt, hpure,
      Finset.filter_empty, Finset.sum_empty]

/-- **Independence theorem:** The space and time components of a fault affect
    different aspects of the procedure outcome.
    - The gauging sign σ depends only on time-faults (measurement errors).
    - The Pauli error on the code state depends only on space-faults.
    Therefore F_S and F_T have independent effects. -/
theorem space_time_independent_effects
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) :
    gaussSignFlip proc F = gaussSignFlip proc F.timeComponent ∧
    (∀ t, F.pauliErrorAt t = F.spaceComponent.pauliErrorAt t) := by
  constructor
  · apply gaussSignFlip_depends_only_on_timeFaults
    simp [SpacetimeFault.timeComponent]
  · intro t
    apply pauliErrorAt_depends_only_on_spaceFaults
    simp [SpacetimeFault.spaceComponent]

/-- The sign flip of F_S · F_T equals the sign flip of F_T when F_S is pure-space. -/
theorem gaussSignFlip_compose_pureSpace
    (F_S F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpS : F_S.isPureSpace) :
    gaussSignFlip proc (F_S.compose F_T) = gaussSignFlip proc F_T := by
  apply gaussSignFlip_depends_only_on_timeFaults
  simp [SpacetimeFault.compose]
  rw [SpacetimeFault.isPureSpace] at hpS
  simp [hpS]

/-! ## Part VII: Main Decomposition Theorem

The central result: any spacetime logical fault decomposes as F = F_S · F_T · S. -/

/-- **Lemma 7 (Space-Time Decoupling): Main Theorem.**

Any spacetime logical fault F in the fault-tolerant gauging measurement procedure
is equivalent, up to multiplication by spacetime stabilizers, to the product of a
space-only fault F_S and a time-only fault F_T.

Specifically: there exist F_S, F_T, and S such that:
- F = F_S · F_T · S (composition via symmetric difference)
- F_S is pure-space (no time-faults) and concentrated at time t_i
- F_T is pure-time (no space-faults) and syndrome-free
- S is a full gauging stabilizer (syndrome-free, outcome-preserving)
- If F_T is nontrivial, it flips the gauging sign σ (time-logical)
- If F_S is nontrivial, its Pauli error at t_i is a nontrivial deformed-code logical

The proof proceeds by:
1. Move all space-faults to t_i using time-propagating stabilizers (Lem 5)
2. Convert boundary init/readout faults to space-faults at t_i (Lem 5 generators)
3. Separate the cleaned fault into space and time parts
4. Classify the time part via Lem 6's dichotomy -/
theorem spaceTime_decomposition
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hlog : IsFullGaugingLogicalFault proc F) :
    ∃ (F_S F_T S : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel),
      -- F = F_S · F_T · S
      F = (F_S.compose F_T).compose S ∧
      -- F_S is pure-space and concentrated at t_i
      F_S.isPureSpace ∧
      (∀ t, t ≠ proc.phase2Start → F_S.spaceFaultsAt t = ∅) ∧
      -- F_T is pure-time and syndrome-free
      F_T.isPureTime ∧
      IsSyndromeFreeGauging proc proc.detectorOfIndex F_T ∧
      -- S is a full gauging stabilizer
      IsFullGaugingStabilizer proc S ∧
      -- At least one of F_S, F_T is nontrivial (F is a logical fault)
      (FlipsGaugingSign proc F_T ∨
       (theDeformedCode proc).isLogicalOp (F_S.pauliErrorAt proc.phase2Start)) := by
  -- Step 1: Clean space-faults to t_i using time-propagating stabilizers (Lem 5)
  obtain ⟨S₁, hS₁_stab, hS₁_clean⟩ :=
    space_fault_cleaning_fullStabilizer proc F hlog.1
  -- The cleaned fault F' = F · S₁ has space-faults only at t_i
  set F' := F.compose S₁
  have hF'_free : IsSyndromeFreeGauging proc proc.detectorOfIndex F' :=
    compose_preserves_syndromeFree proc F S₁ hlog.1 hS₁_stab
  -- Step 2: Absorb boundary faults — trivially satisfied since space_fault_cleaning
  -- already concentrates space-faults at t_i (the empty stabilizer preserves this)
  obtain ⟨S₂, hS₂_stab, hS₂_conc⟩ :=
    boundary_faults_trivially_absorbed proc F' hF'_free hS₁_clean
  set F'' := F'.compose S₂
  have hF''_free : IsSyndromeFreeGauging proc proc.detectorOfIndex F'' :=
    compose_preserves_syndromeFree proc F' S₂ hF'_free hS₂_stab
  -- Step 3: Decompose F'' into space and time components
  let F_S := F''.spaceComponent
  let F_T := F''.timeComponent
  let S := S₁.compose S₂
  -- S is a stabilizer (composition of stabilizers)
  have hS_stab : IsFullGaugingStabilizer proc S :=
    compose_fullGaugingStabilizer proc S₁ S₂ hS₁_stab hS₂_stab
  refine ⟨F_S, F_T, S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- F = (F_S · F_T) · S
    -- We have F'' = F_S · F_T (decompose_space_time)
    -- and F'' = F · S₁ · S₂ = F · (S₁ · S₂) = F · S
    -- so F = F'' · S (since compose is involutive: F · S · S = F)
    -- Hence F = (F_S · F_T) · S
    have hdecomp : F'' = F_S.compose F_T := by
      exact (SpacetimeFault.decompose_space_time F'').symm
    have hF''_eq : F'' = F.compose S := by
      simp only [F'', F', S, SpacetimeFault.compose_assoc]
    rw [← hdecomp, hF''_eq]
    simp only [SpacetimeFault.compose_assoc, SpacetimeFault.compose_self,
      SpacetimeFault.compose_empty_right]
  · -- F_S is pure-space
    exact F''.spaceComponent_isPureSpace
  · -- F_S has space-faults only at t_i
    intro t ht
    -- F_S.spaceFaultsAt t = F''.spaceFaultsAt t (since spaceComponent preserves spaceFaults)
    simp only [F_S, SpacetimeFault.spaceComponent, SpacetimeFault.spaceFaultsAt]
    -- F'' = F' · S₂, and both have space-faults only at t_i after cleaning
    exact hS₂_conc t ht
  · -- F_T is pure-time
    exact F''.timeComponent_isPureTime
  · -- F_T is syndrome-free: F_T.timeFaults = F''.timeFaults, so same violations
    intro idx
    -- F_T.timeFaults = F''.timeFaults by definition of timeComponent
    exact hF''_free idx
  · -- S is a full gauging stabilizer
    exact hS_stab
  · -- Nontriviality: F is a logical fault, so its outcome changes.
    -- ¬FullOutcomePreserving proc F means either sign is flipped or Pauli is nontrivial.
    have hnotpres := hlog.2
    rw [FullOutcomePreserving] at hnotpres
    push_neg at hnotpres
    -- The sign of F equals the sign of F_T (space-faults don't affect sign)
    -- The Pauli error of F at t_i relates to F_S (time-faults don't affect Pauli)
    rcases flipsOrPreserves proc F with hflip | hpres
    · -- F flips the sign, so F_T flips the sign
      left
      rw [FlipsGaugingSign] at hflip ⊢
      -- gaussSignFlip depends only on timeFaults
      -- F_T.timeFaults = F''.timeFaults = (F · S).timeFaults
      -- S is a stabilizer that preserves sign, so sign(F · S) relates to sign(F)
      -- Actually: F_T has same timeFaults as F'', and sign depends only on timeFaults
      -- gaussSignFlip(F_T) = gaussSignFlip(F'') since F_T.timeFaults = F''.timeFaults
      have htf_eq : F_T.timeFaults = F''.timeFaults := by
        simp only [F_T, SpacetimeFault.timeComponent]
      have hFT_eq : gaussSignFlip proc F_T = gaussSignFlip proc F'' :=
        gaussSignFlip_depends_only_on_timeFaults proc F_T F'' htf_eq
      rw [hFT_eq]
      -- gaussSignFlip(F'') = gaussSignFlip(F · S₁ · S₂) = sign(F) + sign(S₁) + sign(S₂)
      -- Since S₁, S₂ preserve sign (sign = 0), this equals sign(F) = 1
      have hpres1 : PreservesGaugingSign proc S₁ := hS₁_stab.2.1
      have hpres2 : PreservesGaugingSign proc S₂ := hS₂_stab.2.1
      -- F'' = (F · S₁) · S₂
      have : gaussSignFlip proc F'' =
          gaussSignFlip proc F' + gaussSignFlip proc S₂ :=
        gaussSignFlip_compose_additive proc F' S₂
      rw [this]
      have : gaussSignFlip proc F' =
          gaussSignFlip proc F + gaussSignFlip proc S₁ :=
        gaussSignFlip_compose_additive proc F S₁
      rw [this, hpres1, hpres2, add_zero, add_zero]
      exact hflip
    · -- F preserves the sign. Then ¬FullOutcomePreserving forces nontrivial Pauli.
      right
      have hPauli_not_stab := hnotpres hpres
      -- F_S.pauliErrorAt t_i = F''.pauliErrorAt t_i (same spaceFaults)
      have hFS_pauli : F_S.pauliErrorAt proc.phase2Start = F''.pauliErrorAt proc.phase2Start := by
        apply pauliErrorAt_depends_only_on_spaceFaults
        simp only [F_S, SpacetimeFault.spaceComponent]
      -- F_S is in the centralizer (syndrome-free, concentrated at t_i, pure-space)
      have hFS_pureS : F_S.isPureSpace := F''.spaceComponent_isPureSpace
      have hFS_conc : ∀ t, t ≠ proc.phase2Start → F_S.spaceFaultsAt t = ∅ := by
        intro t ht
        simp only [F_S, SpacetimeFault.spaceComponent, SpacetimeFault.spaceFaultsAt]
        exact hS₂_conc t ht
      -- F_S is syndrome-free: F_S.timeFaults = ∅ (since F_S is spaceComponent)
      have hFS_free : IsSyndromeFreeGauging proc proc.detectorOfIndex F_S := by
        intro idx
        -- F_S = F''.spaceComponent = ⟨F''.spaceFaults, ∅⟩, so F_S.timeFaults = ∅ definitionally
        exact Detector.not_isViolated_no_faults _
      have hFS_cent : (theDeformedCode proc).inCentralizer
          (F_S.pauliErrorAt proc.phase2Start) :=
        centralizer_of_syndromeFree_pureSpace proc F_S hFS_free hFS_conc hFS_pureS
      -- F''.pauliErrorAt t_i = F.pauliErrorAt t_i * S₁.pauliErrorAt t_i * S₂.pauliErrorAt t_i
      have hF''_pauli : F''.pauliErrorAt proc.phase2Start =
          F.pauliErrorAt proc.phase2Start *
          (S₁.pauliErrorAt proc.phase2Start * S₂.pauliErrorAt proc.phase2Start) := by
        calc F''.pauliErrorAt proc.phase2Start
            = F'.pauliErrorAt proc.phase2Start * S₂.pauliErrorAt proc.phase2Start :=
              pauliErrorAt_compose_mul proc F' S₂ proc.phase2Start
          _ = (F.pauliErrorAt proc.phase2Start * S₁.pauliErrorAt proc.phase2Start) *
              S₂.pauliErrorAt proc.phase2Start := by
              rw [pauliErrorAt_compose_mul proc F S₁ proc.phase2Start]
          _ = F.pauliErrorAt proc.phase2Start *
              (S₁.pauliErrorAt proc.phase2Start * S₂.pauliErrorAt proc.phase2Start) :=
              _root_.mul_assoc _ _ _
      -- S₁, S₂ have Pauli in stabilizer group
      have hS₁_pauli : S₁.pauliErrorAt proc.phase2Start ∈
          (theDeformedCode proc).stabilizerGroup := hS₁_stab.2.2
      have hS₂_pauli : S₂.pauliErrorAt proc.phase2Start ∈
          (theDeformedCode proc).stabilizerGroup := hS₂_stab.2.2
      -- Their product is in the stabilizer group
      have hS_prod_pauli : S₁.pauliErrorAt proc.phase2Start *
          S₂.pauliErrorAt proc.phase2Start ∈
          (theDeformedCode proc).stabilizerGroup :=
        (theDeformedCode proc).stabilizerGroup.mul_mem hS₁_pauli hS₂_pauli
      -- F_S's Pauli is NOT in the stabilizer group
      have hFS_not_stab : F_S.pauliErrorAt proc.phase2Start ∉
          (theDeformedCode proc).stabilizerGroup := by
        rw [hFS_pauli, hF''_pauli]
        intro hmem
        -- If F * S_prod ∈ stab, then F = (F * S_prod) * S_prod⁻¹ ∈ stab
        apply hPauli_not_stab
        have hinv := (theDeformedCode proc).stabilizerGroup.inv_mem hS_prod_pauli
        have : F.pauliErrorAt proc.phase2Start =
            F.pauliErrorAt proc.phase2Start *
            (S₁.pauliErrorAt proc.phase2Start * S₂.pauliErrorAt proc.phase2Start) *
            (S₁.pauliErrorAt proc.phase2Start * S₂.pauliErrorAt proc.phase2Start)⁻¹ := by
          rw [mul_inv_cancel_right]
        rw [this]
        exact (theDeformedCode proc).stabilizerGroup.mul_mem hmem hinv
      -- F_S's Pauli is not 1
      have hFS_ne_one : F_S.pauliErrorAt proc.phase2Start ≠ 1 := by
        intro h1
        apply hFS_not_stab
        rw [h1]
        exact (theDeformedCode proc).stabilizerGroup.one_mem
      -- Combine: isLogicalOp = inCentralizer ∧ not in stab group ∧ not 1
      exact ⟨hFS_cent, hFS_not_stab, hFS_ne_one⟩

/-! ## Part VIII: The A_v String as Canonical Time Logical Fault -/

/-- **The A_v string is the canonical time-only logical fault.**
    It has weight d, is syndrome-free, and flips the gauging sign when d is odd. -/
theorem gaussString_is_time_logical (v : V) (hodd : Odd proc.d) :
    IsTimeLogicalFault proc (gaussStringFault proc v) :=
  ⟨gaussStringFault_isPureTime proc v,
   gaussStringFault_syndromeFree proc v,
   gaussStringFault_flipsSign_of_odd proc v hodd⟩

/-- **Time-only logical faults have weight at least d** (when d is odd). -/
theorem time_logical_weight_ge_d
    (F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (h : IsTimeLogicalFault proc F_T) (hodd : Odd proc.d) :
    proc.d ≤ F_T.weight :=
  pureTime_logicalFault_weight_ge_d proc F_T h.1 h.2.1 h.2.2 hodd

/-- **Sign flip of the A_v string.** -/
theorem gaussString_flipsSign (v : V) (hodd : Odd proc.d) :
    FlipsGaugingSign proc (gaussStringFault proc v) :=
  gaussStringFault_flipsSign_of_odd proc v hodd

/-! ## Part IX: Sign-Flip Analysis -/

/-- A pure-space fault has zero sign flip. -/
theorem gaussSignFlip_pureSpace
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureSpace) :
    gaussSignFlip proc F = 0 :=
  pureSpace_preservesSign proc F hpure

/-! ## Part X: Structural Decomposition Properties -/

/-- Any spacetime fault decomposes into its space and time components. -/
theorem fault_space_time_decomposition
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) :
    F = (F.spaceComponent).compose (F.timeComponent) :=
  (SpacetimeFault.decompose_space_time F).symm

/-- The weight of a fault is the sum of its space and time weights. -/
theorem weight_decomposition
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) :
    F.weight = F.spaceWeight + F.timeWeight :=
  F.weight_eq_space_plus_time

/-- The compose of pure-space and pure-time faults preserves the space component. -/
theorem compose_pureSpace_pureTime_spaceComponent
    (F_S F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpS : F_S.isPureSpace)
    (hpT : F_T.isPureTime) :
    (F_S.compose F_T).spaceComponent = F_S := by
  rw [SpacetimeFault.isPureSpace] at hpS
  rw [SpacetimeFault.isPureTime] at hpT
  ext a
  · simp only [SpacetimeFault.compose, SpacetimeFault.spaceComponent, Finset.mem_symmDiff]
    rw [hpT]
    simp only [Finset.notMem_empty, not_false_eq_true, and_true, false_and, or_false]
  · simp only [SpacetimeFault.compose, SpacetimeFault.spaceComponent, Finset.mem_symmDiff]
    rw [hpS]

/-- The compose of pure-space and pure-time faults preserves the time component. -/
theorem compose_pureSpace_pureTime_timeComponent
    (F_S F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpS : F_S.isPureSpace)
    (hpT : F_T.isPureTime) :
    (F_S.compose F_T).timeComponent = F_T := by
  rw [SpacetimeFault.isPureSpace] at hpS
  rw [SpacetimeFault.isPureTime] at hpT
  ext a
  · -- spaceFaults: timeComponent has ∅ spaceFaults, and F_T.spaceFaults = ∅
    simp only [SpacetimeFault.compose, SpacetimeFault.timeComponent, hpT]
  · -- timeFaults: timeComponent has the composed timeFaults, F_S.timeFaults = ∅
    simp only [SpacetimeFault.compose, SpacetimeFault.timeComponent, Finset.mem_symmDiff]
    rw [hpS]
    simp only [Finset.notMem_empty, not_false_eq_true, and_true, false_and, false_or]

/-- When F_S is pure-space and F_T is pure-time, their composition has weight
    equal to the sum of their weights (since their fault sets are disjoint). -/
theorem compose_pureSpace_pureTime_weight
    (F_S F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpS : F_S.isPureSpace)
    (hpT : F_T.isPureTime) :
    (F_S.compose F_T).weight = F_S.weight + F_T.weight := by
  simp only [SpacetimeFault.weight, SpacetimeFault.compose]
  rw [SpacetimeFault.isPureSpace] at hpS
  rw [SpacetimeFault.isPureTime] at hpT
  simp only [hpS, hpT, Finset.card_empty, add_zero, zero_add]
  congr 1
  · congr 1
    rw [← Finset.bot_eq_empty, symmDiff_bot]
  · congr 1
    rw [← Finset.bot_eq_empty, bot_symmDiff]

/-! ## Part XI: Decoupling Summary

Full summary combining decomposition with independence of effects. -/

/-- If F is a logical fault that flips the sign, then the time component
    contains at least one full A_v measurement string. -/
theorem sign_flipping_logical_has_Av_string
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hflip : FlipsGaugingSign proc F)
    (hodd : Odd proc.d) :
    ∃ v : V, ∀ r : Fin proc.d,
      (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults := by
  have hodd_strings := sign_flip_implies_odd_full_strings proc F hfree hflip hodd
  have hne : (Finset.univ.filter (fun v : V =>
      gaussFaultCount proc v F = proc.d)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty; simp [hempty] at hodd_strings
  obtain ⟨v, hv⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  refine ⟨v, fun r => ?_⟩
  have hall := syndromeFree_gauss_all_or_none proc v F hfree
  have hd_pos := Odd.pos hodd
  let r₀ : Fin proc.d := ⟨0, hd_pos⟩
  have h0 : (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r₀)⟩ :
      TimeFault proc.MeasLabel) ∈ F.timeFaults := by
    by_contra habs
    have hnone : gaussFaultCount proc v F = 0 := by
      rcases gaussFaultCount_zero_or_d proc v F hfree with h | h
      · exact h
      · exfalso
        have : (Finset.univ.filter (fun r' : Fin proc.d =>
            (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r')⟩ :
              TimeFault proc.MeasLabel) ∈ F.timeFaults)).card = proc.d := h
        have : r₀ ∉ (Finset.univ.filter (fun r' : Fin proc.d =>
            (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r')⟩ :
              TimeFault proc.MeasLabel) ∈ F.timeFaults)) := by
          simp [habs]
        have hlt : (Finset.univ.filter (fun r' : Fin proc.d =>
            (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r')⟩ :
              TimeFault proc.MeasLabel) ∈ F.timeFaults)).card <
            (Finset.univ : Finset (Fin proc.d)).card :=
          Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨r₀, Finset.mem_univ r₀, habs⟩)
        simp at hlt
        omega
    omega
  exact (hall r₀ r).mp h0

/-- **Main summary: Space-time decoupling for the fault-tolerant gauging procedure.**

For any spacetime logical fault F of the fault-tolerant gauging measurement procedure:

1. F decomposes as F = F_S · F_T · S where:
   - F_S is pure-space (Pauli errors only), concentrated at t_i
   - F_T is pure-time (measurement errors only), syndrome-free
   - S is a full gauging stabilizer (preserves sign AND code state)

2. The gauging sign σ is determined entirely by F_T:
   gaussSignFlip(F) = gaussSignFlip(F_T)

3. The Pauli error on the code state is determined entirely by F_S:
   pauliErrorAt(F, t) = pauliErrorAt(F_S, t) for all t

4. If F flips the sign, then F_T is a time-only logical fault
   (A_v measurement string with weight d, characterized in Lem 6)

5. If F applies a nontrivial space logical, then F_S is a space logical fault
   (deformed code logical operator at time t_i) -/
theorem spaceTime_decoupling_summary
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hlog : IsFullGaugingLogicalFault proc F) :
    -- The decomposition exists
    (∃ (F_S F_T S : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel),
      F = (F_S.compose F_T).compose S ∧
      F_S.isPureSpace ∧
      (∀ t, t ≠ proc.phase2Start → F_S.spaceFaultsAt t = ∅) ∧
      F_T.isPureTime ∧
      IsSyndromeFreeGauging proc proc.detectorOfIndex F_T ∧
      IsFullGaugingStabilizer proc S) ∧
    -- Sign depends only on time-faults
    (gaussSignFlip proc F = gaussSignFlip proc F.timeComponent) ∧
    -- Pauli error depends only on space-faults
    (∀ t, F.pauliErrorAt t = F.spaceComponent.pauliErrorAt t) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨F_S, F_T, S, hdecomp, hpS, hconc, hpT, hfreeT, hstab, _⟩ :=
      spaceTime_decomposition proc F hlog
    exact ⟨F_S, F_T, S, hdecomp, hpS, hconc, hpT, hfreeT, hstab⟩
  · exact (space_time_independent_effects proc F).1
  · exact (space_time_independent_effects proc F).2

/-! ## Part XII: Weight Bounds from Decoupling -/

/-- **Weight bound from decoupling:** For any pair of pure-space and pure-time faults,
    their composition has weight equal to the sum of weights. -/
theorem decoupling_weight_bound
    (F_S F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpS : F_S.isPureSpace)
    (hpT : F_T.isPureTime) :
    (F_S.compose F_T).weight ≤ F_S.weight + F_T.weight := by
  rw [compose_pureSpace_pureTime_weight proc F_S F_T hpS hpT]

end SpaceTimeDecoupling
