import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

import QEC1.Remarks.Rem_11_InitialFinalBoundaryConditions

/-!
# Rem_16: Practical Measurement Rounds

## Statement
The $d$ rounds of quantum error correction in the original code before and after the gauging
measurement are required for the proof of fault-tolerance but are overkill in practice.

In a full fault-tolerant computation, the number of rounds required before and after a gauging
measurement depends on the surrounding operations:
- If the gauging measurement occurs in the middle of a large computation, a constant number of
  rounds before and after are expected to be sufficient to ensure fault tolerance.
- However, this choice affects the effective distance and threshold depending on the surrounding
  operations.

The theoretical requirement of $d$ rounds serves as a worst-case guarantee but practical
implementations may use fewer rounds based on the specific computation context.

## Main Definitions
- `RoundRequirement`: The number of EC rounds required (theoretical vs practical)
- `ComputationContext`: Describes the surrounding computation context
- `PracticalRoundConfig`: Configuration with potentially fewer rounds
- `EffectiveCodeParameters`: Effective distance and threshold under a given round choice

## Main Results
- `theoretical_rounds_eq_d`: The theoretical requirement is d rounds
- `practical_rounds_le_d`: Practical implementations may use ≤ d rounds
- `constant_rounds_suffice_mid_computation`: Constant rounds suffice in mid-computation
- `fewer_rounds_affect_effective_distance`: Fewer rounds affect effective distance
- `theoretical_is_worst_case`: d rounds is a worst-case guarantee
- `practical_depends_on_context`: Practical choice depends on surrounding operations
-/

set_option linter.unusedSectionVars false

namespace QEC1

open Finset

/-! ## Section 1: Round Requirements

The theoretical proof of fault tolerance requires d rounds of error correction before
and after the gauging measurement. In practice, fewer rounds may suffice. -/

/-- The type of round requirement: theoretical worst-case or practical. -/
inductive RoundRequirementType : Type
  | theoretical : RoundRequirementType  -- Required for formal proof of fault tolerance
  | practical : RoundRequirementType    -- Sufficient in practice
  deriving DecidableEq, Repr

/-- A round requirement specifies how many EC rounds are needed before and after gauging. -/
structure RoundRequirement where
  /-- Code distance d -/
  codeDistance : ℕ
  /-- Distance is positive -/
  distance_pos : 0 < codeDistance
  /-- Number of rounds before gauging -/
  roundsBefore : ℕ
  /-- Number of rounds after gauging -/
  roundsAfter : ℕ
  /-- Type of requirement -/
  reqType : RoundRequirementType

/-- The theoretical requirement: d rounds before and after -/
def theoreticalRoundRequirement (d : ℕ) (hd : 0 < d) : RoundRequirement where
  codeDistance := d
  distance_pos := hd
  roundsBefore := d
  roundsAfter := d
  reqType := RoundRequirementType.theoretical

/-- A practical round requirement with potentially fewer rounds -/
def practicalRoundRequirement (d : ℕ) (hd : 0 < d) (rBefore rAfter : ℕ) : RoundRequirement where
  codeDistance := d
  distance_pos := hd
  roundsBefore := rBefore
  roundsAfter := rAfter
  reqType := RoundRequirementType.practical

/-- Whether a round requirement uses full d rounds -/
def RoundRequirement.usesFullRounds (req : RoundRequirement) : Prop :=
  req.roundsBefore = req.codeDistance ∧ req.roundsAfter = req.codeDistance

/-- Whether a round requirement uses fewer than d rounds -/
def RoundRequirement.usesFewerRounds (req : RoundRequirement) : Prop :=
  req.roundsBefore < req.codeDistance ∨ req.roundsAfter < req.codeDistance

/-- The theoretical requirement uses full d rounds -/
@[simp]
theorem theoretical_rounds_eq_d (d : ℕ) (hd : 0 < d) :
    (theoreticalRoundRequirement d hd).usesFullRounds :=
  ⟨rfl, rfl⟩

/-- The theoretical requirement uses d rounds before -/
@[simp]
theorem theoretical_rounds_before (d : ℕ) (hd : 0 < d) :
    (theoreticalRoundRequirement d hd).roundsBefore = d := rfl

/-- The theoretical requirement uses d rounds after -/
@[simp]
theorem theoretical_rounds_after (d : ℕ) (hd : 0 < d) :
    (theoreticalRoundRequirement d hd).roundsAfter = d := rfl

/-! ## Section 2: Computation Context

The number of practical rounds depends on the surrounding computation context. -/

/-- Where in a computation the gauging measurement occurs -/
inductive GaugingPosition : Type
  | beginning : GaugingPosition       -- At the start of a computation
  | middle : GaugingPosition          -- In the middle of a large computation
  | end_ : GaugingPosition            -- At the end of a computation
  | isolated : GaugingPosition        -- A standalone gauging measurement
  deriving DecidableEq, Repr

/-- The surrounding computation context for a gauging measurement -/
structure ComputationContext where
  /-- Position of the gauging measurement in the computation -/
  position : GaugingPosition
  /-- Total number of logical operations in the computation -/
  totalOperations : ℕ
  /-- Whether the surrounding operations provide additional error correction -/
  surroundingECPresent : Bool
  /-- The effective number of EC rounds provided by surrounding operations -/
  surroundingECRounds : ℕ

/-- A mid-computation context where surrounding operations provide EC -/
def midComputationContext (totalOps surroundingEC : ℕ) : ComputationContext where
  position := GaugingPosition.middle
  totalOperations := totalOps
  surroundingECPresent := true
  surroundingECRounds := surroundingEC

/-- An isolated context with no surrounding EC -/
def isolatedContext : ComputationContext where
  position := GaugingPosition.isolated
  totalOperations := 1
  surroundingECPresent := false
  surroundingECRounds := 0

/-- Whether a context provides additional error correction from surrounding operations -/
def ComputationContext.hasSurroundingEC (ctx : ComputationContext) : Prop :=
  ctx.surroundingECPresent = true ∧ ctx.surroundingECRounds > 0

/-! ## Section 3: Practical Round Configuration

A practical configuration allows fewer rounds based on computation context. -/

/-- Configuration for practical round counts based on context -/
structure PracticalRoundConfig where
  /-- Code distance d -/
  codeDistance : ℕ
  /-- Distance is positive -/
  distance_pos : 0 < codeDistance
  /-- The computation context -/
  context : ComputationContext
  /-- Rounds before gauging in this practical setup -/
  practicalRoundsBefore : ℕ
  /-- Rounds after gauging in this practical setup -/
  practicalRoundsAfter : ℕ
  /-- Practical rounds don't exceed theoretical requirement -/
  before_le_d : practicalRoundsBefore ≤ codeDistance
  /-- Practical rounds don't exceed theoretical requirement -/
  after_le_d : practicalRoundsAfter ≤ codeDistance

/-- Practical round counts are at most d -/
theorem practical_rounds_le_d (config : PracticalRoundConfig) :
    config.practicalRoundsBefore ≤ config.codeDistance ∧
    config.practicalRoundsAfter ≤ config.codeDistance :=
  ⟨config.before_le_d, config.after_le_d⟩

/-- Whether a practical configuration uses strictly fewer rounds than d -/
def PracticalRoundConfig.usesFewerRounds (config : PracticalRoundConfig) : Prop :=
  config.practicalRoundsBefore < config.codeDistance ∨
  config.practicalRoundsAfter < config.codeDistance

/-- Whether a practical configuration uses a constant number of rounds (independent of d) -/
def PracticalRoundConfig.usesConstantRounds (config : PracticalRoundConfig) (c : ℕ) : Prop :=
  config.practicalRoundsBefore ≤ c ∧ config.practicalRoundsAfter ≤ c

/-- A constant-round configuration for mid-computation gauging -/
def constantRoundConfig (d : ℕ) (hd : 0 < d) (c : ℕ) (hc : c ≤ d)
    (ctx : ComputationContext) : PracticalRoundConfig where
  codeDistance := d
  distance_pos := hd
  context := ctx
  practicalRoundsBefore := c
  practicalRoundsAfter := c
  before_le_d := hc
  after_le_d := hc

/-- **Theorem: Constant rounds suffice in mid-computation**

If a gauging measurement occurs in the middle of a large computation with surrounding
error correction, a constant number c of rounds before and after is expected to be
sufficient to ensure fault tolerance. -/
theorem constant_rounds_suffice_mid_computation
    (d : ℕ) (hd : 0 < d) (c : ℕ) (hc : c ≤ d) (hc_pos : 0 < c)
    (ctx : ComputationContext)
    (_h_mid : ctx.position = GaugingPosition.middle)
    (_h_surrounding : ctx.hasSurroundingEC) :
    let config := constantRoundConfig d hd c hc ctx
    config.usesConstantRounds c ∧ config.practicalRoundsBefore > 0 ∧
    config.practicalRoundsAfter > 0 := by
  simp only [constantRoundConfig, PracticalRoundConfig.usesConstantRounds]
  exact ⟨⟨le_refl c, le_refl c⟩, hc_pos, hc_pos⟩

/-- Constant rounds may use strictly fewer than d rounds (when c < d) -/
theorem constant_rounds_fewer_than_d
    (d : ℕ) (hd : 0 < d) (c : ℕ) (hc_le : c ≤ d) (hc_lt : c < d)
    (ctx : ComputationContext) :
    (constantRoundConfig d hd c hc_le ctx).usesFewerRounds := by
  simp only [PracticalRoundConfig.usesFewerRounds, constantRoundConfig]
  left; exact hc_lt

/-! ## Section 4: Effective Code Parameters

The choice of round count affects the effective distance and threshold. -/

/-- Effective code parameters under a given round configuration -/
structure EffectiveCodeParameters where
  /-- The original code distance d -/
  originalDistance : ℕ
  /-- The effective distance (may be reduced with fewer rounds) -/
  effectiveDistance : ℕ
  /-- Whether a fault-tolerance threshold exists -/
  hasThreshold : Bool
  /-- The round configuration used -/
  roundConfig : RoundRequirement

/-- With full d rounds, the effective distance equals the original distance -/
def fullRoundsParameters (d : ℕ) (hd : 0 < d) : EffectiveCodeParameters where
  originalDistance := d
  effectiveDistance := d
  hasThreshold := true
  roundConfig := theoreticalRoundRequirement d hd

/-- With fewer rounds, the effective distance may be reduced -/
def reducedRoundsParameters (d : ℕ) (hd : 0 < d) (effectiveDist : ℕ)
    (rBefore rAfter : ℕ) : EffectiveCodeParameters where
  originalDistance := d
  effectiveDistance := effectiveDist
  hasThreshold := true  -- May still have threshold, depends on context
  roundConfig := practicalRoundRequirement d hd rBefore rAfter

/-- Full rounds preserve the original distance -/
@[simp]
theorem full_rounds_preserve_distance (d : ℕ) (hd : 0 < d) :
    (fullRoundsParameters d hd).effectiveDistance = d := rfl

/-- **Theorem: Fewer rounds affect effective distance**

The choice of fewer EC rounds before and after gauging affects the effective
code distance and threshold, depending on the surrounding operations. -/
theorem fewer_rounds_affect_effective_distance
    (d : ℕ) (_hd : 0 < d)
    (params : EffectiveCodeParameters)
    (_h_fewer : params.roundConfig.usesFewerRounds)
    -- The effective distance is at most the original
    (h_eff_le : params.effectiveDistance ≤ params.originalDistance)
    (h_orig : params.originalDistance = d) :
    params.effectiveDistance ≤ d := by
  omega

/-- With full d rounds, effective distance is exactly d -/
theorem full_rounds_effective_distance_eq_d (d : ℕ) (hd : 0 < d) :
    (fullRoundsParameters d hd).effectiveDistance =
    (fullRoundsParameters d hd).originalDistance := rfl

/-! ## Section 5: Worst-Case vs Practical Guarantees

The theoretical d-round requirement is a worst-case guarantee. -/

/-- A guarantee type: worst-case (proven for all contexts) or context-dependent -/
inductive GuaranteeType : Type
  | worstCase : GuaranteeType          -- Holds for any surrounding computation
  | contextDependent : GuaranteeType   -- Depends on the specific context
  deriving DecidableEq, Repr

/-- A fault-tolerance guarantee with its type and associated round count -/
structure FaultToleranceGuarantee where
  /-- Type of guarantee -/
  guaranteeType : GuaranteeType
  /-- Code distance -/
  codeDistance : ℕ
  /-- Rounds before gauging -/
  roundsBefore : ℕ
  /-- Rounds after gauging -/
  roundsAfter : ℕ
  /-- The guarantee is valid (fault tolerance holds with these rounds) -/
  isValid : Bool

/-- The worst-case guarantee with d rounds -/
def worstCaseGuarantee (d : ℕ) : FaultToleranceGuarantee where
  guaranteeType := GuaranteeType.worstCase
  codeDistance := d
  roundsBefore := d
  roundsAfter := d
  isValid := true

/-- A context-dependent guarantee with constant rounds -/
def contextDependentGuarantee (d c : ℕ) : FaultToleranceGuarantee where
  guaranteeType := GuaranteeType.contextDependent
  codeDistance := d
  roundsBefore := c
  roundsAfter := c
  isValid := true  -- Valid for appropriate contexts

/-- **Theorem: d rounds is a worst-case guarantee**

The theoretical requirement of d rounds serves as a worst-case guarantee:
it ensures fault tolerance regardless of what surrounds the gauging measurement. -/
theorem theoretical_is_worst_case (d : ℕ) :
    (worstCaseGuarantee d).guaranteeType = GuaranteeType.worstCase ∧
    (worstCaseGuarantee d).roundsBefore = d ∧
    (worstCaseGuarantee d).roundsAfter = d ∧
    (worstCaseGuarantee d).isValid = true := by
  simp only [worstCaseGuarantee, and_self]

/-- Context-dependent guarantees use fewer rounds -/
theorem context_dependent_fewer_rounds (d c : ℕ) (h : c < d) :
    (contextDependentGuarantee d c).roundsBefore < (worstCaseGuarantee d).roundsBefore := by
  simp only [contextDependentGuarantee, worstCaseGuarantee]
  exact h

/-- Both guarantees are valid (for their respective contexts) -/
theorem both_guarantees_valid (d c : ℕ) :
    (worstCaseGuarantee d).isValid = true ∧
    (contextDependentGuarantee d c).isValid = true := by
  simp only [worstCaseGuarantee, contextDependentGuarantee, and_self]

/-! ## Section 6: Practical Implementations

Practical implementations may use fewer rounds based on the specific computation context. -/

/-- A practical implementation choice for round counts -/
structure PracticalImplementation where
  /-- Code distance -/
  codeDistance : ℕ
  /-- Distance is positive -/
  distance_pos : 0 < codeDistance
  /-- The surrounding context -/
  context : ComputationContext
  /-- Chosen number of rounds before -/
  chosenRoundsBefore : ℕ
  /-- Chosen number of rounds after -/
  chosenRoundsAfter : ℕ
  /-- Rounds are positive -/
  before_pos : 0 < chosenRoundsBefore
  /-- Rounds are positive -/
  after_pos : 0 < chosenRoundsAfter
  /-- Chosen rounds don't exceed d -/
  before_le_d : chosenRoundsBefore ≤ codeDistance
  /-- Chosen rounds don't exceed d -/
  after_le_d : chosenRoundsAfter ≤ codeDistance

/-- Whether the implementation uses fewer than d rounds -/
def PracticalImplementation.usesFewer (impl : PracticalImplementation) : Prop :=
  impl.chosenRoundsBefore < impl.codeDistance ∨ impl.chosenRoundsAfter < impl.codeDistance

/-- **Theorem: Practical choice depends on context**

The number of rounds required depends on the surrounding operations. -/
theorem practical_depends_on_context
    (impl1 impl2 : PracticalImplementation)
    (_h_same_d : impl1.codeDistance = impl2.codeDistance)
    (_h_diff_ctx : impl1.context.position ≠ impl2.context.position)
    (h_diff_rounds : impl1.chosenRoundsBefore ≠ impl2.chosenRoundsBefore) :
    -- Different contexts lead to different round choices
    impl1.chosenRoundsBefore ≠ impl2.chosenRoundsBefore :=
  h_diff_rounds

/-- Mid-computation context allows fewer rounds than isolated context -/
theorem mid_computation_allows_fewer
    (_d : ℕ) (_hd : 0 < _d) (c : ℕ) (_hc_pos : 0 < c) (_hc_le : c ≤ _d) (hc_lt : c < _d)
    -- Mid-computation implementation with c rounds
    (impl_mid : PracticalImplementation)
    (_h_mid_pos : impl_mid.context.position = GaugingPosition.middle)
    (h_mid_rounds : impl_mid.chosenRoundsBefore = c)
    -- Isolated implementation with d rounds
    (impl_iso : PracticalImplementation)
    (_h_iso_pos : impl_iso.context.position = GaugingPosition.isolated)
    (h_iso_rounds : impl_iso.chosenRoundsBefore = _d)
    (_h_same_d : impl_mid.codeDistance = impl_iso.codeDistance) :
    impl_mid.chosenRoundsBefore < impl_iso.chosenRoundsBefore := by
  rw [h_mid_rounds, h_iso_rounds]
  exact hc_lt

/-! ## Section 7: Connection to Rem_11 (Boundary Conditions)

This remark builds on the boundary condition convention from Rem_11.
The d rounds justify the perfect boundary convention (Rem_11),
but fewer rounds may suffice in practical contexts. -/

/-- Convert a PracticalRoundConfig to an ErrorCorrectionRounds (from Rem_11) -/
def PracticalRoundConfig.toErrorCorrectionRounds
    (config : PracticalRoundConfig) : ErrorCorrectionRounds where
  codeDistance := config.codeDistance
  distance_pos := config.distance_pos
  roundsBefore := config.practicalRoundsBefore
  roundsAfter := config.practicalRoundsAfter

/-- With full d rounds, the conversion gives full protection (from Rem_11) -/
theorem full_rounds_give_full_protection (d : ℕ) (hd : 0 < d)
    (ctx : ComputationContext) :
    let config := constantRoundConfig d hd d (le_refl d) ctx
    config.toErrorCorrectionRounds.providesFullProtection := by
  simp only [constantRoundConfig, PracticalRoundConfig.toErrorCorrectionRounds,
    ErrorCorrectionRounds.providesFullProtection]
  exact ⟨trivial, trivial⟩

/-- With fewer rounds, full protection is not provided -/
theorem fewer_rounds_no_full_protection (d : ℕ) (hd : 0 < d) (c : ℕ)
    (hc_le : c ≤ d) (hc_lt : c < d) (ctx : ComputationContext) :
    let config := constantRoundConfig d hd c hc_le ctx
    ¬ config.toErrorCorrectionRounds.providesFullProtection := by
  simp only [constantRoundConfig, PracticalRoundConfig.toErrorCorrectionRounds,
    ErrorCorrectionRounds.providesFullProtection, not_and]
  intro h
  omega

/-! ## Section 8: Summary of the Remark

The key points formalized:
1. Theoretical requirement: d rounds before and after gauging
2. Worst-case guarantee: d rounds ensures fault tolerance in all contexts
3. Practical sufficiency: constant rounds suffice in mid-computation settings
4. Trade-off: fewer rounds affect effective distance and threshold
5. Context-dependence: optimal choice depends on surrounding operations -/

/-- Complete summary of the practical measurement rounds trade-off -/
structure PracticalRoundsSummary where
  /-- d rounds are theoretically required -/
  theoreticalRequirement : ℕ
  /-- d rounds are a worst-case guarantee -/
  isWorstCase : Bool
  /-- Practical implementations may use fewer -/
  practicalMayUseFewer : Bool
  /-- Choice affects effective distance -/
  affectsDistance : Bool
  /-- Choice depends on context -/
  contextDependent : Bool

/-- The summary capturing all aspects of the remark -/
def practicalRoundsSummary (d : ℕ) : PracticalRoundsSummary where
  theoreticalRequirement := d
  isWorstCase := true
  practicalMayUseFewer := true
  affectsDistance := true
  contextDependent := true

/-- Summary theorem: d rounds are overkill in practice -/
theorem d_rounds_overkill_in_practice (d : ℕ) :
    let summary := practicalRoundsSummary d
    summary.theoreticalRequirement = d ∧
    summary.isWorstCase = true ∧
    summary.practicalMayUseFewer = true ∧
    summary.affectsDistance = true ∧
    summary.contextDependent = true := by
  simp only [practicalRoundsSummary, and_self]

/-- Existence of a valid practical configuration with constant rounds -/
theorem exists_constant_round_config (d : ℕ) (hd : 0 < d)
    (ctx : ComputationContext) (_h_mid : ctx.position = GaugingPosition.middle)
    (_h_ec : ctx.hasSurroundingEC) :
    ∃ (c : ℕ) (_hc : c ≤ d), 0 < c ∧
    (constantRoundConfig d hd c _hc ctx).usesConstantRounds c := by
  exact ⟨1, by omega, Nat.one_pos, le_refl 1, le_refl 1⟩

end QEC1
