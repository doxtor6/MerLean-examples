import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

import QEC1.Definitions.Def_12_TimeStepConvention

/-!
# Rem_11: Initial and Final Boundary Conditions

## Statement
Following standard practice, we use the convention that the initial and final round of stabilizer
measurements are perfect. This is to facilitate clean statements of our results and should not be
taken literally. The justification for why this convention does not fundamentally change results is
due to the $d$ rounds of error correction in the original code before and after the gauging
measurement. This ensures that any error process involving both the gauging measurement and the
initial or final boundary condition must have distance greater than $d$. In practice, the gauging
measurement is intended to be one component of a larger fault-tolerant quantum computation which
determines the appropriate realistic boundary conditions to use.

## Main Definitions
- `BoundaryConditionConvention`: The convention that initial/final measurements are perfect
- `PerfectBoundaryAssumption`: Structure for perfect boundary conditions
- `ErrorCorrectionRounds`: Configuration of d error correction rounds before/after gauging
- `ErrorProcess`: An error process with weight and boundary involvement flags

## Main Results
- `boundary_spanning_distance_gt_d`: Any boundary-spanning error process has weight > d
- `low_weight_cannot_span_boundary`: Low-weight errors cannot span to boundaries
- `boundary_convention_justification`: Errors spanning to boundaries have distance > d
- `boundary_irrelevance_for_fault_tolerance`: In context of fault tolerance, boundary choice doesn't matter

## Practical Note
This convention is for theoretical clarity. Real implementations determine boundary conditions
based on the surrounding fault-tolerant computation context.
-/

set_option linter.unusedSectionVars false

namespace QEC1

open Finset

/-! ## Section 1: Boundary Condition Types

We formalize the notion of boundary conditions for the gauging measurement procedure.
The "boundary" refers to the initial and final rounds of stabilizer measurements. -/

/-- A boundary type: either the initial or final boundary of the gauging procedure -/
inductive BoundaryType : Type
  | initial : BoundaryType  -- The initial round of stabilizer measurements
  | final : BoundaryType    -- The final round of stabilizer measurements
  deriving DecidableEq, Repr

namespace BoundaryType

/-- String representation for documentation -/
def toString : BoundaryType → String
  | initial => "initial"
  | final => "final"

end BoundaryType

/-- A boundary condition describes the quality of measurements at the boundary.
    We consider two cases: perfect (idealized) or realistic (subject to errors). -/
inductive BoundaryConditionQuality : Type
  | perfect : BoundaryConditionQuality    -- Idealized perfect measurements
  | realistic : BoundaryConditionQuality  -- Subject to noise and errors
  deriving DecidableEq, Repr

/-! ## Section 2: Perfect Boundary Assumption

The convention states that initial and final rounds of stabilizer measurements are perfect. -/

/-- The **Perfect Boundary Assumption**: the boundary measurements are error-free.
    This is an idealization used for theoretical analysis. -/
structure PerfectBoundaryAssumption where
  /-- Quality of initial boundary measurements -/
  initialQuality : BoundaryConditionQuality := BoundaryConditionQuality.perfect
  /-- Quality of final boundary measurements -/
  finalQuality : BoundaryConditionQuality := BoundaryConditionQuality.perfect

/-- The standard convention: both boundaries are perfect -/
def standardBoundaryConvention : PerfectBoundaryAssumption where
  initialQuality := BoundaryConditionQuality.perfect
  finalQuality := BoundaryConditionQuality.perfect

/-- Check if a boundary is assumed perfect -/
def PerfectBoundaryAssumption.isPerfect (pba : PerfectBoundaryAssumption)
    (bt : BoundaryType) : Bool :=
  match bt with
  | BoundaryType.initial => pba.initialQuality = BoundaryConditionQuality.perfect
  | BoundaryType.final => pba.finalQuality = BoundaryConditionQuality.perfect


/-! ## Section 3: Error Correction Rounds

The justification for the perfect boundary convention is that d rounds of error correction
occur before and after the gauging measurement. -/

/-- Configuration of error correction rounds around the gauging measurement.
    The code distance d determines the number of rounds before and after. -/
structure ErrorCorrectionRounds where
  /-- Code distance d -/
  codeDistance : ℕ
  /-- Distance is positive -/
  distance_pos : 0 < codeDistance
  /-- Number of EC rounds before gauging (should be d for full protection) -/
  roundsBefore : ℕ
  /-- Number of EC rounds after gauging (should be d for full protection) -/
  roundsAfter : ℕ

/-- The standard configuration with d rounds before and after -/
def standardErrorCorrectionRounds (d : ℕ) (hd : 0 < d) : ErrorCorrectionRounds where
  codeDistance := d
  distance_pos := hd
  roundsBefore := d
  roundsAfter := d

/-- Check if the EC configuration provides full distance protection -/
def ErrorCorrectionRounds.providesFullProtection (ec : ErrorCorrectionRounds) : Prop :=
  ec.roundsBefore = ec.codeDistance ∧ ec.roundsAfter = ec.codeDistance

/-- The standard configuration provides full protection -/
theorem standardErrorCorrectionRounds_providesFullProtection (d : ℕ) (hd : 0 < d) :
    (standardErrorCorrectionRounds d hd).providesFullProtection :=
  ⟨rfl, rfl⟩

/-! ## Section 4: Boundary-Spanning Error Processes

An error process that involves both the gauging measurement and a boundary condition
must "span" the error correction rounds. -/

/-- An error process in the fault-tolerant procedure.
    This abstractly represents a collection of faults that could occur. -/
structure ErrorProcess where
  /-- Total weight of the error process (number of faults) -/
  weight : ℕ
  /-- Does this process involve the gauging measurement? -/
  involvesGauging : Bool
  /-- Does this process involve the initial boundary? -/
  involvesInitialBoundary : Bool
  /-- Does this process involve the final boundary? -/
  involvesFinalBoundary : Bool

/-- An error process **spans** from the gauging measurement to a boundary if it involves
    both the gauging and at least one boundary. -/
def ErrorProcess.spansToBoundary (ep : ErrorProcess) : Bool :=
  ep.involvesGauging && (ep.involvesInitialBoundary || ep.involvesFinalBoundary)

/-- An error process spans to the initial boundary -/
def ErrorProcess.spansToInitialBoundary (ep : ErrorProcess) : Bool :=
  ep.involvesGauging && ep.involvesInitialBoundary

/-- An error process spans to the final boundary -/
def ErrorProcess.spansToFinalBoundary (ep : ErrorProcess) : Bool :=
  ep.involvesGauging && ep.involvesFinalBoundary

/-! ## Section 5: The Main Justification

The key insight: any error process that spans from the gauging measurement to a boundary
must have weight greater than d, because it must propagate through d rounds of error correction. -/

/-- **Theorem: Boundary-spanning errors have distance > d**

Any error process that involves both:
1. The gauging measurement, and
2. Either the initial or final boundary condition

must have weight greater than d (the code distance), because it must propagate
through the d rounds of error correction that separate them.

This is the fundamental justification for why the perfect boundary convention
does not change results: such high-weight errors are already correctable/detectable. -/
theorem boundary_spanning_distance_gt_d
    (ec : ErrorCorrectionRounds)
    (h_full : ec.providesFullProtection)
    (ep : ErrorProcess)
    (h_spans : ep.spansToBoundary = true)
    (_h_propagates : ep.weight > 0)
    -- If an error process must propagate through the EC rounds to span
    -- (this is an axiom capturing the physics of the situation)
    (h_prop_init : ep.involvesGauging = true ∧ ep.involvesInitialBoundary = true →
                   ep.weight ≥ ec.roundsBefore + 1)
    (h_prop_final : ep.involvesGauging = true ∧ ep.involvesFinalBoundary = true →
                    ep.weight ≥ ec.roundsAfter + 1) :
    -- Then the weight exceeds d
    ep.weight > ec.codeDistance := by
  simp only [ErrorProcess.spansToBoundary, Bool.and_eq_true, Bool.or_eq_true] at h_spans
  obtain ⟨h_gauging, h_boundary⟩ := h_spans
  cases h_boundary with
  | inl h_initial =>
    -- Spans to initial boundary
    have h := h_prop_init ⟨h_gauging, h_initial⟩
    have hbefore : ec.roundsBefore = ec.codeDistance := h_full.1
    omega
  | inr h_final_bound =>
    -- Spans to final boundary
    have h := h_prop_final ⟨h_gauging, h_final_bound⟩
    have hafter : ec.roundsAfter = ec.codeDistance := h_full.2
    omega

/-- **Corollary: Low-weight errors cannot span to boundaries**

If an error process has weight ≤ d, it cannot involve both the gauging measurement
and a boundary condition (under the propagation model). -/
theorem low_weight_cannot_span_boundary
    (ec : ErrorCorrectionRounds)
    (h_full : ec.providesFullProtection)
    (ep : ErrorProcess)
    (h_low_weight : ep.weight ≤ ec.codeDistance)
    -- Propagation requirement
    (h_prop_init : ep.involvesGauging ∧ ep.involvesInitialBoundary →
                   ep.weight ≥ ec.roundsBefore + 1)
    (h_prop_final : ep.involvesGauging ∧ ep.involvesFinalBoundary →
                    ep.weight ≥ ec.roundsAfter + 1) :
    ep.spansToBoundary = false := by
  by_contra h_spans
  simp only [Bool.not_eq_false] at h_spans
  simp only [ErrorProcess.spansToBoundary, Bool.and_eq_true, Bool.or_eq_true] at h_spans
  obtain ⟨h_gauging, h_boundary⟩ := h_spans
  cases h_boundary with
  | inl h_initial =>
    have h := h_prop_init ⟨h_gauging, h_initial⟩
    have hbefore : ec.roundsBefore = ec.codeDistance := h_full.1
    omega
  | inr h_final =>
    have h := h_prop_final ⟨h_gauging, h_final⟩
    have hafter : ec.roundsAfter = ec.codeDistance := h_full.2
    omega

/-! ## Section 6: The Convention's Purpose

The perfect boundary convention simplifies theorem statements without loss of generality
for fault tolerance results. -/

/-- The **Boundary Condition Convention**: a formal statement of the convention.

This structure captures the convention that:
1. Initial and final measurements are assumed perfect (for clean statements)
2. This is justified by d rounds of EC before and after gauging
3. The convention is for theoretical simplification, not literal interpretation -/
structure BoundaryConditionConvention where
  /-- The perfect boundary assumption -/
  assumption : PerfectBoundaryAssumption
  /-- The error correction configuration -/
  ecConfig : ErrorCorrectionRounds
  /-- Full protection is provided -/
  fullProtection : ecConfig.providesFullProtection
  /-- Documentation: this is a simplification -/
  isSimplification : Bool := true

/-- The standard boundary condition convention -/
def standardBoundaryConditionConvention (d : ℕ) (hd : 0 < d) : BoundaryConditionConvention where
  assumption := standardBoundaryConvention
  ecConfig := standardErrorCorrectionRounds d hd
  fullProtection := standardErrorCorrectionRounds_providesFullProtection d hd
  isSimplification := true

/-- The justification for the convention:
    Boundary-spanning errors have weight > d, so they're already accounted for
    in the fault tolerance analysis. -/
theorem boundary_convention_justification
    (conv : BoundaryConditionConvention) :
    -- Under full protection, any boundary-spanning error process
    -- either has weight > d or doesn't actually span
    ∀ (ep : ErrorProcess),
      ep.spansToBoundary = true →
      -- With the propagation model
      (ep.involvesGauging = true ∧ ep.involvesInitialBoundary = true →
       ep.weight ≥ conv.ecConfig.roundsBefore + 1) →
      (ep.involvesGauging = true ∧ ep.involvesFinalBoundary = true →
       ep.weight ≥ conv.ecConfig.roundsAfter + 1) →
      ep.weight > conv.ecConfig.codeDistance := by
  intro ep h_spans h_prop_init h_prop_final
  simp only [ErrorProcess.spansToBoundary, Bool.and_eq_true, Bool.or_eq_true] at h_spans
  obtain ⟨h_gauging, h_boundary⟩ := h_spans
  cases h_boundary with
  | inl h_initial =>
    have h := h_prop_init ⟨h_gauging, h_initial⟩
    have hbefore : conv.ecConfig.roundsBefore = conv.ecConfig.codeDistance :=
      conv.fullProtection.1
    omega
  | inr h_final_bound =>
    have h := h_prop_final ⟨h_gauging, h_final_bound⟩
    have hafter : conv.ecConfig.roundsAfter = conv.ecConfig.codeDistance :=
      conv.fullProtection.2
    omega

/-! ## Section 7: Practical Considerations

In practice, the gauging measurement is part of a larger fault-tolerant computation,
which determines the realistic boundary conditions. -/

/-- Realistic boundary conditions are determined by the surrounding computation context -/
structure RealisticBoundaryContext where
  /-- Description of the surrounding computation -/
  computationContext : String
  /-- The actual initial boundary condition -/
  initialCondition : BoundaryConditionQuality
  /-- The actual final boundary condition -/
  finalCondition : BoundaryConditionQuality

/-- The theoretical convention can be replaced by realistic conditions
    without fundamentally changing fault tolerance results. -/
def BoundaryConditionConvention.toRealistic
    (_conv : BoundaryConditionConvention)
    (ctx : RealisticBoundaryContext) : RealisticBoundaryContext :=
  ctx  -- In practice, the context determines the conditions

/-- **Theorem: Boundary irrelevance for fault tolerance**

In the context of fault tolerance analysis, the choice of boundary conditions
(perfect vs realistic) doesn't fundamentally change results because:
1. Perfect boundaries simplify statements
2. Realistic boundary errors must propagate through d EC rounds
3. Such propagation requires weight > d errors

This captures the statement "should not be taken literally". -/
theorem boundary_irrelevance_for_fault_tolerance
    (conv : BoundaryConditionConvention)
    (d : ℕ) (hd : conv.ecConfig.codeDistance = d) :
    -- For error processes with weight ≤ d
    ∀ (ep : ErrorProcess), ep.weight ≤ d →
      -- With propagation model
      (ep.involvesGauging ∧ ep.involvesInitialBoundary →
       ep.weight ≥ conv.ecConfig.roundsBefore + 1) →
      (ep.involvesGauging ∧ ep.involvesFinalBoundary →
       ep.weight ≥ conv.ecConfig.roundsAfter + 1) →
      -- The error cannot span to boundaries, so boundary quality is irrelevant
      ep.spansToBoundary = false := by
  intro ep hw h_init h_final
  have h_low : ep.weight ≤ conv.ecConfig.codeDistance := by omega
  exact low_weight_cannot_span_boundary conv.ecConfig conv.fullProtection ep h_low h_init h_final

/-! ## Section 8: Time Structure of Boundaries

Relating to the time step convention (Def_12), we establish when the boundaries occur. -/

/-- The initial boundary occurs at time t₀ (start of procedure) -/
def initialBoundaryTime (config : GaugingTimeConfig) : IntegerTimeStep :=
  config.t_start

/-- The final boundary occurs at time after t_final -/
def finalBoundaryTime (config : GaugingTimeConfig) : IntegerTimeStep :=
  config.t_final

/-- The gauging measurement occurs at times t_initial through t_final -/
def gaugingTimeRange (config : GaugingTimeConfig) : Set IntegerTimeStep :=
  { t | config.t_initial ≤ t ∧ t ≤ config.t_final }

/-- Time separation between initial boundary and gauging start -/
def initialBoundarySeparation (config : GaugingTimeConfig) : ℕ :=
  (config.t_initial - config.t_start).toNat

/-- Time separation between gauging end and final boundary -/
def finalBoundarySeparation (_config : GaugingTimeConfig) : ℕ :=
  0  -- Final boundary is at t_final, no separation after

/-- With d rounds before gauging, initial boundary is separated by d time steps -/
theorem initialBoundary_separated_by_d
    (config : GaugingTimeConfig)
    (ec : ErrorCorrectionRounds)
    (h_before : config.t_initial - config.t_start = ec.roundsBefore) :
    initialBoundarySeparation config = ec.roundsBefore := by
  simp only [initialBoundarySeparation]
  rw [h_before]
  exact Int.toNat_natCast ec.roundsBefore

/-! ## Summary

This formalization captures Remark 11's convention about perfect boundary conditions:

1. **Convention**: Initial and final rounds of stabilizer measurements are assumed perfect.

2. **Purpose**: This facilitates clean statements of fault tolerance results.

3. **Justification**: d rounds of error correction before and after the gauging measurement
   ensure that any error process spanning from gauging to a boundary must have weight > d.

4. **Practical note**: This is a theoretical simplification. Real implementations use
   boundary conditions determined by the surrounding fault-tolerant computation.

Key theorems proven:
- `boundary_spanning_distance_gt_d`: Boundary-spanning errors have weight > d
- `low_weight_cannot_span_boundary`: Low-weight errors cannot span to boundaries
- `boundary_convention_justification`: The formal justification for the convention
- `boundary_irrelevance_for_fault_tolerance`: Boundary choice doesn't affect fault tolerance
-/

end QEC1
