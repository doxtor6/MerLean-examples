import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_8_Detectors
import QEC1.Definitions.Def_9_Syndrome
import QEC1.Definitions.Def_10_FaultTolerantGaugingProcedure
import QEC1.Lemmas.Lem_4_SpacetimeCodeDetectors
import Mathlib.Tactic

/-!
# Definition 11: Spacetime Logical Fault

## Statement
A **spacetime logical fault** is a collection of space-faults and time-faults (Def 7) that:
1. Does not violate any detector (i.e., the syndrome (Def 9) is empty), AND
2. Changes the outcome of the fault-tolerant gauging measurement procedure (Def 10).

A **spacetime stabilizer** is a collection of space-faults and time-faults that:
1. Does not violate any detector, AND
2. Does NOT change the outcome of the procedure.

Every syndrome-free fault collection is either a spacetime logical fault or a spacetime stabilizer.

## Main Results
- `IsSyndromeFree`: A fault has empty syndrome (no detectors violated)
- `IsSpacetimeLogicalFault`: Syndrome-free AND changes the measurement outcome
- `IsSpacetimeStabilizer`: Syndrome-free AND does NOT change the measurement outcome
- `syndromeFree_dichotomy`: Every syndrome-free fault is either logical or stabilizer

## Corollaries
- `logicalFault_not_stabilizer`: The dichotomy is exclusive
- `empty_isSpacetimeStabilizer`: The empty fault is a stabilizer
- `IsSpacetimeLogicalFault.weight_pos`: A logical fault has positive weight
- `syndromeFree_logicalFault_iff_not_stabilizer`: Characterization via negation
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {V : Type*} [Fintype V] [DecidableEq V]

open Finset PauliOp GaussFlux DeformedCode DeformedOperator FaultTolerantGaugingProcedure

variable {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  {cycles : C → Set G.edgeSet} [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  {checks : J → PauliOp V}

namespace SpacetimeLogicalFault

/-! ## Syndrome-Free Faults

We work with an arbitrary collection of detectors indexed by a fintype `I`.
In the context of the fault-tolerant gauging procedure (Def 10), `I` is
instantiated with `DetectorIndex V C J G.edgeSet d` from Lemma 4. -/

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {M : Type*} [DecidableEq M] [DecidableEq (TimeFault M)]

/-- A spacetime fault is **syndrome-free** if the syndrome is empty, i.e., no detector
    is violated. This is the first condition for both spacetime logical faults and
    spacetime stabilizers. -/
def IsSyndromeFree {Q T : Type*}
    (detectors : I → Detector M) (F : SpacetimeFault Q T M) : Prop :=
  syndromeFault detectors F = ∅

/-- Equivalently, a fault is syndrome-free iff every detector is not violated. -/
theorem isSyndromeFree_iff {Q T : Type*}
    (detectors : I → Detector M) (F : SpacetimeFault Q T M) :
    IsSyndromeFree detectors F ↔ ∀ idx : I, ¬(detectors idx).isViolated F.timeFaults := by
  unfold IsSyndromeFree syndromeFault
  simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]

/-- Equivalently, syndrome-free means the syndrome vector is identically zero. -/
theorem isSyndromeFree_iff_syndromeVec {Q T : Type*}
    (detectors : I → Detector M) (F : SpacetimeFault Q T M) :
    IsSyndromeFree detectors F ↔ syndromeVec detectors F = 0 := by
  rw [isSyndromeFree_iff]
  constructor
  · intro h
    funext i
    simp [syndromeVec, h i]
  · intro h idx
    have hv := congr_fun h idx
    unfold syndromeVec at hv
    simp only [Pi.zero_apply] at hv
    by_contra habs
    rw [if_pos habs] at hv
    exact one_ne_zero hv

/-! ## Outcome-Changing Faults

The gauging procedure produces a classical outcome σ ∈ ZMod 2 (the measurement sign)
and a post-measurement state. A fault "changes the outcome" if it either:
1. Flips the measurement sign σ (changing the classical bit), OR
2. Applies a non-trivial logical operator to the post-measurement code state.

We parametrize the outcome-preserving predicate abstractly, as the precise
quantum state evolution requires Hilbert space formalism. The key structural
content is the syndrome-free dichotomy: every syndrome-free fault is either
outcome-changing (logical fault) or outcome-preserving (stabilizer). -/

/-- A spacetime fault is **outcome-preserving** if its net effect on the
    procedure is trivial: it preserves both the measurement sign and the
    logical information in the post-measurement state.
    We parametrize by a predicate classifying outcome-preserving faults. -/
def IsOutcomePreserving {Q T : Type*}
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M) : Prop :=
  outcomePreserving F

/-- A fault **changes the outcome** if it is not outcome-preserving. -/
def IsOutcomeChanging {Q T : Type*}
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M) : Prop :=
  ¬outcomePreserving F

/-! ## Main Definitions -/

/-- A **spacetime logical fault** is a syndrome-free fault that changes the outcome
    of the fault-tolerant gauging measurement procedure.
    Condition 1: No detector is violated (syndrome is empty).
    Condition 2: The fault changes the measurement result or applies a
    non-trivial logical to the post-measurement state. -/
def IsSpacetimeLogicalFault {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M) : Prop :=
  IsSyndromeFree detectors F ∧ IsOutcomeChanging outcomePreserving F

/-- A **spacetime stabilizer** is a syndrome-free fault that does NOT change
    the outcome of the procedure.
    Condition 1: No detector is violated (syndrome is empty).
    Condition 2: The fault preserves both the measurement result and the
    logical information in the post-measurement state. -/
def IsSpacetimeStabilizer {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M) : Prop :=
  IsSyndromeFree detectors F ∧ IsOutcomePreserving outcomePreserving F

/-! ## Dichotomy -/

/-- **Every syndrome-free fault is either a spacetime logical fault or a spacetime stabilizer.**
    This is a tautological consequence of the definitions: a syndrome-free fault either
    changes the outcome (logical fault) or does not (stabilizer). -/
theorem syndromeFree_dichotomy {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M)
    (hfree : IsSyndromeFree detectors F) :
    IsSpacetimeLogicalFault detectors outcomePreserving F ∨
    IsSpacetimeStabilizer detectors outcomePreserving F := by
  by_cases h : outcomePreserving F
  · right; exact ⟨hfree, h⟩
  · left; exact ⟨hfree, h⟩

/-- The dichotomy is exclusive: a fault cannot be both a logical fault and a stabilizer. -/
theorem logicalFault_not_stabilizer {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M)
    (hlog : IsSpacetimeLogicalFault detectors outcomePreserving F) :
    ¬IsSpacetimeStabilizer detectors outcomePreserving F := by
  intro hstab
  exact hlog.2 hstab.2

/-- Conversely, a stabilizer is not a logical fault. -/
theorem stabilizer_not_logicalFault {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M)
    (hstab : IsSpacetimeStabilizer detectors outcomePreserving F) :
    ¬IsSpacetimeLogicalFault detectors outcomePreserving F := by
  intro hlog
  exact hlog.2 hstab.2

/-! ## Accessor Lemmas -/

/-- A spacetime logical fault is syndrome-free. -/
theorem IsSpacetimeLogicalFault.syndromeFree {Q T : Type*}
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (h : IsSpacetimeLogicalFault detectors outcomePreserving F) :
    IsSyndromeFree detectors F :=
  h.1

/-- A spacetime logical fault changes the outcome. -/
theorem IsSpacetimeLogicalFault.changesOutcome {Q T : Type*}
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (h : IsSpacetimeLogicalFault detectors outcomePreserving F) :
    IsOutcomeChanging outcomePreserving F :=
  h.2

/-- A spacetime stabilizer is syndrome-free. -/
theorem IsSpacetimeStabilizer.syndromeFree {Q T : Type*}
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (h : IsSpacetimeStabilizer detectors outcomePreserving F) :
    IsSyndromeFree detectors F :=
  h.1

/-- A spacetime stabilizer preserves the outcome. -/
theorem IsSpacetimeStabilizer.preservesOutcome {Q T : Type*}
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (h : IsSpacetimeStabilizer detectors outcomePreserving F) :
    IsOutcomePreserving outcomePreserving F :=
  h.2

/-! ## Empty Fault is a Stabilizer -/

/-- The empty fault has empty syndrome: no faults means no detector violations. -/
theorem empty_isSyndromeFree {Q T : Type*}
    [DecidableEq Q] [DecidableEq T] [DecidableEq (SpaceFault Q T)]
    (detectors : I → Detector M) :
    IsSyndromeFree detectors (SpacetimeFault.empty : SpacetimeFault Q T M) := by
  unfold IsSyndromeFree
  rw [syndromeFault_empty]

/-- The empty fault is a spacetime stabilizer, provided it is outcome-preserving
    (the natural requirement: no fault means no change). -/
theorem empty_isSpacetimeStabilizer {Q T : Type*}
    [DecidableEq Q] [DecidableEq T] [DecidableEq (SpaceFault Q T)]
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (hempty : outcomePreserving SpacetimeFault.empty) :
    IsSpacetimeStabilizer detectors outcomePreserving SpacetimeFault.empty :=
  ⟨empty_isSyndromeFree detectors, hempty⟩

/-! ## Weight Properties -/

/-- A syndrome-free fault of weight 0 is the empty fault. -/
theorem syndromeFree_weight_zero_eq_empty {Q T : Type*}
    [DecidableEq Q] [DecidableEq T] [DecidableEq (SpaceFault Q T)]
    {detectors : I → Detector M}
    {F : SpacetimeFault Q T M}
    (_hfree : IsSyndromeFree detectors F)
    (hw : F.weight = 0) : F = SpacetimeFault.empty := by
  rwa [SpacetimeFault.weight_zero_iff_empty] at hw

/-- A spacetime logical fault must have positive weight (it cannot be empty). -/
theorem IsSpacetimeLogicalFault.weight_pos {Q T : Type*}
    [DecidableEq Q] [DecidableEq T] [DecidableEq (SpaceFault Q T)]
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (hlog : IsSpacetimeLogicalFault detectors outcomePreserving F)
    (hempty : outcomePreserving SpacetimeFault.empty) :
    0 < F.weight := by
  by_contra h
  push_neg at h
  have hw : F.weight = 0 := Nat.le_zero.mp h
  have heq : F = SpacetimeFault.empty := syndromeFree_weight_zero_eq_empty hlog.1 hw
  subst heq
  exact hlog.2 hempty

/-! ## Characterization via Syndrome Vector -/

/-- A spacetime logical fault has zero syndrome vector. -/
theorem IsSpacetimeLogicalFault.syndromeVec_eq_zero {Q T : Type*}
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (h : IsSpacetimeLogicalFault detectors outcomePreserving F) :
    syndromeVec detectors F = 0 :=
  (isSyndromeFree_iff_syndromeVec detectors F).mp h.1

/-- A spacetime stabilizer has zero syndrome vector. -/
theorem IsSpacetimeStabilizer.syndromeVec_eq_zero {Q T : Type*}
    {detectors : I → Detector M}
    {outcomePreserving : SpacetimeFault Q T M → Prop}
    {F : SpacetimeFault Q T M}
    (h : IsSpacetimeStabilizer detectors outcomePreserving F) :
    syndromeVec detectors F = 0 :=
  (isSyndromeFree_iff_syndromeVec detectors F).mp h.1

/-! ## Classification of Syndrome-Free Faults -/

/-- The set of all syndrome-free faults partitions into logical faults and stabilizers. -/
theorem syndromeFree_iff_logicalFault_or_stabilizer {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M) :
    IsSyndromeFree detectors F ↔
      (IsSpacetimeLogicalFault detectors outcomePreserving F ∨
       IsSpacetimeStabilizer detectors outcomePreserving F) := by
  constructor
  · exact syndromeFree_dichotomy detectors outcomePreserving F
  · intro h
    rcases h with hlog | hstab
    · exact hlog.1
    · exact hstab.1

/-- A syndrome-free fault is a logical fault iff it is not a stabilizer. -/
theorem syndromeFree_logicalFault_iff_not_stabilizer {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M)
    (hfree : IsSyndromeFree detectors F) :
    IsSpacetimeLogicalFault detectors outcomePreserving F ↔
    ¬IsSpacetimeStabilizer detectors outcomePreserving F := by
  constructor
  · exact logicalFault_not_stabilizer detectors outcomePreserving F
  · intro hns
    refine ⟨hfree, ?_⟩
    intro hp
    exact hns ⟨hfree, hp⟩

/-- A syndrome-free fault is a stabilizer iff it is not a logical fault. -/
theorem syndromeFree_stabilizer_iff_not_logicalFault {Q T : Type*}
    (detectors : I → Detector M)
    (outcomePreserving : SpacetimeFault Q T M → Prop)
    (F : SpacetimeFault Q T M)
    (hfree : IsSyndromeFree detectors F) :
    IsSpacetimeStabilizer detectors outcomePreserving F ↔
    ¬IsSpacetimeLogicalFault detectors outcomePreserving F := by
  constructor
  · intro hstab hlog
    exact logicalFault_not_stabilizer detectors outcomePreserving F hlog hstab
  · intro hnl
    refine ⟨hfree, ?_⟩
    by_contra hnp
    exact hnl ⟨hfree, hnp⟩

/-! ## Gauging Sign Flip

For the fault-tolerant gauging procedure specifically, we can define the sign flip
indicator that tracks whether time-faults flip the measurement sign σ. -/

variable (proc : FaultTolerantGaugingProcedure G cycles checks)

/-- The sign flip indicator: the parity of time-faults that affect Gauss's law
    measurements. A fault changes the gauging sign σ iff this is 1 (mod 2).
    σ = ∑_v ε_v, and a time-fault on a Gauss measurement flips one ε_v. -/
noncomputable def gaussSignFlip
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : ZMod 2 :=
  ∑ v : V, ∑ r : Fin proc.d,
    if (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults then 1 else 0

/-- A fault flips the gauging sign if the sign flip indicator is 1. -/
def FlipsGaugingSign
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  gaussSignFlip proc F = 1

/-- A fault preserves the gauging sign if the sign flip indicator is 0. -/
def PreservesGaugingSign
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  gaussSignFlip proc F = 0

/-- The sign flip is always 0 or 1 in ZMod 2. -/
theorem gaussSignFlip_zero_or_one
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) :
    gaussSignFlip proc F = 0 ∨ gaussSignFlip proc F = 1 := by
  have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    intro x; fin_cases x <;> simp
  exact this _

/-- The sign flip dichotomy: a fault either flips or preserves the gauging sign. -/
theorem flipsOrPreserves
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) :
    FlipsGaugingSign proc F ∨ PreservesGaugingSign proc F := by
  rcases gaussSignFlip_zero_or_one proc F with h | h
  · right; exact h
  · left; exact h

/-- Flipping and preserving are mutually exclusive. -/
theorem flipsGaugingSign_not_preserves
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (h : FlipsGaugingSign proc F) : ¬PreservesGaugingSign proc F := by
  intro hp
  rw [FlipsGaugingSign] at h
  rw [PreservesGaugingSign] at hp
  rw [hp] at h
  exact zero_ne_one h

/-- Preserving and flipping are mutually exclusive. -/
theorem preservesGaugingSign_not_flips
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (h : PreservesGaugingSign proc F) : ¬FlipsGaugingSign proc F := by
  intro hf
  exact flipsGaugingSign_not_preserves proc F hf h

/-! ## Instantiation for the Gauging Procedure

We provide specialized definitions for the fault-tolerant gauging procedure
using its specific detector index type and measurement labels. -/

/-- A syndrome-free fault in the gauging procedure:
    no detector from the spacetime code (Lemma 4) is violated. -/
def IsSyndromeFreeGauging
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  ∀ idx : DetectorIndex V C J G.edgeSet proc.d,
    ¬(detectors idx).isViolated F.timeFaults

/-- A spacetime logical fault in the gauging procedure:
    syndrome-free AND changes the outcome. -/
def IsGaugingLogicalFault
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  IsSyndromeFreeGauging proc detectors F ∧ ¬outcomePreserving F

/-- A spacetime stabilizer in the gauging procedure:
    syndrome-free AND preserves the outcome. -/
def IsGaugingStabilizer
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  IsSyndromeFreeGauging proc detectors F ∧ outcomePreserving F

/-- Every syndrome-free fault in the gauging procedure is either
    a logical fault or a stabilizer. -/
theorem gaugingSyndromeFree_dichotomy
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc detectors F) :
    IsGaugingLogicalFault proc detectors outcomePreserving F ∨
    IsGaugingStabilizer proc detectors outcomePreserving F := by
  by_cases h : outcomePreserving F
  · right; exact ⟨hfree, h⟩
  · left; exact ⟨hfree, h⟩

/-- The gauging dichotomy is exclusive. -/
theorem gaugingLogicalFault_not_stabilizer
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hlog : IsGaugingLogicalFault proc detectors outcomePreserving F) :
    ¬IsGaugingStabilizer proc detectors outcomePreserving F := by
  intro hstab
  exact hlog.2 hstab.2

/-- A gauging stabilizer is not a logical fault. -/
theorem gaugingStabilizer_not_logicalFault
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hstab : IsGaugingStabilizer proc detectors outcomePreserving F) :
    ¬IsGaugingLogicalFault proc detectors outcomePreserving F := by
  intro hlog
  exact hlog.2 hstab.2

/-- A syndrome-free gauging fault is a logical fault iff not a stabilizer. -/
theorem gaugingSyndromeFree_logicalFault_iff
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc detectors F) :
    IsGaugingLogicalFault proc detectors outcomePreserving F ↔
    ¬IsGaugingStabilizer proc detectors outcomePreserving F := by
  constructor
  · exact gaugingLogicalFault_not_stabilizer proc detectors outcomePreserving F
  · intro hns
    refine ⟨hfree, ?_⟩
    intro hp
    exact hns ⟨hfree, hp⟩

/-- A syndrome-free gauging fault is a stabilizer iff not a logical fault. -/
theorem gaugingSyndromeFree_stabilizer_iff
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc detectors F) :
    IsGaugingStabilizer proc detectors outcomePreserving F ↔
    ¬IsGaugingLogicalFault proc detectors outcomePreserving F := by
  constructor
  · intro hstab hlog
    exact gaugingLogicalFault_not_stabilizer proc detectors outcomePreserving F hlog hstab
  · intro hnl
    refine ⟨hfree, ?_⟩
    by_contra hnp
    exact hnl ⟨hfree, hnp⟩

end SpacetimeLogicalFault
