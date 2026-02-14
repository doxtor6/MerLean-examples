import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_10_FaultTolerantGaugingProcedure
import QEC1.Definitions.Def_11_SpacetimeLogicalFault
import QEC1.Definitions.Def_12_SpacetimeFaultDistance
import QEC1.Lemmas.Lem_4_SpacetimeCodeDetectors
import QEC1.Lemmas.Lem_5_SpacetimeStabilizers
import Mathlib.Tactic

/-!
# Lemma 6: Time Fault-Distance

## Statement
The fault-distance for pure measurement and initialization errors (time-faults only,
no space-faults) in the fault-tolerant gauging measurement procedure (Def 10) is
$t_o - t_i = d$, the number of rounds in the deformed code phase.

## Main Results
- `timeFaultDistance`: The time fault-distance (minimum weight of pure-time logical fault)
- `gaussStringFault`: The A_v measurement string of weight d (upper bound witness)
- `gaussStringFault_weight_eq_d`: The A_v string has weight d
- `gaussStringFault_syndromeFree`: The A_v string is syndrome-free
- `timeFaultDistance_le_d`: d_time ≤ d (upper bound)
- `timeFaultDistance_ge_d`: d_time ≥ d (lower bound)
- `timeFaultDistance_eq_d`: d_time = d (main theorem)

## Proof Outline
**Upper bound:** A string of A_v measurement faults for a single vertex v
at all d rounds of Phase 2 has weight d, is syndrome-free (repeated detectors
see two flips that cancel), and flips σ (since d is odd).

**Lower bound:** Any pure time-fault that changes the logical outcome must flip σ.
By the all-or-none constraint from repeated Gauss detectors, each vertex's A_v faults
span either all d rounds or none. A sign flip requires an odd number of full A_v
strings, each contributing d to weight.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset PauliOp GaussFlux DeformedCode DeformedOperator
open FaultTolerantGaugingProcedure SpacetimeLogicalFault SpacetimeStabilizers
open SpacetimeFaultDistance

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  {cycles : C → Set G.edgeSet} [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  {checks : J → PauliOp V}

namespace TimeFaultDistance

variable (proc : FaultTolerantGaugingProcedure G cycles checks)

/-! ## Part I: Pure-Time Logical Fault Definition -/

/-- A pure-time spacetime fault: no space-faults, only time-faults. -/
def IsPureTimeFault (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  F.isPureTime

/-- A pure-time gauging logical fault: pure-time AND a gauging logical fault. -/
def IsPureTimeLogicalFault
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : Prop :=
  IsPureTimeFault proc F ∧ IsGaugingLogicalFault proc detectors outcomePreserving F

/-- The set of weights of pure-time gauging logical faults. -/
def pureTimeLogicalFaultWeights
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop) : Set ℕ :=
  { w : ℕ | ∃ F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel,
    IsPureTimeLogicalFault proc detectors outcomePreserving F ∧ F.weight = w }

/-- The **time fault-distance**: minimum weight of a pure-time gauging logical fault. -/
noncomputable def timeFaultDistance
    (detectors : DetectorIndex V C J G.edgeSet proc.d → Detector proc.MeasLabel)
    (outcomePreserving : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel → Prop) : ℕ :=
  sInf (pureTimeLogicalFaultWeights proc detectors outcomePreserving)

/-! ## Part II: The A_v Measurement String (Upper Bound Witness) -/

/-- The A_v measurement string: time-faults on A_v at all d rounds of Phase 2. -/
def gaussMeasFaults (v : V) : Finset (TimeFault proc.MeasLabel) :=
  Finset.univ.image (fun r : Fin proc.d =>
    (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
      TimeFault proc.MeasLabel))

/-- The A_v measurement string as a spacetime fault. -/
def gaussStringFault (v : V) : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel :=
  ⟨∅, gaussMeasFaults proc v⟩

/-- The A_v string is pure-time. -/
theorem gaussStringFault_isPureTime (v : V) :
    (gaussStringFault proc v).isPureTime := by
  simp [gaussStringFault, SpacetimeFault.isPureTime]

/-- The image map for A_v faults is injective. -/
theorem gaussMeasFaults_injective (v : V) :
    Function.Injective (fun r : Fin proc.d =>
      (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
        TimeFault proc.MeasLabel)) := by
  intro r₁ r₂ h
  simp only [TimeFault.mk.injEq, FTGaugingMeasurement.phase2.injEq,
    DeformedCodeMeasurement.gaussLaw.injEq] at h
  exact h.2

/-- The A_v string has exactly d time-faults. -/
theorem gaussMeasFaults_card (v : V) :
    (gaussMeasFaults proc v).card = proc.d := by
  rw [gaussMeasFaults, Finset.card_image_of_injective _ (gaussMeasFaults_injective proc v)]
  exact Finset.card_fin proc.d

/-- The A_v string has weight d. -/
theorem gaussStringFault_weight_eq_d (v : V) :
    (gaussStringFault proc v).weight = proc.d := by
  simp [gaussStringFault, SpacetimeFault.weight, gaussMeasFaults_card]

/-! ### Membership lemmas -/

/-- A time-fault is in the A_v string iff it's a Gauss A_v measurement at some round. -/
theorem mem_gaussMeasFaults (v : V) (tf : TimeFault proc.MeasLabel) :
    tf ∈ gaussMeasFaults proc v ↔
    ∃ r : Fin proc.d, tf = ⟨FTGaugingMeasurement.phase2
      (DeformedCodeMeasurement.gaussLaw v r)⟩ := by
  simp only [gaussMeasFaults, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩; exact ⟨r, rfl⟩

theorem gaussStringFault_timeFaults_eq (v : V) :
    (gaussStringFault proc v).timeFaults = gaussMeasFaults proc v := rfl

/-- A Gauss A_v measurement at round r is in the A_v string. -/
theorem gaussStringFault_mem_gauss (v : V) (r : Fin proc.d) :
    (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
      TimeFault proc.MeasLabel) ∈ (gaussStringFault proc v).timeFaults := by
  rw [gaussStringFault_timeFaults_eq, mem_gaussMeasFaults]
  exact ⟨r, rfl⟩

/-- A Gauss A_w measurement (w ≠ v) is not in the A_v string. -/
theorem gaussStringFault_no_other_gauss (v w : V) (r : Fin proc.d) (hvw : v ≠ w) :
    (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r)⟩ :
      TimeFault proc.MeasLabel) ∉ (gaussStringFault proc v).timeFaults := by
  rw [gaussStringFault_timeFaults_eq, mem_gaussMeasFaults]
  push_neg
  intro r' h
  have := congr_arg TimeFault.measurement h
  simp only [FTGaugingMeasurement.phase2.injEq, DeformedCodeMeasurement.gaussLaw.injEq] at this
  exact hvw this.1.symm

/-! ### The A_v string flips the gauging sign -/

/-- The gaussSignFlip for the A_v string equals d (mod 2). -/
theorem gaussStringFault_signFlip (v : V) :
    gaussSignFlip proc (gaussStringFault proc v) = (proc.d : ZMod 2) := by
  unfold gaussSignFlip
  have hsum : ∀ w : V,
      (∑ r : Fin proc.d,
        if (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r)⟩ :
            TimeFault proc.MeasLabel) ∈ (gaussStringFault proc v).timeFaults
        then (1 : ZMod 2) else 0) =
      if w = v then (proc.d : ZMod 2) else 0 := by
    intro w
    by_cases hvw : v = w
    · subst hvw
      have : ∀ r : Fin proc.d,
          (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
            TimeFault proc.MeasLabel) ∈ (gaussStringFault proc v).timeFaults :=
        gaussStringFault_mem_gauss proc v
      simp only [this, ite_true]
      simp [Finset.sum_const, Finset.card_fin]
    · have hne : v ≠ w := hvw
      rw [if_neg (Ne.symm hne)]
      apply Finset.sum_eq_zero
      intro r _
      have : (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r)⟩ :
          TimeFault proc.MeasLabel) ∉ (gaussStringFault proc v).timeFaults :=
        gaussStringFault_no_other_gauss proc v w r hne
      simp [this]
  simp_rw [hsum]
  rw [Finset.sum_ite_eq' Finset.univ v]
  simp

/-- When d is odd, the A_v string flips the gauging sign. -/
theorem gaussStringFault_flipsSign_of_odd (v : V) (hodd : Odd proc.d) :
    FlipsGaugingSign proc (gaussStringFault proc v) := by
  rw [FlipsGaugingSign, gaussStringFault_signFlip]
  exact hodd.natCast_zmod_two

/-! ### Syndrome-freeness of the A_v string -/

/-- Helper: no A_v measurement in the gaussStringFault is a non-Gauss-v measurement. -/
private theorem gauss_string_disjoint_nonGauss (v : V)
    (m : proc.MeasLabel)
    (hm : ¬∃ r : Fin proc.d, m = FTGaugingMeasurement.phase2
        (DeformedCodeMeasurement.gaussLaw v r)) :
    (⟨m⟩ : TimeFault proc.MeasLabel) ∉ (gaussStringFault proc v).timeFaults := by
  rw [gaussStringFault_timeFaults_eq, mem_gaussMeasFaults]
  push_neg at hm ⊢
  intro r hr
  exact hm r (congr_arg TimeFault.measurement hr)

/-- The A_v string is syndrome-free with respect to all detectors from Lemma 4. -/
theorem gaussStringFault_syndromeFree (v : V) :
    IsSyndromeFreeGauging proc proc.detectorOfIndex (gaussStringFault proc v) := by
  intro idx
  cases idx with
  | phase1Repeated j r r' hr =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, phase1RepeatedDetector_parametric] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with rfl | rfl <;> simp
  | phase2GaussRepeated w r r' hr =>
    rw [Detector.isViolated_iff_flipParity]
    simp only [detectorOfIndex, phase2RepeatedDetector_gauss, Detector.flipParity]
    have hne : (FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r) :
        proc.MeasLabel) ≠
        FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r') := by
      simp [FTGaugingMeasurement.phase2.injEq, DeformedCodeMeasurement.gaussLaw.injEq]; omega
    rw [Finset.sum_pair hne]
    by_cases hvw : v = w
    · subst hvw
      simp only [gaussStringFault_mem_gauss, ite_true]
      simp [CharTwo.add_self_eq_zero]
    · have h1 : (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r)⟩ :
          TimeFault proc.MeasLabel) ∉ (gaussStringFault proc v).timeFaults :=
        gaussStringFault_no_other_gauss proc v w r hvw
      have h2 : (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw w r')⟩ :
          TimeFault proc.MeasLabel) ∉ (gaussStringFault proc v).timeFaults :=
        gaussStringFault_no_other_gauss proc v w r' hvw
      simp [h1, h2]
  | phase2FluxRepeated p r r' hr =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, phase2RepeatedDetector_flux, Finset.mem_insert,
      Finset.mem_singleton] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with rfl | rfl <;> simp
  | phase2DeformedRepeated j r r' hr =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, phase2RepeatedDetector_deformed, Finset.mem_insert,
      Finset.mem_singleton] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with rfl | rfl <;> simp
  | phase3Repeated j r r' hr =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, phase3RepeatedDetector] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with rfl | rfl <;> simp
  | fluxInit p =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, fluxInitDetector] at hm
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with ⟨_, _, rfl⟩ | rfl <;> simp
  | deformedInit j =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, deformedInitDetector] at hm
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with (rfl | rfl) | ⟨_, _, rfl⟩ <;> simp
  | fluxUngauge p =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, fluxUngaugeDetector] at hm
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with rfl | ⟨_, _, rfl⟩ <;> simp
  | deformedUngauge j =>
    apply not_isViolated_disjoint
    intro m hm
    simp only [detectorOfIndex, deformedUngaugeDetector] at hm
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    apply gauss_string_disjoint_nonGauss
    push_neg; intro r₀
    rcases hm with (rfl | rfl) | ⟨_, _, rfl⟩ <;> simp

/-! ## Part III: Upper Bound -/

/-- The A_v string is a gauging logical fault when d is odd. -/
theorem gaussStringFault_isLogicalFault (v : V) (hodd : Odd proc.d) :
    IsGaugingLogicalFault proc proc.detectorOfIndex
      (PreservesGaugingSign proc) (gaussStringFault proc v) := by
  constructor
  · exact gaussStringFault_syndromeFree proc v
  · rw [PreservesGaugingSign, gaussStringFault_signFlip]
    rw [hodd.natCast_zmod_two]
    exact one_ne_zero

/-- Upper bound: timeFaultDistance ≤ d when d is odd and V is nonempty. -/
theorem timeFaultDistance_le_d (v : V) (hodd : Odd proc.d) :
    timeFaultDistance proc proc.detectorOfIndex (PreservesGaugingSign proc) ≤ proc.d := by
  unfold timeFaultDistance
  apply Nat.sInf_le
  exact ⟨gaussStringFault proc v,
    ⟨gaussStringFault_isPureTime proc v,
     gaussStringFault_isLogicalFault proc v hodd⟩,
    gaussStringFault_weight_eq_d proc v⟩

/-! ## Part IV: Lower Bound -/

/-- For a pure-time fault, weight = timeFaults.card. -/
theorem pureTime_weight_eq_card
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureTime) :
    F.weight = F.timeFaults.card := by
  simp only [SpacetimeFault.weight, SpacetimeFault.isPureTime] at *
  rw [hpure, Finset.card_empty, zero_add]

/-- Gauss fault count for vertex v: number of A_v measurement faults across all rounds. -/
noncomputable def gaussFaultCount (v : V)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) : ℕ :=
  (Finset.univ.filter (fun r : Fin proc.d =>
    (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
      TimeFault proc.MeasLabel) ∈ F.timeFaults)).card

/-- The gaussSignFlip equals the sum of Gauss fault count parities. -/
theorem gaussSignFlip_eq_sum_parities
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) :
    gaussSignFlip proc F = ∑ v : V, (gaussFaultCount proc v F : ZMod 2) := by
  unfold gaussSignFlip gaussFaultCount
  congr 1; ext v
  rw [Finset.card_filter]
  simp only [Finset.sum_boole, Nat.cast_id]

/-! ### Consecutive round constraint -/

/-- For a syndrome-free fault, consecutive Gauss A_v rounds have the same fault status. -/
theorem syndromeFree_gauss_consecutive (v : V)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (r r' : Fin proc.d) (hr : r.val + 1 = r'.val) :
    ((⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults ↔
     (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r')⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults) := by
  have hdet := hfree (.phase2GaussRepeated v r r' hr)
  rw [Detector.isViolated_iff_flipParity] at hdet
  simp only [detectorOfIndex, phase2RepeatedDetector_gauss, Detector.flipParity] at hdet
  have hne : (FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r) :
      proc.MeasLabel) ≠
      FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r') := by
    simp [FTGaugingMeasurement.phase2.injEq, DeformedCodeMeasurement.gaussLaw.injEq]; omega
  rw [Finset.sum_pair hne] at hdet
  by_cases h1 : (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
      TimeFault proc.MeasLabel) ∈ F.timeFaults <;>
  by_cases h2 : (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r')⟩ :
      TimeFault proc.MeasLabel) ∈ F.timeFaults
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exfalso; simp [h1, h2] at hdet
  · exfalso; simp [h1, h2] at hdet
  · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

/-- All-or-none: for a syndrome-free fault, either all rounds of A_v are faulted or none are. -/
theorem syndromeFree_gauss_all_or_none (v : V)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (r r' : Fin proc.d) :
    ((⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults ↔
     (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r')⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults) := by
  suffices ∀ (a b : Fin proc.d), a.val ≤ b.val →
    ((⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v a)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults ↔
     (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v b)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults) by
    by_cases hle : r.val ≤ r'.val
    · exact this r r' hle
    · push_neg at hle; exact (this r' r (le_of_lt hle)).symm
  intro a b hab
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hab
  revert b
  induction k with
  | zero =>
    intro b hk hab
    have : a = b := Fin.ext (by omega)
    subst this; exact Iff.rfl
  | succ n ih =>
    intro b hk hab
    have hn_lt : a.val + n < proc.d := by omega
    have hn1_lt : a.val + n + 1 < proc.d := by omega
    have ih' := ih ⟨a.val + n, hn_lt⟩ (by simp [Fin.val_mk]) rfl
    have hcons := syndromeFree_gauss_consecutive proc v F hfree
      ⟨a.val + n, hn_lt⟩ ⟨a.val + n + 1, hn1_lt⟩ rfl
    have hbeq : b = ⟨a.val + n + 1, hn1_lt⟩ := Fin.ext (by simp [Fin.val_mk]; omega)
    rw [hbeq]
    exact ih'.trans hcons

/-- The Gauss fault count for each vertex is either 0 or d. -/
theorem gaussFaultCount_zero_or_d (v : V)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F) :
    gaussFaultCount proc v F = 0 ∨ gaussFaultCount proc v F = proc.d := by
  unfold gaussFaultCount
  by_cases hd : proc.d = 0
  · left; simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
      forall_const]; intro x; exact absurd x.isLt (by omega)
  · have hd_pos : 0 < proc.d := Nat.pos_of_ne_zero hd
    let r₀ : Fin proc.d := ⟨0, hd_pos⟩
    by_cases hfaulted : (⟨FTGaugingMeasurement.phase2
        (DeformedCodeMeasurement.gaussLaw v r₀)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults
    · right
      have hall : ∀ r : Fin proc.d,
          (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
            TimeFault proc.MeasLabel) ∈ F.timeFaults :=
        fun r => (syndromeFree_gauss_all_or_none proc v F hfree r₀ r).mp hfaulted
      have : Finset.univ.filter (fun r : Fin proc.d =>
          (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
            TimeFault proc.MeasLabel) ∈ F.timeFaults) = Finset.univ := by
        ext r; simp [hall r]
      rw [this]; exact Finset.card_fin proc.d
    · left
      have hnone : ∀ r : Fin proc.d,
          (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
            TimeFault proc.MeasLabel) ∉ F.timeFaults := by
        intro r hr
        exact hfaulted ((syndromeFree_gauss_all_or_none proc v F hfree r r₀).mp hr)
      have : Finset.univ.filter (fun r : Fin proc.d =>
          (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
            TimeFault proc.MeasLabel) ∈ F.timeFaults) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact fun r _ => hnone r
      rw [this]; exact Finset.card_empty

/-- Gauss fault parity for each vertex is either 0 or d (mod 2). -/
theorem gaussFaultParity_zero_or_d (v : V)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F) :
    (gaussFaultCount proc v F : ZMod 2) = 0 ∨
    (gaussFaultCount proc v F : ZMod 2) = (proc.d : ZMod 2) := by
  rcases gaussFaultCount_zero_or_d proc v F hfree with h | h
  · left; simp [h]
  · right; simp [h]

/-- For a syndrome-free fault that flips the sign with odd d: odd number of full A_v strings. -/
theorem sign_flip_implies_odd_full_strings
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hflip : FlipsGaugingSign proc F)
    (hodd : Odd proc.d) :
    Odd (Finset.univ.filter (fun v : V =>
      gaussFaultCount proc v F = proc.d)).card := by
  rw [FlipsGaugingSign] at hflip
  rw [gaussSignFlip_eq_sum_parities] at hflip
  have hd_mod : (proc.d : ZMod 2) = 1 := hodd.natCast_zmod_two
  have hparity_vals : ∀ v : V,
      (gaussFaultCount proc v F : ZMod 2) = 0 ∨
      (gaussFaultCount proc v F : ZMod 2) = 1 := by
    intro v
    rcases gaussFaultParity_zero_or_d proc v F hfree with h | h
    · left; exact h
    · right; rw [h, hd_mod]
  have hsum_eq_card : ∑ v : V, (gaussFaultCount proc v F : ZMod 2) =
      ((Finset.univ.filter (fun v : V =>
        (gaussFaultCount proc v F : ZMod 2) = 1)).card : ZMod 2) := by
    rw [Finset.card_filter]
    push_cast
    congr 1; funext v
    rcases hparity_vals v with h | h
    · simp [h]
    · simp [h]
  rw [hsum_eq_card] at hflip
  have hfilter_eq : Finset.univ.filter (fun v : V =>
        (gaussFaultCount proc v F : ZMod 2) = 1) =
      Finset.univ.filter (fun v : V => gaussFaultCount proc v F = proc.d) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp
      rcases gaussFaultCount_zero_or_d proc v F hfree with h | h
      · exfalso; simp [h] at hp
      · exact h
    · intro hc; simp [hc, hd_mod]
  rw [hfilter_eq] at hflip
  rwa [ZMod.natCast_eq_one_iff_odd] at hflip

/-- The total Gauss fault count ≤ weight for a pure-time fault. -/
theorem pureTime_weight_ge_gauss_sum
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureTime) :
    ∑ v : V, gaussFaultCount proc v F ≤ F.weight := by
  rw [pureTime_weight_eq_card proc F hpure]
  unfold gaussFaultCount
  -- The biUnion of mapped Gauss faults is a subset of F.timeFaults
  have hle : (Finset.univ.biUnion (fun v : V =>
      (Finset.univ.filter (fun r : Fin proc.d =>
        (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
          TimeFault proc.MeasLabel) ∈ F.timeFaults)).image
        (fun r => (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
          TimeFault proc.MeasLabel)))).card ≤ F.timeFaults.card := by
    apply Finset.card_le_card
    intro tf htf
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_filter] at htf
    obtain ⟨_, _, hmem, rfl⟩ := htf
    exact hmem
  have heq : ∑ v : V, (Finset.univ.filter (fun r : Fin proc.d =>
      (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
        TimeFault proc.MeasLabel) ∈ F.timeFaults)).card =
      (Finset.univ.biUnion (fun v : V =>
        (Finset.univ.filter (fun r : Fin proc.d =>
          (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
            TimeFault proc.MeasLabel) ∈ F.timeFaults)).image
          (fun r => (⟨FTGaugingMeasurement.phase2 (DeformedCodeMeasurement.gaussLaw v r)⟩ :
            TimeFault proc.MeasLabel)))).card := by
    rw [Finset.card_biUnion]
    · congr 1; ext v
      rw [Finset.card_image_of_injective]
      intro r₁ r₂ h
      simp only [TimeFault.mk.injEq, FTGaugingMeasurement.phase2.injEq,
        DeformedCodeMeasurement.gaussLaw.injEq] at h
      exact h.2
    · intro v₁ _ v₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro tf htf1 htf2
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at htf1 htf2
      obtain ⟨_, _, rfl⟩ := htf1
      obtain ⟨_, _, h⟩ := htf2
      simp only [TimeFault.mk.injEq, FTGaugingMeasurement.phase2.injEq,
        DeformedCodeMeasurement.gaussLaw.injEq] at h
      exact hne h.1.symm
  linarith

/-- A pure-time fault with a full A_v string has weight ≥ d. -/
theorem pureTime_weight_ge_d_of_full_string
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : F.isPureTime)
    (v : V) (hv : gaussFaultCount proc v F = proc.d) :
    proc.d ≤ F.weight := by
  calc proc.d = gaussFaultCount proc v F := hv.symm
    _ ≤ ∑ w : V, gaussFaultCount proc w F :=
        Finset.single_le_sum (f := fun w => gaussFaultCount proc w F)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    _ ≤ F.weight := pureTime_weight_ge_gauss_sum proc F hpure

/-- **Lower bound**: Any pure-time logical fault has weight ≥ d (when d is odd). -/
theorem pureTime_logicalFault_weight_ge_d
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : IsPureTimeFault proc F)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hflip : FlipsGaugingSign proc F)
    (hodd : Odd proc.d) :
    proc.d ≤ F.weight := by
  have hodd_strings := sign_flip_implies_odd_full_strings proc F hfree hflip hodd
  have hne : (Finset.univ.filter (fun v : V =>
      gaussFaultCount proc v F = proc.d)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    simp [hempty] at hodd_strings
  obtain ⟨v, hv⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact pureTime_weight_ge_d_of_full_string proc F hpure v hv

/-! ## Part V: Main Theorem -/

/-- **Lower bound for time fault-distance**: timeFaultDistance ≥ d. -/
theorem timeFaultDistance_ge_d (hodd : Odd proc.d) (hV : Nonempty V) :
    proc.d ≤ timeFaultDistance proc proc.detectorOfIndex (PreservesGaugingSign proc) := by
  unfold timeFaultDistance
  by_cases hempty : (pureTimeLogicalFaultWeights proc proc.detectorOfIndex
      (PreservesGaugingSign proc)).Nonempty
  · apply le_csInf hempty
    intro w ⟨F, ⟨hpure, hlog⟩, hw⟩
    rw [← hw]
    have hfree := hlog.1
    have hnotpres := hlog.2
    have hflip : FlipsGaugingSign proc F := by
      rw [PreservesGaugingSign] at hnotpres
      rcases gaussSignFlip_zero_or_one proc F with h | h
      · exact absurd h hnotpres
      · exact h
    exact pureTime_logicalFault_weight_ge_d proc F hpure hfree hflip hodd
  · -- No pure-time logical faults: impossible since the A_v string exists
    exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have : proc.d ∈ pureTimeLogicalFaultWeights proc proc.detectorOfIndex
        (PreservesGaugingSign proc) := by
      obtain ⟨v⟩ := hV
      exact ⟨gaussStringFault proc v,
        ⟨gaussStringFault_isPureTime proc v,
         gaussStringFault_isLogicalFault proc v hodd⟩,
        gaussStringFault_weight_eq_d proc v⟩
    rw [hempty] at this
    exact this

/-- **Lemma 6 (Time Fault-Distance): timeFaultDistance = d.** -/
theorem timeFaultDistance_eq_d (v : V) (hodd : Odd proc.d) (hV : Nonempty V) :
    timeFaultDistance proc proc.detectorOfIndex (PreservesGaugingSign proc) = proc.d := by
  apply le_antisymm
  · exact timeFaultDistance_le_d proc v hodd
  · exact timeFaultDistance_ge_d proc hodd hV

/-! ## Part V-b: Justification of the Outcome Predicate (Paper Step 5, second bullet)

The paper's proof (Step 5) shows that for pure-time faults, `PreservesGaugingSign` is the
correct outcome predicate. Specifically: every syndrome-free pure-time fault that does NOT
flip σ decomposes into the spacetime stabilizer generators from Lemma 5 (B_p measurement
pairs, s̃_j measurement pairs, and boundary initialization/readout faults). Since these
generators preserve the gauging outcome by `listedGenerator_isGaugingStabilizer` (Lem 5),
they are trivial logical faults.

This section proves this equivalence, connecting our use of `PreservesGaugingSign proc`
to the paper's full argument.
-/

/-- Every syndrome-free pure-time fault that preserves the Gauss sign is a gauging stabilizer
    that decomposes into Lemma 5's listed generators. This is the mathematical content of
    Step 5 (second bullet) of the paper's proof: non-σ-flipping syndrome-free pure-time faults
    are products of spacetime stabilizers (B_p/s̃_j measurement pairs and boundary faults),
    hence trivial. -/
theorem pureTime_preservesSign_decomposes_into_generators
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (_hpure : IsPureTimeFault proc F)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hpres : PreservesGaugingSign proc F) :
    ∃ gens : List (SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel),
      (∀ g ∈ gens, IsListedGenerator proc g) ∧
      F = gens.foldl SpacetimeFault.compose SpacetimeFault.empty :=
  spacetimeStabilizer_completeness proc F ⟨hfree, hpres⟩

/-- For syndrome-free pure-time faults, the dichotomy from Def 11 specializes to:
    either the fault flips σ (logical fault), or it decomposes into Lemma 5's
    stabilizer generators (trivial fault). This justifies using `PreservesGaugingSign`
    as the `outcomePreserving` predicate in the time fault-distance definition. -/
theorem pureTime_syndromeFree_logical_or_stabilizer_generators
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : IsPureTimeFault proc F)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F) :
    FlipsGaugingSign proc F ∨
    (PreservesGaugingSign proc F ∧
     ∃ gens : List (SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel),
       (∀ g ∈ gens, IsListedGenerator proc g) ∧
       F = gens.foldl SpacetimeFault.compose SpacetimeFault.empty) := by
  rcases flipsOrPreserves proc F with hflip | hpres
  · left; exact hflip
  · right
    exact ⟨hpres, pureTime_preservesSign_decomposes_into_generators proc F hpure hfree hpres⟩

/-! ## Part VI: Corollaries -/

/-- Any pure-time fault of weight < d is a gauging stabilizer (when d is odd). -/
theorem pureTime_weight_lt_d_is_stabilizer
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : IsPureTimeFault proc F)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hw : F.weight < proc.d)
    (hodd : Odd proc.d) :
    IsGaugingStabilizer proc proc.detectorOfIndex (PreservesGaugingSign proc) F := by
  refine ⟨hfree, ?_⟩
  by_contra hnotpres
  rw [PreservesGaugingSign] at hnotpres
  have hflip : FlipsGaugingSign proc F := by
    rcases gaussSignFlip_zero_or_one proc F with h | h
    · exact absurd h hnotpres
    · exact h
  have hge := pureTime_logicalFault_weight_ge_d proc F hpure hfree hflip hodd
  omega

/-- The Gauss fault count dichotomy (rephrased). -/
theorem gaussFaultCount_dichotomy (v : V)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F) :
    gaussFaultCount proc v F = 0 ∨ gaussFaultCount proc v F = proc.d :=
  gaussFaultCount_zero_or_d proc v F hfree

/-- The time fault-distance equals the Phase 2 duration t_o - t_i. -/
theorem timeFaultDistance_eq_phase2_duration (v : V) (hodd : Odd proc.d) (hV : Nonempty V) :
    timeFaultDistance proc proc.detectorOfIndex (PreservesGaugingSign proc) =
    proc.phase3Start - proc.phase2Start := by
  rw [timeFaultDistance_eq_d proc v hodd hV, phase2_duration]

/-- Minimum-weight pure-time logical faults have exactly one full A_v string. -/
theorem minimum_weight_is_single_string
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hpure : IsPureTimeFault proc F)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hflip : FlipsGaugingSign proc F)
    (hw : F.weight = proc.d)
    (hodd : Odd proc.d) :
    (Finset.univ.filter (fun v : V =>
      gaussFaultCount proc v F = proc.d)).card = 1 := by
  have hodd_strings := sign_flip_implies_odd_full_strings proc F hfree hflip hodd
  have hne : (Finset.univ.filter (fun v : V =>
      gaussFaultCount proc v F = proc.d)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty; simp [hempty] at hodd_strings
  have hle_one : (Finset.univ.filter (fun v : V =>
      gaussFaultCount proc v F = proc.d)).card ≤ 1 := by
    by_contra h
    push_neg at h
    rw [Finset.one_lt_card_iff] at h
    obtain ⟨v₁, v₂, hv₁m, hv₂m, hne_v⟩ := h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₁m hv₂m
    have hpair : gaussFaultCount proc v₁ F + gaussFaultCount proc v₂ F ≤
        ∑ w : V, gaussFaultCount proc w F := by
      have : gaussFaultCount proc v₁ F + gaussFaultCount proc v₂ F =
          ∑ w ∈ ({v₁, v₂} : Finset V), gaussFaultCount proc w F :=
        (Finset.sum_pair (f := fun w => gaussFaultCount proc w F) hne_v).symm
      rw [this]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [hv₁m, hv₂m] at hpair
    have hge_weight := pureTime_weight_ge_gauss_sum proc F hpure
    have hd_pos : 0 < proc.d := Odd.pos hodd
    omega
  have hge_one : 1 ≤ (Finset.univ.filter (fun v : V =>
      gaussFaultCount proc v F = proc.d)).card :=
    Finset.card_pos.mpr hne
  omega

end TimeFaultDistance
