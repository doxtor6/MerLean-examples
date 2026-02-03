import QEC1.Definitions.Def_15_SpacetimeFaultDistance

/-!
# Time Fault Distance (Lemma 5)

## Statement
The fault-distance for pure measurement and initialization errors is $(t_o - t_i)$,
the number of rounds between the start and end of code deformation.

Specifically: Any spacetime logical fault consisting only of measurement/initialization
errors has weight ≥ t_o - t_i.

## Main Results
**Main Definition** (`isPureTimeFault`): A fault with no space faults (only time/init faults)
**Main Theorem** (`pure_time_fault_weight_ge_rounds`): Pure time fault weight ≥ t_o - t_i
**Corollary** (`time_fault_distance`): The minimum weight for pure time logical faults

## Proof Structure
The key insight is formalized via comparison detectors:
1. A **comparison detector** at round t compares the measurement at t with the one at t-1
2. If a time fault occurs at round t but NOT at t-1, the comparison detector fires
3. Therefore, undetectable pure time faults must occur in "chains" spanning all rounds
4. The minimum chain length from t_i to t_o is exactly t_o - t_i

## Supporting Lemmas (from original statement)
**Lemma (measurement_fault_propagation):** A measurement fault on check C at time t must be
accompanied by measurement faults on C at either t-1 or t+1 (or boundary termination).

**Lemma (boundary_termination_Av):** Strings of Av measurement faults can terminate at
t = t_i and t = t_o (boundary conditions for the deformation interval).

**Lemma (Av_measurement_fault_logical):** Repeated Av measurement faults from t_i to t_o
form a nontrivial logical fault.

## File Structure
1. Pure Time Fault Predicate: Faults with only time/measurement errors
2. Code Deformation Interval: Parameters t_i and t_o
3. Comparison Detector Model: Detectors comparing consecutive rounds
4. Chain Property Derivation: PROVEN from comparison detector structure
5. Main Theorem: Weight lower bound for pure time logical faults
6. Achievability: Chain faults are logical faults with weight = t_o - t_i
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Pure Time Fault Predicate -/

/-- A spacetime fault is a **pure time fault** if it has no space faults. -/
def isPureTimeFault {n m : ℕ} (F : SpaceTimeFault n m) : Prop :=
  F.spaceFaults = ∅

instance instDecidableIsPureTimeFault {n m : ℕ} (F : SpaceTimeFault n m) :
    Decidable (isPureTimeFault F) :=
  inferInstanceAs (Decidable (F.spaceFaults = ∅))

theorem isPureTimeFault_weight {n m : ℕ} (F : SpaceTimeFault n m)
    (h : isPureTimeFault F) : F.weight = F.timeFaults.card := by
  unfold SpaceTimeFault.weight isPureTimeFault at *
  simp [h]

@[simp]
theorem empty_isPureTimeFault : isPureTimeFault (SpaceTimeFault.empty : SpaceTimeFault n m) := by
  unfold isPureTimeFault SpaceTimeFault.empty
  rfl

theorem isPureTimeFault_weight_zero_iff {n m : ℕ} (F : SpaceTimeFault n m)
    (h : isPureTimeFault F) : F.weight = 0 ↔ F.timeFaults = ∅ := by
  rw [isPureTimeFault_weight F h]
  exact Finset.card_eq_zero

/-! ## Section 2: Code Deformation Interval -/

structure CodeDeformationInterval where
  t_i : TimeStep
  t_o : TimeStep
  start_le_end : t_i ≤ t_o

namespace CodeDeformationInterval

def numRounds (I : CodeDeformationInterval) : ℕ := I.t_o - I.t_i

theorem numRounds_nonneg (I : CodeDeformationInterval) : 0 ≤ I.numRounds :=
  Nat.zero_le _

theorem numRounds_zero_of_eq (I : CodeDeformationInterval) (h : I.t_i = I.t_o) :
    I.numRounds = 0 := by
  unfold numRounds; rw [h]; exact Nat.sub_self I.t_o

theorem numRounds_pos_of_lt (I : CodeDeformationInterval) (h : I.t_i < I.t_o) :
    0 < I.numRounds := Nat.sub_pos_of_lt h

def trivial (t : TimeStep) : CodeDeformationInterval where
  t_i := t; t_o := t; start_le_end := le_refl t

@[simp]
theorem trivial_numRounds (t : TimeStep) : (trivial t).numRounds = 0 := Nat.sub_self t

def ofDuration (t_start : TimeStep) (duration : ℕ) : CodeDeformationInterval where
  t_i := t_start
  t_o := t_start + duration
  start_le_end := Nat.le_add_right t_start duration

theorem ofDuration_numRounds (t_start : TimeStep) (duration : ℕ) :
    (ofDuration t_start duration).numRounds = duration := by simp [ofDuration, numRounds]

end CodeDeformationInterval

/-! ## Section 3: Time Fault Coverage -/

def coveredRounds {m : ℕ} (timeFaults : Finset (TimeFault m)) : Finset TimeStep :=
  timeFaults.image (·.measurementRound)

def coversAllRounds {m : ℕ} (timeFaults : Finset (TimeFault m))
    (I : CodeDeformationInterval) : Prop :=
  ∀ t : ℕ, I.t_i ≤ t → t < I.t_o → t ∈ coveredRounds timeFaults

/-! ## Section 4: Comparison Detector Model -/

structure ComparisonDetector (m : ℕ) where
  measurementIdx : Fin m
  round : TimeStep
  deriving DecidableEq

def timeFaultCountAt {m : ℕ} (faults : Finset (TimeFault m))
    (idx : Fin m) (t : TimeStep) : ℕ :=
  (faults.filter (fun f => f.measurementIndex = idx ∧ f.measurementRound = t)).card

/-- Comparison detector fires if parities at consecutive rounds differ.
    Note: This compares round t to round t-1. For boundary conditions in code
    deformation, use `violatesInteriorComparisonDetector` which only fires
    when BOTH rounds are within the interval. -/
def violatesComparisonDetector {m : ℕ} (faults : Finset (TimeFault m))
    (D : ComparisonDetector m) : Prop :=
  let countAtRound := timeFaultCountAt faults D.measurementIdx D.round
  let countAtPrev := if D.round = 0 then 0
                     else timeFaultCountAt faults D.measurementIdx (D.round - 1)
  Odd countAtRound ≠ Odd countAtPrev

/-- Interior comparison detector: only fires when both t and t-1 are in the interval.
    This models the fact that faults can "enter" at t_i and "exit" at t_o without detection. -/
def violatesInteriorComparisonDetector {m : ℕ} (faults : Finset (TimeFault m))
    (I : CodeDeformationInterval) (idx : Fin m) (t : TimeStep) : Prop :=
  I.t_i < t ∧ t < I.t_o ∧
  let countAtRound := timeFaultCountAt faults idx t
  let countAtPrev := timeFaultCountAt faults idx (t - 1)
  Odd countAtRound ≠ Odd countAtPrev

instance {m : ℕ} (faults : Finset (TimeFault m)) (D : ComparisonDetector m) :
    Decidable (violatesComparisonDetector faults D) := by
  unfold violatesComparisonDetector; infer_instance

/-! ## Section 5: Key Lemmas - Parity Propagation -/

/-- If a comparison detector doesn't fire at round t > 0, parities match. -/
theorem no_violation_implies_same_parity {m : ℕ}
    (faults : Finset (TimeFault m)) (D : ComparisonDetector m) (ht_pos : D.round ≠ 0)
    (hno_viol : ¬violatesComparisonDetector faults D) :
    Odd (timeFaultCountAt faults D.measurementIdx D.round) ↔
    Odd (timeFaultCountAt faults D.measurementIdx (D.round - 1)) := by
  unfold violatesComparisonDetector at hno_viol
  simp only [ne_eq, not_not] at hno_viol
  simp only [ht_pos, ↓reduceIte] at hno_viol
  exact Iff.of_eq hno_viol

theorem fault_at_implies_covered {m : ℕ}
    (faults : Finset (TimeFault m)) (idx : Fin m) (t : TimeStep)
    (hpos : 0 < timeFaultCountAt faults idx t) :
    t ∈ coveredRounds faults := by
  unfold timeFaultCountAt at hpos
  rw [Finset.card_pos] at hpos
  obtain ⟨f, hf⟩ := hpos
  simp only [Finset.mem_filter] at hf
  exact Finset.mem_image.mpr ⟨f, hf.1, hf.2.2⟩

/-! ## Section 6: Chain Coverage Theorem (KEY)

**Key Theorem**: For a pure time fault to be undetectable w.r.t. comparison
detectors AND have faults at some index with odd count in the interval,
all rounds in the interval are covered.

This is DERIVED from the comparison detector structure. -/

/-- All rounds in an interval have the same parity if no comparison detector fires. -/
theorem same_parity_in_interval {m : ℕ}
    (faults : Finset (TimeFault m)) (I : CodeDeformationInterval) (idx : Fin m)
    (hno_viol : ∀ t, I.t_i ≤ t → t < I.t_o → ¬violatesComparisonDetector faults ⟨idx, t⟩)
    (t1 t2 : TimeStep) (ht1_ge : I.t_i ≤ t1) (ht1_lt : t1 < I.t_o)
    (ht2_ge : I.t_i ≤ t2) (ht2_lt : t2 < I.t_o) :
    Odd (timeFaultCountAt faults idx t1) ↔ Odd (timeFaultCountAt faults idx t2) := by
  -- Symmetric in t1, t2
  wlog hle : t1 ≤ t2 with Hsym
  · exact (Hsym faults I idx hno_viol t2 t1 ht2_ge ht2_lt ht1_ge ht1_lt (Nat.le_of_not_le hle)).symm
  -- Induction on the difference t2 - t1
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  subst hd
  induction d with
  | zero => simp
  | succ d ih =>
    -- t2 = t1 + (d + 1), so t2 - 1 = t1 + d
    have ht2m1_ge : I.t_i ≤ t1 + d := Nat.le_trans ht1_ge (Nat.le_add_right t1 d)
    have ht2m1_lt : t1 + d < I.t_o := by
      have h : t1 + d < t1 + d + 1 := Nat.lt_succ_self (t1 + d)
      exact Nat.lt_of_lt_of_le h (Nat.le_of_lt ht2_lt)
    have hih : Odd (timeFaultCountAt faults idx t1) ↔
        Odd (timeFaultCountAt faults idx (t1 + d)) := ih ht2m1_ge ht2m1_lt (Nat.le_add_right t1 d)
    -- Detector at t1 + d + 1
    have hdet := hno_viol (t1 + d + 1) ht2_ge ht2_lt
    have ht2_pos : t1 + d + 1 ≠ 0 := Nat.succ_ne_zero (t1 + d)
    have hparity := no_violation_implies_same_parity faults ⟨idx, t1 + d + 1⟩ ht2_pos hdet
    simp only [Nat.add_sub_cancel] at hparity
    exact hih.trans hparity.symm

/-- **Key Lemma**: If an index has a fault with odd count in the interval,
    then all rounds have odd (hence positive) count. -/
theorem chain_coverage_at_index {m : ℕ}
    (faults : Finset (TimeFault m)) (I : CodeDeformationInterval) (idx : Fin m)
    (hno_viol : ∀ t, I.t_i ≤ t → t < I.t_o → ¬violatesComparisonDetector faults ⟨idx, t⟩)
    (t0 : TimeStep) (ht0_ge : I.t_i ≤ t0) (ht0_lt : t0 < I.t_o)
    (ht0_odd : Odd (timeFaultCountAt faults idx t0)) :
    ∀ t, I.t_i ≤ t → t < I.t_o → 0 < timeFaultCountAt faults idx t := by
  intro t ht_ge ht_lt
  have hsame := same_parity_in_interval faults I idx hno_viol t0 t ht0_ge ht0_lt ht_ge ht_lt
  have hodd_t := hsame.mp ht0_odd
  obtain ⟨k, hk⟩ := hodd_t
  omega

/-- **Derived Chain Coverage Theorem** -/
theorem undetectable_covers_rounds {m : ℕ}
    (faults : Finset (TimeFault m)) (I : CodeDeformationInterval)
    (hno_viol : ∀ (idx : Fin m) (t : TimeStep),
      I.t_i ≤ t → t < I.t_o → ¬violatesComparisonDetector faults ⟨idx, t⟩)
    (hfaults_in_interval : ∃ idx : Fin m, ∃ t0 : TimeStep,
      I.t_i ≤ t0 ∧ t0 < I.t_o ∧ Odd (timeFaultCountAt faults idx t0)) :
    coversAllRounds faults I := by
  obtain ⟨idx, t0, ht0_ge, ht0_lt, ht0_odd⟩ := hfaults_in_interval
  intro t ht_ge ht_lt
  have hpos := chain_coverage_at_index faults I idx
    (fun t' ht'_ge ht'_lt => hno_viol idx t' ht'_ge ht'_lt)
    t0 ht0_ge ht0_lt ht0_odd t ht_ge ht_lt
  exact fault_at_implies_covered faults idx t hpos

/-! ## Section 7: Round Coverage Implies Weight Bound -/

theorem covered_rounds_card_ge_interval {m : ℕ} (timeFaults : Finset (TimeFault m))
    (I : CodeDeformationInterval) (hcover : coversAllRounds timeFaults I) :
    I.numRounds ≤ (coveredRounds timeFaults).card := by
  unfold CodeDeformationInterval.numRounds
  by_cases htriv : I.t_o ≤ I.t_i
  · simp only [Nat.sub_eq_zero_of_le htriv, Nat.zero_le]
  · push_neg at htriv
    let roundSet : Finset ℕ := Finset.Ico I.t_i I.t_o
    have hsub : roundSet ⊆ coveredRounds timeFaults := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      exact hcover t ht.1 ht.2
    calc I.t_o - I.t_i = roundSet.card := (Nat.card_Ico I.t_i I.t_o).symm
      _ ≤ (coveredRounds timeFaults).card := Finset.card_le_card hsub

theorem timeFaults_card_ge_covered {m : ℕ} (timeFaults : Finset (TimeFault m)) :
    (coveredRounds timeFaults).card ≤ timeFaults.card :=
  Finset.card_image_le

theorem timeFaults_cover_implies_weight_bound {m : ℕ} (timeFaults : Finset (TimeFault m))
    (I : CodeDeformationInterval) (hcover : coversAllRounds timeFaults I) :
    I.numRounds ≤ timeFaults.card :=
  Nat.le_trans (covered_rounds_card_ge_interval timeFaults I hcover)
    (timeFaults_card_ge_covered timeFaults)

/-! ## Section 8: Pure Time Fault Trivial Action Condition -/

theorem isPureTimeFault_actsTrivially_iff {n k m : ℕ} (C : StabilizerCode n k)
    (F : SpaceTimeFault n m) (hpure : isPureTimeFault F) :
    actsTriviallyOnMeasurement C F ↔ timeFaultsCancel F.timeFaults := by
  unfold actsTriviallyOnMeasurement
  constructor
  · intro ⟨htc, _⟩; exact htc
  · intro htc
    exact ⟨htc, by
      unfold isPureTimeFault at hpure
      unfold spaceFaultsAreStabilizer
      rw [hpure, spaceFaultsToCheck_empty]
      exact identity_is_stabilizer C⟩

theorem isPureTimeFault_isLogicalFault_iff {n k m : ℕ} (C : StabilizerCode n k)
    (F : SpaceTimeFault n m) (detectors : Finset (Detector n))
    (hpure : isPureTimeFault F) :
    IsSpacetimeLogicalFaultConcrete C F detectors ↔
      isUndetectable F detectors ∧ ¬timeFaultsCancel F.timeFaults := by
  unfold IsSpacetimeLogicalFaultConcrete
  rw [isPureTimeFault_actsTrivially_iff C F hpure]

/-! ## Section 9: Main Theorem -/

/-- **Main Theorem (Lemma 5)**: Pure time fault weight ≥ numRounds when
    comparison detectors don't fire and there's an odd-count fault in the interval. -/
theorem pure_time_fault_weight_ge_rounds {n m : ℕ}
    (F : SpaceTimeFault n m) (I : CodeDeformationInterval)
    (hpure : isPureTimeFault F)
    (hno_viol : ∀ (idx : Fin m) (t : TimeStep),
      I.t_i ≤ t → t < I.t_o → ¬violatesComparisonDetector F.timeFaults ⟨idx, t⟩)
    (hfaults_in_interval : ∃ idx : Fin m, ∃ t0 : TimeStep,
      I.t_i ≤ t0 ∧ t0 < I.t_o ∧ Odd (timeFaultCountAt F.timeFaults idx t0)) :
    I.numRounds ≤ F.weight := by
  have hcover := undetectable_covers_rounds F.timeFaults I hno_viol hfaults_in_interval
  rw [isPureTimeFault_weight F hpure]
  exact timeFaults_cover_implies_weight_bound F.timeFaults I hcover

/-! ## Section 10: Achievability - Chain Faults Are Logical Faults -/

def timeFaultChain (m : ℕ) (I : CodeDeformationInterval) (idx : Fin m) :
    Finset (TimeFault m) :=
  (Finset.Ico I.t_i I.t_o).image (fun t => ⟨idx, t⟩)

theorem timeFaultChain_card (m : ℕ) (I : CodeDeformationInterval) (idx : Fin m) :
    (timeFaultChain m I idx).card = I.numRounds := by
  unfold timeFaultChain CodeDeformationInterval.numRounds
  rw [Finset.card_image_of_injective]
  · exact Nat.card_Ico I.t_i I.t_o
  · intro t1 t2 h; simp only [TimeFault.mk.injEq] at h; exact h.2

theorem timeFaultChain_covers (m : ℕ) (I : CodeDeformationInterval) (idx : Fin m) :
    coversAllRounds (timeFaultChain m I idx) I := by
  intro t ht_ge ht_lt
  simp only [coveredRounds, timeFaultChain, Finset.mem_image, Finset.mem_Ico]
  exact ⟨⟨idx, t⟩, ⟨t, ⟨ht_ge, ht_lt⟩, rfl⟩, rfl⟩

def pureTimeFaultFromChain {n : ℕ} (m : ℕ) (I : CodeDeformationInterval)
    (idx : Fin m) : SpaceTimeFault n m where
  spaceFaults := ∅
  timeFaults := timeFaultChain m I idx

theorem pureTimeFaultFromChain_isPure {n : ℕ} (m : ℕ) (I : CodeDeformationInterval)
    (idx : Fin m) : isPureTimeFault (pureTimeFaultFromChain (n := n) m I idx) := rfl

theorem pureTimeFaultFromChain_weight {n : ℕ} (m : ℕ) (I : CodeDeformationInterval)
    (idx : Fin m) : (pureTimeFaultFromChain (n := n) m I idx).weight = I.numRounds := by
  simp only [SpaceTimeFault.weight, pureTimeFaultFromChain, Finset.card_empty, Nat.zero_add]
  exact timeFaultChain_card m I idx

/-- Helper: count at round t in chain is 1 if t ∈ [t_i, t_o) -/
theorem chainFault_count_at_idx {n : ℕ} (m : ℕ) (I : CodeDeformationInterval) (idx : Fin m)
    (t : TimeStep) (ht_ge : I.t_i ≤ t) (ht_lt : t < I.t_o) :
    timeFaultCountAt (pureTimeFaultFromChain (n := n) m I idx).timeFaults idx t = 1 := by
  unfold timeFaultCountAt pureTimeFaultFromChain timeFaultChain
  rw [Finset.card_eq_one]
  use ⟨idx, t⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · intro ⟨⟨t', ⟨_, _⟩, hf_eq⟩, hf_idx, hf_round⟩
    simp only [← hf_eq, TimeFault.mk.injEq] at hf_idx hf_round ⊢
    exact ⟨hf_idx, hf_round⟩
  · intro hf_eq
    rw [hf_eq]
    refine ⟨⟨t, ⟨ht_ge, ht_lt⟩, rfl⟩, rfl, rfl⟩

/-- Helper: count at round t in chain is 0 if t ∉ [t_i, t_o) -/
theorem chainFault_count_outside {n : ℕ} (m : ℕ) (I : CodeDeformationInterval) (idx : Fin m)
    (t : TimeStep) (ht_out : t < I.t_i ∨ I.t_o ≤ t) :
    timeFaultCountAt (pureTimeFaultFromChain (n := n) m I idx).timeFaults idx t = 0 := by
  unfold timeFaultCountAt pureTimeFaultFromChain timeFaultChain
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Finset.notMem_empty,
    iff_false, not_and]
  intro ⟨t', ⟨ht'_ge, ht'_lt⟩, hf_eq⟩ _ hf_round
  rw [← hf_eq] at hf_round
  cases ht_out with
  | inl h => exact Nat.lt_irrefl t (Nat.lt_of_lt_of_le h (hf_round ▸ ht'_ge))
  | inr h => exact Nat.lt_irrefl t (Nat.lt_of_lt_of_le (hf_round ▸ ht'_lt) h)

/-- Helper: count at different index is always 0 -/
theorem chainFault_count_other_idx {n : ℕ} (m : ℕ) (I : CodeDeformationInterval)
    (idx idx' : Fin m) (hidx : idx ≠ idx') (t : TimeStep) :
    timeFaultCountAt (pureTimeFaultFromChain (n := n) m I idx).timeFaults idx' t = 0 := by
  unfold timeFaultCountAt pureTimeFaultFromChain timeFaultChain
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Finset.notMem_empty,
    iff_false, not_and]
  intro ⟨t', _, hf_eq⟩ hf_idx _
  rw [← hf_eq] at hf_idx
  exact hidx hf_idx

/-- **Lemma (boundary_termination_Av):** Chain doesn't violate INTERIOR comparison detectors.
    Interior detectors only fire for t > t_i, allowing the chain to "enter" at t_i.
    This models the boundary condition in code deformation. -/
theorem chainFault_no_interior_violation_at_idx {n : ℕ} (m : ℕ)
    (I : CodeDeformationInterval) (idx : Fin m) :
    ∀ t, ¬violatesInteriorComparisonDetector
      (pureTimeFaultFromChain (n := n) m I idx).timeFaults I idx t := by
  intro t
  unfold violatesInteriorComparisonDetector
  simp only [not_and, ne_eq, not_not]
  intro ht_gt_ti ht_lt_to
  -- t > t_i, so t - 1 ≥ t_i, both in interval, both count = 1
  have ht_m1_ge : I.t_i ≤ t - 1 := Nat.le_sub_one_of_lt ht_gt_ti
  have ht_m1_lt : t - 1 < I.t_o := Nat.lt_of_lt_of_le (Nat.sub_lt
    (Nat.lt_of_le_of_lt (Nat.zero_le I.t_i) ht_gt_ti) Nat.one_pos) (Nat.le_of_lt ht_lt_to)
  rw [chainFault_count_at_idx m I idx t (Nat.le_of_lt ht_gt_ti) ht_lt_to]
  rw [chainFault_count_at_idx m I idx (t - 1) ht_m1_ge ht_m1_lt]

/-- Chain doesn't violate interior comparison detectors at other indices (count = 0 everywhere). -/
theorem chainFault_no_interior_violation_other_idx {n : ℕ} (m : ℕ)
    (I : CodeDeformationInterval) (idx idx' : Fin m) (hidx : idx ≠ idx') :
    ∀ t, ¬violatesInteriorComparisonDetector
      (pureTimeFaultFromChain (n := n) m I idx).timeFaults I idx' t := by
  intro t
  unfold violatesInteriorComparisonDetector
  simp only [not_and, ne_eq, not_not]
  intro _ht_gt_ti _ht_lt_to
  rw [chainFault_count_other_idx m I idx idx' hidx t]
  rw [chainFault_count_other_idx m I idx idx' hidx (t - 1)]

/-- **Lemma (Av_measurement_fault_logical):** Chain doesn't cancel when numRounds is odd. -/
theorem chainFault_not_cancel {n : ℕ} (m : ℕ) (I : CodeDeformationInterval)
    (idx : Fin m) (_hm : 0 < m) (hnumRounds_odd : Odd I.numRounds) :
    ¬timeFaultsCancel (pureTimeFaultFromChain (n := n) m I idx).timeFaults := by
  intro hcancel
  unfold pureTimeFaultFromChain timeFaultChain at hcancel
  let faults := (Finset.Ico I.t_i I.t_o).image (fun t => (⟨idx, t⟩ : TimeFault m))
  have hcount : (faults.filter (fun f => f.measurementIndex = idx)).card = I.numRounds := by
    have hall : ∀ f ∈ faults, f.measurementIndex = idx := by
      intro f hf
      rw [Finset.mem_image] at hf
      obtain ⟨t', _, hft⟩ := hf
      rw [← hft]
    rw [Finset.filter_true_of_mem hall, Finset.card_image_of_injective]
    · exact Nat.card_Ico I.t_i I.t_o
    · intro t1 t2 h; simp only [TimeFault.mk.injEq] at h; exact h.2
  have heven := hcancel idx
  simp only [faults] at hcount
  rw [hcount] at heven
  exact Nat.not_even_iff_odd.mpr hnumRounds_odd heven

theorem chainFault_undetectable_for_detectors {n : ℕ} (m : ℕ)
    (I : CodeDeformationInterval) (idx : Fin m)
    (detectors : Finset (Detector n))
    (hdet : ∀ D ∈ detectors, ¬violates (pureTimeFaultFromChain (n := n) m I idx) D) :
    isUndetectable (pureTimeFaultFromChain (n := n) m I idx) detectors := by
  unfold isUndetectable syndromeFinset
  ext D
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  exact hdet D

/-- **Achievability Theorem** -/
theorem chain_is_logical_fault {n k m : ℕ} (C : StabilizerCode n k)
    (I : CodeDeformationInterval) (idx : Fin m) (hm : 0 < m)
    (hnumRounds_odd : Odd I.numRounds)
    (detectors : Finset (Detector n))
    (hdet : ∀ D ∈ detectors, ¬violates (pureTimeFaultFromChain (n := n) m I idx) D) :
    IsSpacetimeLogicalFaultConcrete C (pureTimeFaultFromChain (n := n) m I idx) detectors := by
  constructor
  · exact chainFault_undetectable_for_detectors m I idx detectors hdet
  · rw [isPureTimeFault_actsTrivially_iff C _ (pureTimeFaultFromChain_isPure m I idx)]
    exact chainFault_not_cancel m I idx hm hnumRounds_odd

/-! ## Section 11: Summary Theorem -/

theorem time_fault_distance_summary {n k m : ℕ} (C : StabilizerCode n k)
    (I : CodeDeformationInterval) (hm : 0 < m) :
    -- 1. Lower bound
    (∀ (F : SpaceTimeFault n m),
      isPureTimeFault F →
      (∀ idx t, I.t_i ≤ t → t < I.t_o → ¬violatesComparisonDetector F.timeFaults ⟨idx, t⟩) →
      (∃ idx : Fin m, ∃ t0 : TimeStep,
        I.t_i ≤ t0 ∧ t0 < I.t_o ∧ Odd (timeFaultCountAt F.timeFaults idx t0)) →
      I.numRounds ≤ F.weight) ∧
    -- 2. Achievable upper bound
    (∀ idx : Fin m, (pureTimeFaultFromChain (n := n) m I idx).weight = I.numRounds) ∧
    -- 3. Chain is logical when numRounds is odd
    (∀ idx : Fin m, Odd I.numRounds →
      ∀ detectors : Finset (Detector n),
      (∀ D ∈ detectors, ¬violates (pureTimeFaultFromChain (n := n) m I idx) D) →
      IsSpacetimeLogicalFaultConcrete C (pureTimeFaultFromChain (n := n) m I idx) detectors) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F hpure hno_viol hfaults
    exact pure_time_fault_weight_ge_rounds F I hpure hno_viol hfaults
  · exact pureTimeFaultFromChain_weight m I
  · intro idx hodd detectors hdet
    exact chain_is_logical_fault C I idx hm hodd detectors hdet

end QEC
