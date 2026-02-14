import QEC1.Definitions.Def_7_SpaceAndTimeFaults
import QEC1.Definitions.Def_8_Detectors
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Definition 9: Syndrome

## Statement
The **syndrome** of a spacetime fault (Def 7) is the set of detectors (Def 8) that are
violated by the fault. A detector is violated if the product of its measurement outcomes
is −1 instead of the expected +1.

Equivalently, working over Z₂, if detectors are indexed as D₁, …, Dₘ, the syndrome
can be identified with a binary vector s ∈ Z₂^m where sⱼ = 1 iff detector Dⱼ is violated.

## Main Results
- `syndromeFault`: The syndrome of a spacetime fault as a finset of detector indices
- `syndromeVec`: The syndrome as a binary vector s ∈ (I → ZMod 2)
- `mem_syndromeFault_iff`: Detector i is in the syndrome iff it is violated by the fault
- `syndromeVec_eq_one_iff`: s(i) = 1 iff detector i is violated

## Corollaries
- `syndromeFault_empty`: The syndrome is empty for the fault-free configuration
- `syndromeVec_zero`: The syndrome vector is zero for no faults
- `syndromeFault_eq_syndrome`: The spacetime syndrome reduces to the time-fault syndrome
- `syndromeVec_sum`: The sum of the syndrome vector counts violated detectors (mod 2)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {Q : Type*} {T : Type*} {M : Type*}
variable {I : Type*}

/-! ## Decidability of isViolated -/

/-- `Detector.isViolated` is decidable because it reduces to equality in `ZMod 2`,
    which has `DecidableEq`. -/
instance Detector.decidableIsViolated [DecidableEq M] [DecidableEq (TimeFault M)]
    (D : Detector M) (faults : Finset (TimeFault M)) :
    Decidable (D.isViolated faults) :=
  inferInstanceAs (Decidable (D.observedParity faults = 1))

/-! ## Syndrome of a Spacetime Fault -/

/-- The syndrome of a spacetime fault F with respect to a collection of detectors:
    the finset of detector indices that are violated by F.
    Since detectors depend only on measurement outcomes (time-faults flip outcomes),
    the syndrome is determined by the time-fault component of F. -/
def syndromeFault [DecidableEq I] [Fintype I] [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) : Finset I :=
  Finset.univ.filter (fun i => (detectors i).isViolated F.timeFaults)

/-- The syndrome as a binary vector: s(i) = 1 if detector i is violated, 0 otherwise.
    This is the Z₂^m representation from the paper. -/
def syndromeVec [DecidableEq I] [Fintype I] [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) : I → ZMod 2 :=
  fun i => if (detectors i).isViolated F.timeFaults then 1 else 0

/-! ## Membership and characterization -/

/-- A detector index is in the syndrome iff the detector is violated by the spacetime fault. -/
@[simp]
theorem mem_syndromeFault_iff [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (i : I) :
    i ∈ syndromeFault detectors F ↔ (detectors i).isViolated F.timeFaults := by
  simp [syndromeFault]

/-- The syndrome vector is 1 at index i iff detector i is violated. -/
@[simp]
theorem syndromeVec_eq_one_iff [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (i : I) :
    syndromeVec detectors F i = 1 ↔ (detectors i).isViolated F.timeFaults := by
  unfold syndromeVec
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun hv => absurd hv h⟩

/-- The syndrome vector is 0 at index i iff detector i is not violated. -/
@[simp]
theorem syndromeVec_eq_zero_iff [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (i : I) :
    syndromeVec detectors F i = 0 ↔ ¬(detectors i).isViolated F.timeFaults := by
  unfold syndromeVec
  split_ifs with h
  · simp [h]
  · simp [h]

/-! ## Consistency with Def_8 syndrome -/

/-- The spacetime syndrome equals the Def_8 syndrome applied to the time-fault component.
    This captures the key fact that detectors depend only on measurement outcomes,
    so only time-faults affect the syndrome. -/
theorem syndromeFault_eq_syndrome [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) :
    syndromeFault detectors F = Detector.syndrome detectors F.timeFaults := by
  ext i
  simp [syndromeFault, Detector.syndrome, Detector.isViolated]

/-! ## Empty fault syndrome -/

/-- The syndrome is empty for the fault-free spacetime configuration. -/
@[simp]
theorem syndromeFault_empty [DecidableEq Q] [DecidableEq T]
    [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    [DecidableEq (SpaceFault Q T)]
    (detectors : I → Detector M) :
    syndromeFault detectors (SpacetimeFault.empty : SpacetimeFault Q T M) = ∅ := by
  simp only [syndromeFault, Finset.filter_eq_empty_iff]
  intro i _
  exact Detector.not_isViolated_no_faults (detectors i)

/-- The syndrome vector is zero for the fault-free configuration. -/
@[simp]
theorem syndromeVec_zero [DecidableEq Q] [DecidableEq T]
    [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    [DecidableEq (SpaceFault Q T)]
    (detectors : I → Detector M) :
    syndromeVec detectors (SpacetimeFault.empty : SpacetimeFault Q T M) = 0 := by
  ext i
  simp only [syndromeVec, Pi.zero_apply]
  have : ¬(detectors i).isViolated (SpacetimeFault.empty : SpacetimeFault Q T M).timeFaults :=
    Detector.not_isViolated_no_faults (detectors i)
  simp [this]


/-! ## Syndrome vector and finset correspondence -/

/-- The syndrome finset is exactly the support of the syndrome vector. -/
theorem syndromeFault_eq_support [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) :
    syndromeFault detectors F =
      Finset.univ.filter (fun i => syndromeVec detectors F i = 1) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_syndromeFault_iff, syndromeVec_eq_one_iff]

/-- Membership in syndrome finset iff the syndrome vector entry is 1. -/
theorem mem_syndromeFault_iff_vec [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (i : I) :
    i ∈ syndromeFault detectors F ↔ syndromeVec detectors F i = 1 := by
  rw [mem_syndromeFault_iff, ← syndromeVec_eq_one_iff]

/-- Not in syndrome finset iff the syndrome vector entry is 0. -/
theorem not_mem_syndromeFault_iff_vec [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (i : I) :
    i ∉ syndromeFault detectors F ↔ syndromeVec detectors F i = 0 := by
  rw [mem_syndromeFault_iff, syndromeVec_eq_zero_iff]

/-! ## Space-faults do not affect the syndrome -/

/-- Space-faults do not affect the syndrome: two spacetime faults with the same
    time-faults produce the same syndrome. This formalizes the key insight that
    the syndrome depends only on measurement outcome flips (time-faults). -/
theorem syndromeFault_depends_on_timeFaults [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F₁ F₂ : SpacetimeFault Q T M) (h : F₁.timeFaults = F₂.timeFaults) :
    syndromeFault detectors F₁ = syndromeFault detectors F₂ := by
  ext i
  simp [syndromeFault, Detector.isViolated, Detector.observedParity, h]

/-- The syndrome vector is the same for faults with identical time-fault components. -/
theorem syndromeVec_depends_on_timeFaults [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F₁ F₂ : SpacetimeFault Q T M) (h : F₁.timeFaults = F₂.timeFaults) :
    syndromeVec detectors F₁ = syndromeVec detectors F₂ := by
  ext i
  simp [syndromeVec, Detector.isViolated, Detector.observedParity, h]

/-! ## Syndrome of pure space-faults and pure time-faults -/

/-- A pure space-fault (no time-faults) has empty syndrome. -/
theorem syndromeFault_pureSpace [DecidableEq Q] [DecidableEq T]
    [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    [DecidableEq (SpaceFault Q T)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (hpure : F.isPureSpace) :
    syndromeFault detectors F = ∅ := by
  have htf : F.timeFaults = ∅ := hpure
  simp only [syndromeFault, Finset.filter_eq_empty_iff]
  intro i _
  unfold Detector.isViolated
  rw [htf, Detector.observedParity_no_faults]
  exact zero_ne_one

/-- A pure space-fault has zero syndrome vector. -/
theorem syndromeVec_pureSpace [DecidableEq Q] [DecidableEq T]
    [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    [DecidableEq (SpaceFault Q T)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (hpure : F.isPureSpace) :
    syndromeVec detectors F = 0 := by
  have htf : F.timeFaults = ∅ := hpure
  ext i
  simp only [syndromeVec, Pi.zero_apply]
  have : ¬(detectors i).isViolated F.timeFaults := by
    unfold Detector.isViolated
    rw [htf, Detector.observedParity_no_faults]
    exact zero_ne_one
  simp [this]

/-! ## Syndrome cardinality -/

/-- The number of violated detectors equals the cardinality of the syndrome. -/
theorem syndromeFault_card [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) :
    (syndromeFault detectors F).card =
      (Finset.univ.filter (fun i => (detectors i).isViolated F.timeFaults)).card := by
  rfl

/-! ## Syndrome sum (mod 2) -/

/-- The sum of the syndrome vector counts the number of violated detectors mod 2. -/
theorem syndromeVec_sum [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) :
    ∑ i : I, syndromeVec detectors F i =
      ((syndromeFault detectors F).card : ZMod 2) := by
  simp only [syndromeVec, syndromeFault]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.cast_card]

/-! ## Syndrome determined by flip parity -/

/-- The syndrome is equivalently described using flip parities of detectors. -/
theorem syndromeFault_eq_flipParity_filter [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) :
    syndromeFault detectors F =
      Finset.univ.filter (fun i => (detectors i).flipParity F.timeFaults = 1) := by
  ext i
  simp [syndromeFault, Detector.isViolated, Detector.observedParity_eq_flipParity]

/-- In ZMod 2, every element is 0 or 1. -/
private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- The syndrome vector can be computed via flip parities. -/
theorem syndromeVec_eq_flipParity [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F : SpacetimeFault Q T M) (i : I) :
    syndromeVec detectors F i = (detectors i).flipParity F.timeFaults := by
  simp only [syndromeVec, Detector.isViolated, Detector.observedParity_eq_flipParity]
  split_ifs with h
  · exact h.symm
  · push_neg at h
    rcases zmod2_eq_zero_or_one ((detectors i).flipParity F.timeFaults) with h0 | h1
    · exact h0.symm
    · exact absurd h1 h

/-! ## Single fault syndrome -/

/-- A pure space-fault has empty syndrome: space-faults don't violate detectors. -/
theorem syndromeFault_ofSpaceFault [DecidableEq Q] [DecidableEq T]
    [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    [DecidableEq (SpaceFault Q T)]
    (detectors : I → Detector M) (f : SpaceFault Q T) :
    syndromeFault detectors (SpacetimeFault.ofSpaceFault f : SpacetimeFault Q T M) = ∅ := by
  apply syndromeFault_pureSpace
  exact SpacetimeFault.isPureSpace_ofSpaceFault f

/-- A detector not containing any faulted measurement is not violated. -/
theorem not_isViolated_disjoint [DecidableEq M] [DecidableEq (TimeFault M)]
    (D : Detector M) (faults : Finset (TimeFault M))
    (h : ∀ m ∈ D.measurements, (⟨m⟩ : TimeFault M) ∉ faults) :
    ¬D.isViolated faults := by
  rw [Detector.isViolated_iff_flipParity]
  have : D.flipParity faults = 0 := by
    unfold Detector.flipParity
    apply Finset.sum_eq_zero
    intro m hm
    simp [h m hm]
  rw [this]
  exact zero_ne_one

/-! ## Syndrome determines information about errors -/

/-- The syndrome captures the error information revealed by detectors:
    two faults produce the same syndrome iff they violate the same detectors. -/
theorem syndromeFault_eq_iff [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F₁ F₂ : SpacetimeFault Q T M) :
    syndromeFault detectors F₁ = syndromeFault detectors F₂ ↔
      ∀ i : I, (detectors i).isViolated F₁.timeFaults ↔
              (detectors i).isViolated F₂.timeFaults := by
  constructor
  · intro h i
    have h1 := mem_syndromeFault_iff detectors F₁ i
    have h2 := mem_syndromeFault_iff detectors F₂ i
    rw [h] at h1
    exact ⟨fun hv => h2.mp (h1.mpr hv), fun hv => h1.mp (h2.mpr hv)⟩
  · intro h
    ext i
    simp [syndromeFault, h i]

/-- Two faults with the same syndrome have identical syndrome vectors. -/
theorem syndromeVec_eq_iff [DecidableEq I] [Fintype I]
    [DecidableEq M] [DecidableEq (TimeFault M)]
    (detectors : I → Detector M)
    (F₁ F₂ : SpacetimeFault Q T M) :
    syndromeVec detectors F₁ = syndromeVec detectors F₂ ↔
      syndromeFault detectors F₁ = syndromeFault detectors F₂ := by
  constructor
  · intro h
    ext i
    have hi : syndromeVec detectors F₁ i = syndromeVec detectors F₂ i := congr_fun h i
    simp only [mem_syndromeFault_iff, ← syndromeVec_eq_one_iff, hi]
  · intro h
    ext i
    have : (i ∈ syndromeFault detectors F₁) ↔ (i ∈ syndromeFault detectors F₂) := by
      rw [h]
    rw [mem_syndromeFault_iff, ← syndromeVec_eq_one_iff] at this
    rw [mem_syndromeFault_iff, ← syndromeVec_eq_one_iff] at this
    rcases zmod2_eq_zero_or_one (syndromeVec detectors F₁ i) with h0 | h1 <;>
    rcases zmod2_eq_zero_or_one (syndromeVec detectors F₂ i) with h0' | h1'
    · rw [h0, h0']
    · exfalso; rw [h0] at this; exact zero_ne_one (this.mpr h1')
    · exfalso; rw [h0'] at this; exact zero_ne_one (this.mp h1)
    · rw [h1, h1']
