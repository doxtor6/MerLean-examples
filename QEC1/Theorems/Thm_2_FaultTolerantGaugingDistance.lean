import QEC1.Definitions.Def_12_SpacetimeFaultDistance
import QEC1.Lemmas.Lem_3_SpaceDistance
import QEC1.Lemmas.Lem_6_TimeFaultDistance
import QEC1.Lemmas.Lem_7_SpaceTimeDecoupling
import QEC1.Remarks.Rem_13_OptimalCheegerConstant
import Mathlib.Tactic

/-!
# Theorem 2: Fault-Tolerant Gauging Distance

## Statement
The spacetime fault-distance (Def_12) of the fault-tolerant gauging measurement procedure
(Def_10) is d, the distance of the original [[n,k,d]] stabilizer code (Rem_3), provided that:
1. The graph G has Cheeger constant h(G) ≥ 1 (Rem_4), and
2. The number of deformed code rounds satisfies t_o - t_i ≥ d.

Formally: d_spacetime = d.

## Main Results
- `spacetimeFaultDistance_eq_d`: The spacetime fault-distance equals d
- `spacetimeFaultDistance_ge_d`: Lower bound: d_spacetime ≥ d
- `spacetimeFaultDistance_le_d`: Upper bound: d_spacetime ≤ d (via space-fault witness)
- `fullLogicalFault_weight_ge_d`: Any full gauging logical fault has weight ≥ d

## Proof Outline
**Lower bound**: Any spacetime logical fault F decomposes as F = F_S · F_T · S (Lem 7).
Case (a): If F_T flips σ (requires odd d), then |F_T| ≥ d by Lem 6, hence |F| ≥ d.
Case (b): If F_S is a nontrivial space logical, then d ≤ d* ≤ |F_S.pauliErrorAt| ≤ |F|
  by Lem 3 with h(G) ≥ 1.
When d is even, case (a) is vacuous (no syndrome-free pure-time fault can flip σ),
so only case (b) applies.

**Upper bound**: A minimum-weight logical L₀ of the original code, placed as a
space-fault at time t_i, gives a spacetime logical fault of weight d.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open Finset PauliOp GaussFlux DeformedCode DeformedOperator DeformedCodeChecks
open FaultTolerantGaugingProcedure SpacetimeLogicalFault SpacetimeStabilizers
open SpacetimeFaultDistance TimeFaultDistance SpaceTimeDecoupling
open OptimalCheegerConstant DesiderataForGraphG

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  {cycles : C → Set G.edgeSet} [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  {checks : J → PauliOp V}

namespace FaultTolerantGaugingDistance

variable (proc : FaultTolerantGaugingProcedure G cycles checks)

/-! ## Part I: Space-Fault Witness Construction

The paper's upper bound uses a minimum-weight logical operator L₀ of the original
code, placed as a space-fault at time t_i. This construction builds a spacetime
fault from a deformed code logical operator.

For each qubit q in P.support, we create a SpaceFault at qubit q, time t_i,
with the appropriate X and Z components from P. The resulting spacetime fault
has no time-faults (pure-space), so it is syndrome-free.
-/

/-- Build a SpaceFault from a qubit in the support of P. -/
def mkSpaceFault (P : PauliOp (ExtQubit G)) (t : ℕ)
    (q : ExtQubit G) (hq : q ∈ P.support) :
    SpaceFault (ExtQubit G) ℕ :=
  ⟨q, t, P.xVec q, P.zVec q, (PauliOp.mem_support P q).mp hq⟩

/-- The finset of space-faults corresponding to a Pauli operator at a given time. -/
def spaceFaultsOfPauliOp (P : PauliOp (ExtQubit G)) (t : ℕ) :
    Finset (SpaceFault (ExtQubit G) ℕ) :=
  P.support.attach.image (fun ⟨q, hq⟩ => mkSpaceFault P t q hq)

/-- The map from P.support to SpaceFault is injective (different qubits give
    different space faults). -/
theorem mkSpaceFault_injective (P : PauliOp (ExtQubit G)) (t : ℕ) :
    Function.Injective (fun (x : {q // q ∈ P.support}) =>
      mkSpaceFault P t x.val x.property) := by
  intro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ heq
  simp only [mkSpaceFault, SpaceFault.mk.injEq] at heq
  exact Subtype.ext heq.1

/-- The space-fault finset has the same cardinality as P.support. -/
theorem spaceFaultsOfPauliOp_card (P : PauliOp (ExtQubit G)) (t : ℕ) :
    (spaceFaultsOfPauliOp P t).card = P.support.card := by
  unfold spaceFaultsOfPauliOp
  rw [Finset.card_image_of_injective _ (mkSpaceFault_injective P t)]
  exact Finset.card_attach

/-- Given a logical operator P of the deformed code, placing it as a collection
    of space-faults at time t_i produces a spacetime fault.

    Concretely: for each qubit q in P.support, we create a SpaceFault at qubit q,
    time t_i, with the appropriate X and Z components from P. -/
def spacetimeFaultOfDeformedLogical
    (P : PauliOp (ExtQubit G))
    (_hlog : (theDeformedCode proc).isLogicalOp P) :
    SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel :=
  ⟨spaceFaultsOfPauliOp P proc.phase2Start, ∅⟩

/-- The space-fault witness has the same weight as the Pauli operator. -/
theorem spacetimeFaultOfDeformedLogical_weight
    (P : PauliOp (ExtQubit G))
    (hlog : (theDeformedCode proc).isLogicalOp P) :
    (spacetimeFaultOfDeformedLogical proc P hlog).weight = P.weight := by
  unfold spacetimeFaultOfDeformedLogical SpacetimeFault.weight PauliOp.weight
  simp [spaceFaultsOfPauliOp_card]

/-- The space-fault witness is pure-space (no time-faults). -/
theorem spacetimeFaultOfDeformedLogical_isPureSpace
    (P : PauliOp (ExtQubit G))
    (hlog : (theDeformedCode proc).isLogicalOp P) :
    (spacetimeFaultOfDeformedLogical proc P hlog).isPureSpace := by
  unfold spacetimeFaultOfDeformedLogical SpacetimeFault.isPureSpace
  rfl

/-- The space-fault witness is syndrome-free: it has no time-faults, so
    every detector checks against ∅ which is never violated. -/
theorem spacetimeFaultOfDeformedLogical_syndromeFree
    (P : PauliOp (ExtQubit G))
    (hlog : (theDeformedCode proc).isLogicalOp P) :
    IsSyndromeFreeGauging proc proc.detectorOfIndex
      (spacetimeFaultOfDeformedLogical proc P hlog) := by
  intro idx
  have htf : (spacetimeFaultOfDeformedLogical proc P hlog).timeFaults = ∅ := rfl
  rw [htf]
  exact Detector.not_isViolated_no_faults _

/-- Helper: a space fault in spaceFaultsOfPauliOp has the correct time. -/
theorem spaceFaultsOfPauliOp_time (P : PauliOp (ExtQubit G)) (t : ℕ)
    (f : SpaceFault (ExtQubit G) ℕ) (hf : f ∈ spaceFaultsOfPauliOp P t) :
    f.time = t := by
  simp only [spaceFaultsOfPauliOp, Finset.mem_image, Finset.mem_attach,
    Subtype.exists, true_and] at hf
  obtain ⟨q, _, rfl⟩ := hf
  rfl

/-- Helper: a space fault in spaceFaultsOfPauliOp has qubit in P.support. -/
theorem spaceFaultsOfPauliOp_qubit_mem (P : PauliOp (ExtQubit G)) (t : ℕ)
    (f : SpaceFault (ExtQubit G) ℕ) (hf : f ∈ spaceFaultsOfPauliOp P t) :
    f.qubit ∈ P.support := by
  simp only [spaceFaultsOfPauliOp, Finset.mem_image, Finset.mem_attach,
    Subtype.exists, true_and] at hf
  obtain ⟨q, hq, rfl⟩ := hf
  exact hq

/-- Helper: for each qubit in P.support, there exists a space fault. -/
theorem spaceFaultsOfPauliOp_mem (P : PauliOp (ExtQubit G)) (t : ℕ)
    (q : ExtQubit G) (hq : q ∈ P.support) :
    mkSpaceFault P t q hq ∈ spaceFaultsOfPauliOp P t := by
  simp only [spaceFaultsOfPauliOp, Finset.mem_image, Finset.mem_attach,
    Subtype.exists, true_and]
  exact ⟨q, hq, rfl⟩

/-- Helper: each space fault in spaceFaultsOfPauliOp has xComponent = P.xVec f.qubit -/
theorem spaceFaultsOfPauliOp_xComponent (P : PauliOp (ExtQubit G)) (t : ℕ)
    (f : SpaceFault (ExtQubit G) ℕ) (hf : f ∈ spaceFaultsOfPauliOp P t) :
    f.xComponent = P.xVec f.qubit := by
  simp only [spaceFaultsOfPauliOp, Finset.mem_image, Finset.mem_attach,
    Subtype.exists, true_and] at hf
  obtain ⟨q, _, rfl⟩ := hf
  rfl

/-- Helper: each space fault in spaceFaultsOfPauliOp has zComponent = P.zVec f.qubit -/
theorem spaceFaultsOfPauliOp_zComponent (P : PauliOp (ExtQubit G)) (t : ℕ)
    (f : SpaceFault (ExtQubit G) ℕ) (hf : f ∈ spaceFaultsOfPauliOp P t) :
    f.zComponent = P.zVec f.qubit := by
  simp only [spaceFaultsOfPauliOp, Finset.mem_image, Finset.mem_attach,
    Subtype.exists, true_and] at hf
  obtain ⟨q, _, rfl⟩ := hf
  rfl

/-- Helper: at most one space fault per qubit in spaceFaultsOfPauliOp. -/
theorem spaceFaultsOfPauliOp_unique (P : PauliOp (ExtQubit G)) (t : ℕ)
    (f₁ f₂ : SpaceFault (ExtQubit G) ℕ)
    (hf₁ : f₁ ∈ spaceFaultsOfPauliOp P t) (hf₂ : f₂ ∈ spaceFaultsOfPauliOp P t)
    (hq : f₁.qubit = f₂.qubit) : f₁ = f₂ := by
  simp only [spaceFaultsOfPauliOp, Finset.mem_image, Finset.mem_attach,
    Subtype.exists, true_and] at hf₁ hf₂
  obtain ⟨q₁, _, rfl⟩ := hf₁
  obtain ⟨q₂, _, rfl⟩ := hf₂
  simp only [mkSpaceFault] at hq
  subst hq; rfl

/-- The Pauli error at t_i of the space-fault witness equals P. -/
theorem spacetimeFaultOfDeformedLogical_pauliErrorAt
    (P : PauliOp (ExtQubit G))
    (hlog : (theDeformedCode proc).isLogicalOp P) :
    (spacetimeFaultOfDeformedLogical proc P hlog).pauliErrorAt proc.phase2Start = P := by
  ext q
  · -- xVec component
    simp only [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt,
      spacetimeFaultOfDeformedLogical]
    have hfilter : (spaceFaultsOfPauliOp P proc.phase2Start).filter
        (fun f => f.time = proc.phase2Start) =
        spaceFaultsOfPauliOp P proc.phase2Start := by
      ext f
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      exact spaceFaultsOfPauliOp_time P proc.phase2Start f
    rw [hfilter]
    by_cases hq : q ∈ P.support
    · -- q is in support: exactly one fault at q contributes P.xVec q
      have hmem := spaceFaultsOfPauliOp_mem P proc.phase2Start q hq
      -- The unique fault at qubit q is mkSpaceFault
      -- Use sum_eq_single_of_mem
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · simp [mkSpaceFault]
      · intro f hf hne
        have hfq : f.qubit ≠ q := by
          intro heqq
          apply hne
          exact spaceFaultsOfPauliOp_unique P proc.phase2Start f
            (mkSpaceFault P proc.phase2Start q hq) hf hmem heqq
        simp [hfq]
    · -- q not in support: P.xVec q = 0 (both components are zero)
      rw [PauliOp.mem_support] at hq; push_neg at hq; rw [hq.1]
      apply Finset.sum_eq_zero
      intro f hf
      have : f.qubit ≠ q := by
        intro heq_q
        have hmem_q := spaceFaultsOfPauliOp_qubit_mem P proc.phase2Start f hf
        rw [heq_q] at hmem_q
        rw [PauliOp.mem_support] at hmem_q
        exact hmem_q.elim (fun h => h hq.1) (fun h => h hq.2)
      simp [this]
  · -- zVec component (symmetric argument)
    simp only [SpacetimeFault.pauliErrorAt, SpacetimeFault.spaceFaultsAt,
      spacetimeFaultOfDeformedLogical]
    have hfilter : (spaceFaultsOfPauliOp P proc.phase2Start).filter
        (fun f => f.time = proc.phase2Start) =
        spaceFaultsOfPauliOp P proc.phase2Start := by
      ext f
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      exact spaceFaultsOfPauliOp_time P proc.phase2Start f
    rw [hfilter]
    by_cases hq : q ∈ P.support
    · have hmem := spaceFaultsOfPauliOp_mem P proc.phase2Start q hq
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · simp [mkSpaceFault]
      · intro f hf hne
        have hfq : f.qubit ≠ q := by
          intro heqq
          apply hne
          exact spaceFaultsOfPauliOp_unique P proc.phase2Start f
            (mkSpaceFault P proc.phase2Start q hq) hf hmem heqq
        simp [hfq]
    · rw [PauliOp.mem_support] at hq; push_neg at hq; rw [hq.2]
      apply Finset.sum_eq_zero
      intro f hf
      have : f.qubit ≠ q := by
        intro heq_q
        have hmem_q := spaceFaultsOfPauliOp_qubit_mem P proc.phase2Start f hf
        rw [heq_q] at hmem_q
        rw [PauliOp.mem_support] at hmem_q
        exact hmem_q.elim (fun h => h hq.1) (fun h => h hq.2)
      simp [this]

/-- The space-fault witness is a full gauging logical fault:
    it is syndrome-free and NOT outcome-preserving.
    The sign is preserved (pure-space → gaussSignFlip = 0), but the Pauli error
    at t_i is P, which is NOT in the stabilizer group (since P is a logical). -/
theorem spaceFaultWitness_isFullLogicalFault
    (P : PauliOp (ExtQubit G))
    (hlog : (theDeformedCode proc).isLogicalOp P) :
    IsFullGaugingLogicalFault proc (spacetimeFaultOfDeformedLogical proc P hlog) := by
  refine ⟨spacetimeFaultOfDeformedLogical_syndromeFree proc P hlog, ?_⟩
  intro ⟨_, hpauli_stab⟩
  rw [spacetimeFaultOfDeformedLogical_pauliErrorAt] at hpauli_stab
  exact hlog.2.1 hpauli_stab

/-! ## Part II: Upper Bound d_spacetime ≤ d

A deformed code logical of minimum weight gives a space-fault witness.
By Rem 13 (d* = d when h(G) ≥ 1), the deformed code has a logical of weight d.
-/

/-- Upper bound: d_spacetime ≤ d (via the space-fault witness).

    Place a minimum-weight deformed code logical at time t_i as a collection
    of space-faults. This has weight d* ≤ d and is a full gauging logical fault. -/
theorem spacetimeFaultDistance_le_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (_hconn : G.Connected) (_hcard : 2 ≤ Fintype.card V)
    (_hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (_hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (_hexp : SufficientExpansion G)
    (_hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (_hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (P : PauliOp V) (hPlog : origCode.isLogicalOp P) (hPpureX : P.zVec = 0)
    (hPweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (theDeformedCode proc).stabilizerGroup) :
    gaugingSpacetimeFaultDistance proc proc.detectorOfIndex
      (FullOutcomePreserving proc) ≤ proc.d := by
  have hDeformedCode_eq : theDeformedCode proc =
      deformedStabilizerCode G cycles checks proc.deformedData
        proc.cycleParity proc.checks_commute := rfl
  -- The lift of P is a logical of the deformed code
  have hLiftLog : (theDeformedCode proc).isLogicalOp (liftToExtended G P) := by
    rw [hDeformedCode_eq]
    exact liftToExtended_isLogical G cycles checks origCode hJ hchecks_eq
      proc.deformedData proc.cycleParity proc.checks_commute
      P hPlog hPpureX (by rw [← hDeformedCode_eq]; exact hnotDeformedStab)
  -- Build the space-fault witness
  let F := spacetimeFaultOfDeformedLogical proc (liftToExtended G P) hLiftLog
  -- The witness is a full gauging logical fault
  have hlog := spaceFaultWitness_isFullLogicalFault proc (liftToExtended G P) hLiftLog
  calc gaugingSpacetimeFaultDistance proc proc.detectorOfIndex (FullOutcomePreserving proc)
      ≤ F.weight := gaugingSpacetimeFaultDistance_le proc hlog
    _ = (liftToExtended G P).weight :=
        spacetimeFaultOfDeformedLogical_weight proc (liftToExtended G P) hLiftLog
    _ = P.weight := liftToExtended_weight G P
    _ = origCode.distance := hPweight
    _ = proc.d := hd_eq

/-! ## Part III: Lower Bound d_spacetime ≥ d

Any full logical fault has weight ≥ d. We use the decomposition from Lem 7:
- Case (a): F_T flips σ → |F| ≥ d via time component weight bound (requires odd d)
- Case (b): F_S is a nontrivial deformed code logical → d ≤ d* ≤ |F.pauliErrorAt| ≤ |F|

When d is even, case (a) is vacuous: no syndrome-free pure-time fault can flip σ
(each vertex has 0 or d faults by all-or-none, so total count is k·d ≡ 0 mod 2).
-/

/-- When d is even, no syndrome-free pure-time fault can flip the gauging sign σ.
    This is because the all-or-none property (from Lem 6's detector structure) forces
    each vertex's A_v fault count to be 0 or d. When d is even, the total
    gaussSignFlip = Σ (0 or d) = k·d ≡ 0 (mod 2) for all k. -/
theorem even_d_no_time_sign_flip
    (F_T : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (_hpT : F_T.isPureTime)
    (hfreeT : IsSyndromeFreeGauging proc proc.detectorOfIndex F_T)
    (heven : Even proc.d) :
    PreservesGaugingSign proc F_T := by
  -- When d is even, every vertex contributes 0 or d (even) faults.
  -- Total sign = sum of even numbers = 0 in ZMod 2.
  rw [PreservesGaugingSign]
  rw [gaussSignFlip_eq_sum_parities proc F_T]
  apply Finset.sum_eq_zero
  intro v _
  rcases gaussFaultCount_zero_or_d proc v F_T hfreeT with h0 | hd
  · simp [h0]
  · rw [hd]
    exact ZMod.natCast_eq_zero_iff_even.mpr heven

/-- Helper: the product of a centralizer element and a stabilizer group element
    is in the centralizer. -/
theorem inCentralizer_mul_stabilizerGroup
    (code : StabilizerCode (ExtQubit G))
    (P s : PauliOp (ExtQubit G))
    (hP : code.inCentralizer P)
    (hs : s ∈ code.stabilizerGroup) :
    code.inCentralizer (P * s) := by
  intro i
  rw [PauliOp.PauliCommute]
  rw [PauliOp.symplecticInner_mul_left]
  have h1 := hP i
  rw [PauliOp.PauliCommute] at h1
  rw [h1]
  have h2 := code.stabilizerGroup_subset_centralizer s hs i
  rw [PauliOp.PauliCommute] at h2
  rw [h2, add_zero]

/-- Helper: distance ≤ weight of any logical operator (directly from sInf). -/
theorem distance_le_weight_of_isLogicalOp
    (code : StabilizerCode (ExtQubit G))
    (P : PauliOp (ExtQubit G))
    (hlog : code.isLogicalOp P) :
    code.distance ≤ P.weight := by
  unfold StabilizerCode.distance
  apply Nat.sInf_le
  exact ⟨P, hlog, rfl⟩

/-- Helper: the support of pauliErrorAt t is a subset of the qubit image of
    spaceFaultsAt t. -/
theorem pauliErrorAt_support_subset_image
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) (t : ℕ) :
    (F.pauliErrorAt t).support ⊆ (F.spaceFaultsAt t).image SpaceFault.qubit := by
  intro q hq
  rw [PauliOp.mem_support] at hq
  rw [Finset.mem_image]
  -- q ∈ support means xVec q ≠ 0 ∨ zVec q ≠ 0
  -- xVec q = ∑ f ∈ spaceFaultsAt t, if f.qubit = q then f.xComponent else 0
  -- For this sum to be nonzero, there must exist f with f.qubit = q
  by_contra h
  push_neg at h
  have hx0 : (F.pauliErrorAt t).xVec q = 0 := by
    simp only [SpacetimeFault.pauliErrorAt]
    apply Finset.sum_eq_zero
    intro f hf
    have hne := h f hf
    simp only [ite_eq_right_iff]
    intro heq; exact absurd heq hne
  have hz0 : (F.pauliErrorAt t).zVec q = 0 := by
    simp only [SpacetimeFault.pauliErrorAt]
    apply Finset.sum_eq_zero
    intro f hf
    have hne := h f hf
    simp only [ite_eq_right_iff]
    intro heq; exact absurd heq hne
  exact hq.elim (fun h => h hx0) (fun h => h hz0)

/-- Helper: the weight of the Pauli error at a time is ≤ the total space weight.
    Each qubit in the support of pauliErrorAt t corresponds to at least one
    space-fault at time t, and space-faults at time t are a subset of all
    space-faults. -/
theorem pauliErrorAt_weight_le_spaceWeight
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel) (t : ℕ) :
    (F.pauliErrorAt t).weight ≤ F.spaceWeight := by
  unfold PauliOp.weight SpacetimeFault.spaceWeight
  calc (F.pauliErrorAt t).support.card
      ≤ ((F.spaceFaultsAt t).image SpaceFault.qubit).card :=
        Finset.card_le_card (pauliErrorAt_support_subset_image proc F t)
    _ ≤ (F.spaceFaultsAt t).card := Finset.card_image_le
    _ ≤ F.spaceFaults.card := Finset.card_le_card (Finset.filter_subset _ _)

/-- Any full gauging logical fault has weight ≥ d.

    This is the core content of the lower bound. We use the space-time decoupling
    (Lem 7) to decompose F into space and time components, then bound each case
    using Lem 3 (space distance) and Lem 6 (time distance). -/
theorem fullLogicalFault_weight_ge_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hlog : IsFullGaugingLogicalFault proc F) :
    proc.d ≤ F.weight := by
  -- Decompose F = F_S · F_T · S via Lem 7
  obtain ⟨F_S, F_T, S, hdecomp, hpS, hconc, hpT, hfreeT, hstab, hnontriv⟩ :=
    spaceTime_decomposition proc F hlog
  -- Case analysis: either F_T flips σ, or F_S is a nontrivial deformed code logical
  rcases hnontriv with hflip | hspace_log
  · -- Case (a): F_T flips σ → |F| ≥ d
    -- We show F.timeComponent is pure-time, syndrome-free, and flips σ.
    -- By Lem 6 (which requires odd d): |F.timeComponent| ≥ d.
    -- When d is even, this case is vacuous (no pure-time syndrome-free fault can flip σ).

    -- First, establish that F flips the gauging sign.
    -- gaussSignFlip(F) = gaussSignFlip(F_S) + gaussSignFlip(F_T) + gaussSignFlip(S)
    --                   = 0 + 1 + 0 = 1
    have hF_flips : FlipsGaugingSign proc F := by
      rw [FlipsGaugingSign]
      -- Compute via the decomposition F = (F_S · F_T) · S
      have h1 := gaussSignFlip_compose_additive proc (F_S.compose F_T) S
      have h2 := gaussSignFlip_compose_additive proc F_S F_T
      have hFS_sign := gaussSignFlip_pureSpace proc F_S hpS
      have hS_sign : PreservesGaugingSign proc S := hstab.2.1
      rw [PreservesGaugingSign] at hS_sign
      -- gaussSignFlip(F) = gaussSignFlip((F_S · F_T) · S)
      conv_lhs => rw [hdecomp]
      rw [h1, h2, hFS_sign, hS_sign, zero_add, add_zero]
      exact hflip
    -- F.timeComponent is pure-time, has same timeFaults as F
    have htc_pure : F.timeComponent.isPureTime := F.timeComponent_isPureTime
    -- Syndrome-free: same timeFaults as F, and IsSyndromeFreeGauging only depends on timeFaults
    have htc_free : IsSyndromeFreeGauging proc proc.detectorOfIndex F.timeComponent := by
      intro idx
      -- F.timeComponent.timeFaults = F.timeFaults (by definition of timeComponent)
      exact hlog.1 idx
    -- F.timeComponent flips the sign (same timeFaults → same gaussSignFlip)
    have htc_flips : FlipsGaugingSign proc F.timeComponent := by
      rw [FlipsGaugingSign]
      rw [FlipsGaugingSign] at hF_flips
      rwa [← (space_time_independent_effects proc F).1]
    -- F.timeComponent flipping σ implies d must be odd (otherwise no pure-time
    -- syndrome-free fault can flip σ). So we can apply pureTime_logicalFault_weight_ge_d.
    have hodd : Odd proc.d := by
      by_contra hnotOdd
      rw [Nat.not_odd_iff_even] at hnotOdd
      have := even_d_no_time_sign_flip proc F_T hpT hfreeT hnotOdd
      rw [PreservesGaugingSign] at this
      rw [FlipsGaugingSign] at hflip
      rw [this] at hflip
      exact zero_ne_one hflip
    have htc_ge := pureTime_logicalFault_weight_ge_d proc F.timeComponent
      htc_pure htc_free htc_flips hodd
    -- |F| ≥ F.timeWeight = F.timeComponent.weight ≥ d
    calc proc.d ≤ F.timeComponent.weight := htc_ge
      _ = F.timeWeight := SpacetimeFault.weight_timeComponent F
      _ ≤ F.weight := SpacetimeFault.timeWeight_le_weight F
  · -- Case (b): F_S is a nontrivial deformed code logical → weight ≥ d* ≥ d
    have hFS_logical := hspace_log
    -- The deformed code distance d* ≥ d by Lem 3 with h(G) ≥ 1
    have hDeformedCode_eq : theDeformedCode proc =
        deformedStabilizerCode G cycles checks proc.deformedData
          proc.cycleParity proc.checks_commute := rfl
    have hdstar_ge := sufficient_expansion_gives_dstar_ge_d G cycles checks origCode hJ hchecks_eq
      proc.deformedData proc.cycleParity proc.checks_commute
      hconn hcard hexact hexact_boundary hexp hL_logical
      (by rw [← hDeformedCode_eq]; exact hDeformedHasLogicals)
    -- We show F.pauliErrorAt(t_i) is a logical of the deformed code,
    -- then use d ≤ d* ≤ |F.pauliErrorAt| ≤ |F|.
    -- Compute pauliErrorAt(F, t_i) via the decomposition
    -- F = (F_S · F_T) · S, so pauliErrorAt is a product
    have hF_pauli : F.pauliErrorAt proc.phase2Start =
        F_S.pauliErrorAt proc.phase2Start *
        (F_T.pauliErrorAt proc.phase2Start *
         S.pauliErrorAt proc.phase2Start) := by
      have h1 := pauliErrorAt_compose_mul proc (F_S.compose F_T) S proc.phase2Start
      have h2 := pauliErrorAt_compose_mul proc F_S F_T proc.phase2Start
      conv_lhs => rw [hdecomp]
      rw [h1, h2, _root_.mul_assoc]
    -- F_T.pauliErrorAt = 1 (pure-time)
    have hFT_pauli : F_T.pauliErrorAt proc.phase2Start = 1 :=
      pureTime_pauliError_trivial proc F_T hpT proc.phase2Start
    -- S.pauliErrorAt ∈ stabilizer group
    have hS_pauli : S.pauliErrorAt proc.phase2Start ∈
        (theDeformedCode proc).stabilizerGroup := hstab.2.2
    -- Simplify: F.pauliErrorAt = F_S.pauliErrorAt * S.pauliErrorAt
    rw [hFT_pauli, _root_.one_mul] at hF_pauli
    -- F_S.pauliErrorAt is a logical, S.pauliErrorAt is a stabilizer
    -- Their product F.pauliErrorAt is also a logical
    obtain ⟨hcent_FS, hnotstab_FS, hne1_FS⟩ := hFS_logical
    have hF_pauli_logical : (theDeformedCode proc).isLogicalOp
        (F.pauliErrorAt proc.phase2Start) := by
      rw [hF_pauli]
      refine ⟨?_, ?_, ?_⟩
      · -- In centralizer: product of centralizer element and stabilizer element
        exact inCentralizer_mul_stabilizerGroup (theDeformedCode proc)
          (F_S.pauliErrorAt proc.phase2Start) (S.pauliErrorAt proc.phase2Start)
          hcent_FS hS_pauli
      · -- Not in stabilizer group: if P * s ∈ stab, then P = (P*s) * s⁻¹ ∈ stab
        intro hmem
        apply hnotstab_FS
        have hinv := (theDeformedCode proc).stabilizerGroup.inv_mem hS_pauli
        have : F_S.pauliErrorAt proc.phase2Start =
            F_S.pauliErrorAt proc.phase2Start *
            S.pauliErrorAt proc.phase2Start *
            (S.pauliErrorAt proc.phase2Start)⁻¹ := by
          rw [mul_inv_cancel_right]
        rw [this]
        exact (theDeformedCode proc).stabilizerGroup.mul_mem hmem hinv
      · -- Not identity: if P * s = 1, then P = s⁻¹ ∈ stab, contradiction
        intro h1
        apply hnotstab_FS
        have hinv := (theDeformedCode proc).stabilizerGroup.inv_mem hS_pauli
        have hPeq : F_S.pauliErrorAt proc.phase2Start =
            (S.pauliErrorAt proc.phase2Start)⁻¹ :=
          eq_inv_of_mul_eq_one_left h1
        rw [hPeq]
        exact hinv
    -- d ≤ d* ≤ |F.pauliErrorAt| ≤ |F|
    rw [← hd_eq]
    calc origCode.distance
        ≤ (deformedStabilizerCode G cycles checks proc.deformedData
            proc.cycleParity proc.checks_commute).distance := hdstar_ge
      _ ≤ (F.pauliErrorAt proc.phase2Start).weight := by
          rw [← hDeformedCode_eq]
          exact distance_le_weight_of_isLogicalOp (theDeformedCode proc)
            (F.pauliErrorAt proc.phase2Start) hF_pauli_logical
      _ ≤ F.spaceWeight :=
          pauliErrorAt_weight_le_spaceWeight proc F proc.phase2Start
      _ ≤ F.weight := SpacetimeFault.spaceWeight_le_weight F

/-! ## Part IV: Lower Bound via sInf -/

/-- Lower bound: d_spacetime ≥ d. -/
theorem spacetimeFaultDistance_ge_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (P : PauliOp V) (hPlog : origCode.isLogicalOp P) (hPpureX : P.zVec = 0)
    (_hPweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (theDeformedCode proc).stabilizerGroup) :
    proc.d ≤ gaugingSpacetimeFaultDistance proc proc.detectorOfIndex
      (FullOutcomePreserving proc) := by
  -- The deformed code has logical operators, so logical faults exist
  have hDeformedCode_eq : theDeformedCode proc =
      deformedStabilizerCode G cycles checks proc.deformedData
        proc.cycleParity proc.checks_commute := rfl
  have hLiftLog : (theDeformedCode proc).isLogicalOp (liftToExtended G P) := by
    rw [hDeformedCode_eq]
    exact liftToExtended_isLogical G cycles checks origCode hJ hchecks_eq
      proc.deformedData proc.cycleParity proc.checks_commute
      P hPlog hPpureX (by rw [← hDeformedCode_eq]; exact hnotDeformedStab)
  -- There exists a full gauging logical fault (the space-fault witness)
  have hexists : (gaugingLogicalFaultWeights proc proc.detectorOfIndex
      (FullOutcomePreserving proc)).Nonempty := by
    let F := spacetimeFaultOfDeformedLogical proc (liftToExtended G P) hLiftLog
    exact ⟨F.weight, F,
      spaceFaultWitness_isFullLogicalFault proc (liftToExtended G P) hLiftLog, rfl⟩
  apply le_csInf hexists
  intro w ⟨F, hlog, hw⟩
  rw [← hw]
  exact fullLogicalFault_weight_ge_d proc origCode hJ hchecks_eq
    hconn hcard hexact hexact_boundary hexp hL_logical
    hDeformedHasLogicals hd_eq F hlog

/-! ## Part V: Main Theorem -/

/-- **Theorem 2 (Fault-Tolerant Gauging Distance):**
    The spacetime fault-distance of the fault-tolerant gauging measurement procedure
    equals d, the distance of the original code, when h(G) ≥ 1.

    No parity assumption on d is needed: when d is even, the lower bound still
    holds because case (a) (time-logical) is vacuous, and case (b) (space-logical)
    provides |F| ≥ d* ≥ d. -/
theorem spacetimeFaultDistance_eq_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (P : PauliOp V) (hPlog : origCode.isLogicalOp P) (hPpureX : P.zVec = 0)
    (hPweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (theDeformedCode proc).stabilizerGroup) :
    gaugingSpacetimeFaultDistance proc proc.detectorOfIndex
      (FullOutcomePreserving proc) = proc.d := by
  apply le_antisymm
  · exact spacetimeFaultDistance_le_d proc origCode hJ hchecks_eq
      hconn hcard hexact hexact_boundary hexp hL_logical
      hDeformedHasLogicals hd_eq P hPlog hPpureX hPweight hnotDeformedStab
  · exact spacetimeFaultDistance_ge_d proc origCode hJ hchecks_eq
      hconn hcard hexact hexact_boundary hexp hL_logical
      hDeformedHasLogicals hd_eq P hPlog hPpureX hPweight hnotDeformedStab

/-! ## Corollaries -/

/-- The spacetime fault-distance is positive. -/
theorem spacetimeFaultDistance_pos
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (P : PauliOp V) (hPlog : origCode.isLogicalOp P) (hPpureX : P.zVec = 0)
    (hPweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (theDeformedCode proc).stabilizerGroup) :
    0 < gaugingSpacetimeFaultDistance proc proc.detectorOfIndex
      (FullOutcomePreserving proc) := by
  rw [spacetimeFaultDistance_eq_d proc origCode hJ hchecks_eq
    hconn hcard hexact hexact_boundary hexp hL_logical
    hDeformedHasLogicals hd_eq P hPlog hPpureX hPweight hnotDeformedStab]
  exact proc.d_pos

/-- Any full gauging fault of weight < d is a gauging stabilizer. -/
theorem weight_lt_d_is_stabilizer
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (P : PauliOp V) (hPlog : origCode.isLogicalOp P) (hPpureX : P.zVec = 0)
    (hPweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (theDeformedCode proc).stabilizerGroup)
    (F : SpacetimeFault (ExtQubit G) ℕ proc.MeasLabel)
    (hfree : IsSyndromeFreeGauging proc proc.detectorOfIndex F)
    (hw : F.weight < proc.d) :
    IsFullGaugingStabilizer proc F := by
  have hlt : F.weight < gaugingSpacetimeFaultDistance proc proc.detectorOfIndex
      (FullOutcomePreserving proc) := by
    rw [spacetimeFaultDistance_eq_d proc origCode hJ hchecks_eq
      hconn hcard hexact hexact_boundary hexp hL_logical
      hDeformedHasLogicals hd_eq P hPlog hPpureX hPweight hnotDeformedStab]
    exact hw
  exact syndromeFree_gauging_weight_lt_is_stabilizer proc hfree hlt

/-- The spacetime fault-distance equals the Phase 2 duration. -/
theorem spacetimeFaultDistance_eq_phase2_duration
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P)
    (hd_eq : origCode.distance = proc.d)
    (P : PauliOp V) (hPlog : origCode.isLogicalOp P) (hPpureX : P.zVec = 0)
    (hPweight : P.weight = origCode.distance)
    (hnotDeformedStab : liftToExtended G P ∉
      (theDeformedCode proc).stabilizerGroup) :
    gaugingSpacetimeFaultDistance proc proc.detectorOfIndex
      (FullOutcomePreserving proc) =
    proc.phase3Start - proc.phase2Start := by
  rw [spacetimeFaultDistance_eq_d proc origCode hJ hchecks_eq
    hconn hcard hexact hexact_boundary hexp hL_logical
    hDeformedHasLogicals hd_eq P hPlog hPpureX hPweight hnotDeformedStab]
  exact (phase2_duration proc).symm

/-- Space code distance d* ≥ d when h(G) ≥ 1. -/
theorem deformed_distance_ge_d
    (origCode : StabilizerCode V)
    (hJ : origCode.I = J)
    (hchecks_eq : ∀ j : J, origCode.check (hJ ▸ j) = checks j)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V)
    (hexact : ∀ (γ : G.edgeSet → ZMod 2),
      γ ∈ LinearMap.ker (GraphMaps.secondCoboundaryMap G cycles) →
      ∃ c : V → ZMod 2, GraphMaps.coboundaryMap G c = γ)
    (hexact_boundary : ∀ (δ : G.edgeSet → ZMod 2),
      δ ∈ LinearMap.ker (GraphMaps.boundaryMap G) →
      δ ∈ LinearMap.range (GraphMaps.secondBoundaryMap G cycles))
    (hexp : SufficientExpansion G)
    (hL_logical : origCode.isLogicalOp (GaugingMeasurementCorrectness.logicalOpV (V := V)))
    (hDeformedHasLogicals : ∃ P : PauliOp (ExtQubit G),
      (theDeformedCode proc).isLogicalOp P) :
    origCode.distance ≤
      (deformedStabilizerCode G cycles checks proc.deformedData
        proc.cycleParity proc.checks_commute).distance :=
  sufficient_expansion_gives_dstar_ge_d G cycles checks origCode hJ hchecks_eq
    proc.deformedData proc.cycleParity proc.checks_commute
    hconn hcard hexact hexact_boundary hexp hL_logical
    (by exact hDeformedHasLogicals)

end FaultTolerantGaugingDistance
