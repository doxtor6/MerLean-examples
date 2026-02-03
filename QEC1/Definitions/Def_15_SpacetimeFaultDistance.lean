import QEC1.Definitions.Def_14_SpacetimeStabilizer

/-!
# Spacetime Fault-Distance (Definition 15)

## Statement
The **spacetime fault-distance** of the fault-tolerant gauging measurement procedure is:
$$d_{\text{ST}} = \min\{|F| : F \text{ is a spacetime logical fault}\}$$

where $|F|$ counts single-qubit Pauli errors plus single measurement errors.

Equivalently, $d_{\text{ST}}$ is the minimum weight of an undetectable fault pattern
that is not equivalent to a spacetime stabilizer.

## Main Results
**Main Definition** (`SpacetimeFaultDistance`): The spacetime fault-distance d_ST
**Main Theorem** (`spacetimeFaultDistance_is_min`): d_ST is minimum weight of logical fault
**Equivalence** (`spacetimeFaultDistance_equiv`): Alternative characterization

## File Structure
1. Set of Logical Faults: The set of all spacetime logical fault weights
2. Spacetime Fault Distance: d_ST as minimum of logical fault weights
3. Basic Properties: Positivity, lower/upper bounds
4. Helper Lemmas: simp lemmas and basic facts
-/

namespace QEC

/-! ## Section 1: Set of Logical Fault Weights

We define the set of weights of all spacetime logical faults. The spacetime fault-distance
is the minimum of this set. -/

/-- The set of weights of spacetime logical faults.
    W = {|F| : F is a spacetime logical fault} -/
def logicalFaultWeights {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) : Set ℕ :=
  { w | ∃ F : SpaceTimeFault n m,
        IsSpacetimeLogicalFaultConcrete C F detectors ∧ F.weight = w }

/-- Alternative characterization: weights of undetectable non-stabilizer faults -/
def undetectableNonStabilizerWeights {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) : Set ℕ :=
  { w | ∃ F : SpaceTimeFault n m,
      isUndetectable F detectors ∧
      ¬actsTriviallyOnMeasurement C F ∧
      F.weight = w }

/-- The two weight sets are equal (undetectable non-stabilizer = logical fault) -/
theorem logicalFaultWeights_eq_undetectableNonStabilizer {n k m : ℕ}
    (C : StabilizerCode n k) (detectors : Finset (Detector n)) :
    logicalFaultWeights (m := m) C detectors =
    undetectableNonStabilizerWeights (m := m) C detectors := by
  ext w
  simp only [logicalFaultWeights, undetectableNonStabilizerWeights,
             IsSpacetimeLogicalFaultConcrete, Set.mem_setOf_eq]
  constructor
  · intro ⟨F, ⟨hund, hnottriv⟩, heq⟩
    exact ⟨F, hund, hnottriv, heq⟩
  · intro ⟨F, hund, hnottriv, heq⟩
    exact ⟨F, ⟨hund, hnottriv⟩, heq⟩

/-! ## Section 2: Spacetime Fault Distance Definition

The spacetime fault-distance is the minimum weight of any spacetime logical fault. -/

/-- Predicate: there exists at least one spacetime logical fault -/
def hasLogicalFault {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) : Prop :=
  ∃ F : SpaceTimeFault n m, IsSpacetimeLogicalFaultConcrete C F detectors

/-- The spacetime fault-distance d_ST as a natural number.
    d_ST = min{|F| : F is a spacetime logical fault}

    If no logical faults exist (which would mean perfect error correction),
    we return 0 as a sentinel value. In practice, interesting codes always
    have logical faults, so d_ST > 0.

    We define this as the WellFounded.min of the logical fault weight set. -/
noncomputable def spacetimeFaultDistance {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) : ℕ :=
  @dite _ (hasLogicalFault (m := m) C detectors) (Classical.dec _)
    (fun h => WellFounded.min Nat.lt_wfRel.wf (logicalFaultWeights (m := m) C detectors) <| by
      obtain ⟨F, hF⟩ := h
      exact ⟨F.weight, F, hF, rfl⟩)
    (fun _ => 0)

/-! ## Section 3: Main Properties -/

/-- The spacetime fault distance is at most the weight of any logical fault -/
theorem spacetimeFaultDistance_le_weight {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (F : SpaceTimeFault n m)
    (hF : IsSpacetimeLogicalFaultConcrete C F detectors) :
    spacetimeFaultDistance (m := m) C detectors ≤ F.weight := by
  unfold spacetimeFaultDistance
  have hhas : hasLogicalFault (m := m) C detectors := ⟨F, hF⟩
  simp only [hhas, dite_true]
  apply WellFounded.min_le
  exact ⟨F, hF, rfl⟩

/-- The spacetime fault distance is a lower bound: all logical faults have weight ≥ d_ST -/
theorem weight_ge_spacetimeFaultDistance {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (F : SpaceTimeFault n m)
    (hF : IsSpacetimeLogicalFaultConcrete C F detectors) :
    F.weight ≥ spacetimeFaultDistance (m := m) C detectors :=
  spacetimeFaultDistance_le_weight C detectors F hF

/-- If logical faults exist, the minimum is achieved -/
theorem spacetimeFaultDistance_is_min {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : hasLogicalFault (m := m) C detectors) :
    ∃ F : SpaceTimeFault n m,
      IsSpacetimeLogicalFaultConcrete C F detectors ∧
      F.weight = spacetimeFaultDistance (m := m) C detectors := by
  unfold spacetimeFaultDistance
  simp only [h, dite_true]
  have hne : (logicalFaultWeights (m := m) C detectors).Nonempty := by
    obtain ⟨F, hF⟩ := h
    exact ⟨F.weight, F, hF, rfl⟩
  have hmin := WellFounded.min_mem Nat.lt_wfRel.wf (logicalFaultWeights (m := m) C detectors) hne
  obtain ⟨F, hFlog, hFw⟩ := hmin
  exact ⟨F, hFlog, hFw⟩

/-- If no logical faults exist, d_ST = 0 -/
theorem spacetimeFaultDistance_zero_of_no_logical {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : ¬hasLogicalFault (m := m) C detectors) :
    spacetimeFaultDistance (m := m) C detectors = 0 := by
  unfold spacetimeFaultDistance
  simp only [h, dite_false]

/-! ## Section 4: Properties of Spacetime Fault Distance -/

/-- A fault with weight < d_ST cannot be a logical fault -/
theorem not_logical_of_weight_lt {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (F : SpaceTimeFault n m)
    (hF : F.weight < spacetimeFaultDistance (m := m) C detectors) :
    ¬IsSpacetimeLogicalFaultConcrete C F detectors := by
  intro hlog
  have hge := spacetimeFaultDistance_le_weight C detectors F hlog
  omega

/-- A fault with weight < d_ST is either detectable or a stabilizer -/
theorem detectable_or_stabilizer_if_weight_lt {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (F : SpaceTimeFault n m)
    (hF : F.weight < spacetimeFaultDistance (m := m) C detectors) :
    ¬isUndetectable F detectors ∨ actsTriviallyOnMeasurement C F := by
  by_contra h
  push_neg at h
  have hlog : IsSpacetimeLogicalFaultConcrete C F detectors := ⟨h.1, h.2⟩
  exact not_logical_of_weight_lt C detectors F hF hlog

/-! ## Section 5: Spacetime Fault Distance Structure

We provide a structure that bundles a code, detectors, and proof that
the spacetime fault distance is well-defined and achieves its minimum. -/

/-- Structure bundling the spacetime fault distance with a witness achieving the minimum -/
structure SpacetimeFaultDistanceWitness (n k m : ℕ) (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) where
  /-- The minimum weight logical fault (witness) -/
  witness : SpaceTimeFault n m
  /-- The witness is a logical fault -/
  isLogical : IsSpacetimeLogicalFaultConcrete C witness detectors
  /-- The witness achieves the minimum -/
  achievesMin : witness.weight = spacetimeFaultDistance (m := m) C detectors

namespace SpacetimeFaultDistanceWitness

variable {n k m : ℕ} {C : StabilizerCode n k} {detectors : Finset (Detector n)}

/-- The distance value -/
noncomputable def distance (_w : SpacetimeFaultDistanceWitness n k m C detectors) : ℕ :=
  spacetimeFaultDistance (m := m) C detectors

/-- Distance equals witness weight -/
@[simp]
theorem distance_eq_weight (w : SpacetimeFaultDistanceWitness n k m C detectors) :
    w.distance = w.witness.weight := w.achievesMin.symm

/-- The witness is undetectable -/
theorem witness_undetectable (w : SpacetimeFaultDistanceWitness n k m C detectors) :
    isUndetectable w.witness detectors := w.isLogical.1

/-- The witness is not a stabilizer -/
theorem witness_not_stabilizer (w : SpacetimeFaultDistanceWitness n k m C detectors) :
    ¬actsTriviallyOnMeasurement C w.witness := w.isLogical.2

end SpacetimeFaultDistanceWitness

/-- Construct a witness from the existence of logical faults -/
noncomputable def mkSpacetimeFaultDistanceWitness {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : hasLogicalFault (m := m) C detectors) :
    SpacetimeFaultDistanceWitness n k m C detectors :=
  Classical.choice <| by
    obtain ⟨F, hF, heq⟩ := spacetimeFaultDistance_is_min C detectors h
    exact ⟨⟨F, hF, heq⟩⟩

/-! ## Section 6: Fault-Tolerance Threshold

A code can tolerate faults of weight t if t < d_ST.
This section establishes the relationship between fault tolerance and d_ST. -/

/-- A code can tolerate weight-t faults if t < d_ST -/
def canTolerateFaults {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (t : ℕ) : Prop :=
  t < spacetimeFaultDistance (m := m) C detectors

/-- If the code can tolerate weight t, any fault of weight ≤ t is correctable or stabilizer -/
theorem tolerable_implies_correctable {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (t : ℕ)
    (htol : canTolerateFaults (m := m) C detectors t)
    (F : SpaceTimeFault n m) (hF : F.weight ≤ t) :
    ¬isUndetectable F detectors ∨ actsTriviallyOnMeasurement C F := by
  have hlt : F.weight < spacetimeFaultDistance (m := m) C detectors := by
    unfold canTolerateFaults at htol
    omega
  exact detectable_or_stabilizer_if_weight_lt C detectors F hlt

/-- The maximum tolerable fault weight is d_ST - 1 (when d_ST > 0) -/
theorem max_tolerable_weight {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n))
    (hpos : 0 < spacetimeFaultDistance (m := m) C detectors) :
    canTolerateFaults (m := m) C detectors
      (spacetimeFaultDistance (m := m) C detectors - 1) := by
  unfold canTolerateFaults
  omega

/-! ## Section 7: Helper Lemmas -/

/-- The spacetime fault distance is non-negative -/
@[simp]
theorem spacetimeFaultDistance_nonneg {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) :
    0 ≤ spacetimeFaultDistance (m := m) C detectors :=
  Nat.zero_le _

/-- Logical fault weights are bounded below by d_ST -/
theorem logicalFaultWeights_bounded_below {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) :
    ∀ w ∈ logicalFaultWeights (m := m) C detectors,
      spacetimeFaultDistance (m := m) C detectors ≤ w := by
  intro w hw
  obtain ⟨F, hF, heq⟩ := hw
  rw [← heq]
  exact spacetimeFaultDistance_le_weight C detectors F hF

/-- If d_ST is achieved, the witness set is nonempty -/
theorem logicalFaultWeights_nonempty_of_hasLogical {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : hasLogicalFault (m := m) C detectors) :
    (logicalFaultWeights (m := m) C detectors).Nonempty := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.weight, F, hF, rfl⟩

/-- d_ST ∈ logicalFaultWeights when logical faults exist -/
theorem spacetimeFaultDistance_mem_weights {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : hasLogicalFault (m := m) C detectors) :
    spacetimeFaultDistance (m := m) C detectors ∈
      logicalFaultWeights (m := m) C detectors := by
  obtain ⟨F, hF, heq⟩ := spacetimeFaultDistance_is_min C detectors h
  exact ⟨F, hF, heq⟩

/-- A fault of weight exactly d_ST exists when logical faults exist -/
theorem exists_logical_of_exact_distance {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : hasLogicalFault (m := m) C detectors) :
    ∃ F : SpaceTimeFault n m,
      IsSpacetimeLogicalFaultConcrete C F detectors ∧
      F.weight = spacetimeFaultDistance (m := m) C detectors :=
  spacetimeFaultDistance_is_min C detectors h

/-! ## Section 8: d_ST > 0 Characterization -/

/-- d_ST > 0 iff there exist logical faults and all have positive weight -/
theorem spacetimeFaultDistance_pos_iff {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) :
    0 < spacetimeFaultDistance (m := m) C detectors ↔
    hasLogicalFault (m := m) C detectors ∧
    ∀ F : SpaceTimeFault n m,
      IsSpacetimeLogicalFaultConcrete C F detectors → 0 < F.weight := by
  constructor
  · intro hpos
    constructor
    · by_contra h
      rw [spacetimeFaultDistance_zero_of_no_logical C detectors h] at hpos
      exact Nat.not_lt_zero 0 hpos
    · intro F hF
      have hge := spacetimeFaultDistance_le_weight C detectors F hF
      omega
  · intro ⟨hhas, hpos⟩
    obtain ⟨F, hF, heq⟩ := spacetimeFaultDistance_is_min C detectors hhas
    rw [← heq]
    exact hpos F hF

/-! ## Section 9: Equivalent Characterization -/

/-- The spacetime fault distance is equivalently:
    d_ST = min{|F| : F is undetectable and not a spacetime stabilizer} -/
theorem spacetimeFaultDistance_equiv_undetectable {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : hasLogicalFault (m := m) C detectors) :
    ∃ F : SpaceTimeFault n m,
      isUndetectable F detectors ∧
      ¬actsTriviallyOnMeasurement C F ∧
      F.weight = spacetimeFaultDistance (m := m) C detectors := by
  obtain ⟨F, hF, heq⟩ := spacetimeFaultDistance_is_min C detectors h
  exact ⟨F, hF.1, hF.2, heq⟩

/-! ## Section 10: Basic Facts About Distance -/

/-- Distance is well-defined: if logical faults exist, d_ST is their minimum -/
theorem spacetimeFaultDistance_spec {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (h : hasLogicalFault (m := m) C detectors) :
    (∀ F : SpaceTimeFault n m,
      IsSpacetimeLogicalFaultConcrete C F detectors →
      spacetimeFaultDistance (m := m) C detectors ≤ F.weight) ∧
    (∃ F : SpaceTimeFault n m,
      IsSpacetimeLogicalFaultConcrete C F detectors ∧
      F.weight = spacetimeFaultDistance (m := m) C detectors) := by
  constructor
  · exact fun F hF => spacetimeFaultDistance_le_weight C detectors F hF
  · exact spacetimeFaultDistance_is_min C detectors h

/-! ## Section 11: Relationship to Stabilizer Code -/

/-- The distance depends on the stabilizer structure -/
theorem distance_depends_on_stabilizer {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) (F : SpaceTimeFault n m)
    (hF : IsSpacetimeLogicalFaultConcrete C F detectors) :
    ¬spaceFaultsAreStabilizer C F.spaceFaults ∨ ¬timeFaultsCancel F.timeFaults := by
  have hnottriv := hF.2
  unfold actsTriviallyOnMeasurement at hnottriv
  push_neg at hnottriv
  tauto

/-- Empty fault is not a logical fault (it's a stabilizer) -/
theorem empty_not_logical {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n)) :
    ¬IsSpacetimeLogicalFaultConcrete C
      (SpaceTimeFault.empty : SpaceTimeFault n m) detectors := by
  intro h
  have htriv : actsTriviallyOnMeasurement C
      (SpaceTimeFault.empty : SpaceTimeFault n m) := actsTrivially_empty C
  exact h.2 htriv

/-- If d_ST > 0, weight-0 undetectable faults must be stabilizers.
    This shows that d_ST is a meaningful measure of code quality. -/
theorem distance_pos_means_nontrivial {n k m : ℕ} (C : StabilizerCode n k)
    (detectors : Finset (Detector n))
    (hpos : 0 < spacetimeFaultDistance (m := m) C detectors) :
    ∀ F : SpaceTimeFault n m,
      F.weight = 0 → isUndetectable F detectors →
      actsTriviallyOnMeasurement C F := by
  intro F hw hund
  by_contra hnottriv
  have hlog : IsSpacetimeLogicalFaultConcrete C F detectors := ⟨hund, hnottriv⟩
  have hge := spacetimeFaultDistance_le_weight C detectors F hlog
  omega

end QEC
