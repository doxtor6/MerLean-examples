import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import QEC1.Remarks.Rem_2_NotationPauliOperators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Definition 5: Gauging Measurement Algorithm

## Statement
The gauging measurement procedure measures a logical operator L = ∏_{v ∈ V} X_v
by introducing auxiliary edge qubits, measuring Gauss's law operators A_v and
edge qubits Z_e, and applying byproduct corrections.

We formalize the classical data and processing of the algorithm:
- Measurement outcomes (ε_v for Gauss's law, ω_e for edge qubits)
- The sign σ = ∏_v ε_v that gives the measurement result
- The byproduct correction rule based on walk parities
- Additivity of walk parity under concatenation and reversal
- The Gauss's law operators and edge Z operators being measured
- Commutativity of all measured operators

We use ZMod 2 for measurement outcomes: 0 ↔ +1, 1 ↔ -1.
Products of ±1 values correspond to sums in ZMod 2.

## Main Results
- `GaugingInput` : the input data for the gauging procedure
- `GaugingOutcomes` : the measurement outcomes (ε_v, ω_e)
- `measurementSign` : the sign σ = ∑_v ε_v (in ZMod 2)
- `walkParity` : the parity of ω along a walk
- `byproductCorrectionAt` : the correction at vertex v given a specific walk from v₀
- `gaugingAlgorithm` : the full classical output of the algorithm
- `walkParity_append` : additivity under concatenation
- `walkParity_reverse` : invariance under reversal
- `walkParity_well_defined` : two walks give the same parity when closed walks have zero parity
- `gaussLaw_product_gives_logical` : ∏_v A_v = L
- `gaussLaw_measured_commute` : Gauss measurements commute
- `edgeZ_measured_commute` : edge measurements commute

## Corollaries
- Sign characterization lemmas
- Walk parity algebra
- Measurement operator identifications
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GaugingMeasurement

open Finset PauliOp GaussFlux

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## Input Data -/

/-- The input data for the gauging measurement procedure.
    - A connected graph G = (V, E) with V = support of the logical operator L = ∏_v X_v
    - A distinguished base vertex v₀ ∈ V for byproduct correction -/
structure GaugingInput where
  /-- The base vertex v₀ ∈ V -/
  baseVertex : V
  /-- The graph G is connected -/
  connected : G.Connected

/-! ## Measurement Outcomes -/

/-- The measurement outcomes from the gauging procedure.
    We use ZMod 2 to represent ±1 outcomes: 0 ↔ +1, 1 ↔ -1.
    Products of ±1 correspond to sums in ZMod 2.

    - gaussOutcome v : the outcome ε_v of measuring Gauss's law operator A_v
    - edgeOutcome e : the outcome ω_e of measuring Z_e -/
structure GaugingOutcomes where
  /-- Gauss's law measurement outcomes: ε_v for each v ∈ V -/
  gaussOutcome : V → ZMod 2
  /-- Edge Z-measurement outcomes: ω_e for each e ∈ E -/
  edgeOutcome : G.edgeSet → ZMod 2

/-! ## Sign Computation -/

/-- The measurement sign σ = ∏_v ε_v, encoded as ∑_v ε_v in ZMod 2.
    This is the measurement result of the logical L = ∏_v X_v:
    σ = 0 (in ZMod 2) means the +1 eigenvalue, σ = 1 means -1. -/
def measurementSign (outcomes : GaugingOutcomes G) : ZMod 2 :=
  ∑ v : V, outcomes.gaussOutcome v

@[simp]
theorem measurementSign_def (outcomes : GaugingOutcomes G) :
    measurementSign G outcomes = ∑ v : V, outcomes.gaussOutcome v := rfl

/-! ## Walk Parity -/

/-- Given edge measurement outcomes ω and a walk in G, compute the parity
    of ω along the walk: the ZMod 2 sum of ω(e) over all edges e traversed.
    This is ∑_{d ∈ walk.darts} ω(d.edge) in ZMod 2.

    An edge traversed by dart d has d.edge ∈ G.edgeSet (from d.adj). -/
noncomputable def walkParity (ω : G.edgeSet → ZMod 2)
    {u v : V} (w : G.Walk u v) : ZMod 2 :=
  (w.darts.map (fun d => ω ⟨d.edge, G.mem_edgeSet.mpr d.adj⟩)).sum

@[simp]
theorem walkParity_nil (ω : G.edgeSet → ZMod 2) (v : V) :
    walkParity G ω (SimpleGraph.Walk.nil : G.Walk v v) = 0 := by
  simp [walkParity, SimpleGraph.Walk.darts]

theorem walkParity_cons (ω : G.edgeSet → ZMod 2)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkParity G ω (SimpleGraph.Walk.cons h p) =
    ω ⟨s(u, v), G.mem_edgeSet.mpr h⟩ + walkParity G ω p := by
  simp only [walkParity, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons,
    SimpleGraph.Dart.edge_mk, SimpleGraph.Dart.adj]

/-! ## Walk Parity Algebra -/

/-- Walk parity is additive under concatenation. -/
theorem walkParity_append (ω : G.edgeSet → ZMod 2)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkParity G ω (p.append q) = walkParity G ω p + walkParity G ω q := by
  induction p with
  | nil => simp [walkParity]
  | cons h p' ih =>
    rw [SimpleGraph.Walk.cons_append, walkParity_cons, walkParity_cons, ih]
    ring

/-- Walk parity is invariant under reversal (since we work in ZMod 2,
    and reversing traverses the same edges as Sym2 elements). -/
theorem walkParity_reverse (ω : G.edgeSet → ZMod 2)
    {u v : V} (p : G.Walk u v) :
    walkParity G ω p.reverse = walkParity G ω p := by
  induction p with
  | nil => simp
  | @cons a b c h p' ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkParity_append, walkParity_cons,
        walkParity_nil, walkParity_cons, ih]
    have : ω ⟨s(b, a), G.mem_edgeSet.mpr (G.symm h)⟩ =
           ω ⟨s(a, b), G.mem_edgeSet.mpr h⟩ := by
      congr 1; exact Subtype.ext Sym2.eq_swap
    rw [this]; ring

/-- Walk parity of a single-edge walk. -/
theorem walkParity_single (ω : G.edgeSet → ZMod 2)
    {u v : V} (h : G.Adj u v) :
    walkParity G ω (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) =
    ω ⟨s(u, v), G.mem_edgeSet.mpr h⟩ := by
  rw [walkParity_cons, walkParity_nil, add_zero]

/-- The difference of walk parities along two paths from u to v equals
    the parity of the closed walk formed by going along p then back along q. -/
theorem walkParity_diff_eq_closed (ω : G.edgeSet → ZMod 2)
    {u v : V} (p q : G.Walk u v) :
    walkParity G ω p + walkParity G ω q =
    walkParity G ω (p.append q.reverse) := by
  rw [walkParity_append, walkParity_reverse]

/-- If all closed walks have zero parity, then the walk parity from u to v
    is independent of the choice of walk. -/
theorem walkParity_well_defined (ω : G.edgeSet → ZMod 2)
    (hclosed : ∀ (v : V) (c : G.Walk v v), walkParity G ω c = 0)
    {u v : V} (p q : G.Walk u v) :
    walkParity G ω p = walkParity G ω q := by
  have h := hclosed u (p.append q.reverse)
  rw [walkParity_append, walkParity_reverse] at h
  have : walkParity G ω p + walkParity G ω q = 0 := h
  exact CharTwo.add_eq_zero.mp this

/-! ## Byproduct Correction -/

/-- The byproduct correction at vertex v, given a specific walk from v₀ to v.
    This is the parity of edge outcomes along the walk:
    c(v) = ∑_{e ∈ γ} ω_e (in ZMod 2).

    c(v) = 1 means "apply X_v" (corresponding to ∏_{e ∈ γ} ω_e = -1 in ±1 notation). -/
noncomputable def byproductCorrectionAt (ω : G.edgeSet → ZMod 2)
    {v₀ v : V} (γ : G.Walk v₀ v) : ZMod 2 :=
  walkParity G ω γ

/-- The byproduct correction at the base vertex using the trivial walk is 0. -/
@[simp]
theorem byproductCorrectionAt_self (ω : G.edgeSet → ZMod 2) (v₀ : V) :
    byproductCorrectionAt G ω (SimpleGraph.Walk.nil : G.Walk v₀ v₀) = 0 := by
  simp [byproductCorrectionAt]

/-- The byproduct correction is well-defined (independent of walk choice)
    when all closed walks have zero parity. -/
theorem byproductCorrectionAt_well_defined (ω : G.edgeSet → ZMod 2)
    (hclosed : ∀ (v : V) (c : G.Walk v v), walkParity G ω c = 0)
    {v₀ v : V} (γ₁ γ₂ : G.Walk v₀ v) :
    byproductCorrectionAt G ω γ₁ = byproductCorrectionAt G ω γ₂ :=
  walkParity_well_defined G ω hclosed γ₁ γ₂

/-- The byproduct correction Pauli operator for a given walk assignment:
    for each vertex v, apply X_v iff c(v) = 1. -/
noncomputable def byproductCorrectionOp
    {v₀ : V} (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2) :
    PauliOp V where
  xVec := fun v => byproductCorrectionAt G ω (walks v)
  zVec := 0

/-- The byproduct correction operator is pure X-type. -/
theorem byproductCorrectionOp_pure_X
    {v₀ : V} (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2) :
    (byproductCorrectionOp G walks ω).zVec = 0 := rfl

/-- The byproduct correction operator is self-inverse (in the Pauli group). -/
theorem byproductCorrectionOp_mul_self
    {v₀ : V} (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2) :
    byproductCorrectionOp G walks ω *
    byproductCorrectionOp G walks ω = 1 := by
  ext v
  · simp only [mul_xVec, Pi.add_apply, one_xVec, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · simp only [mul_zVec, Pi.add_apply, one_zVec, Pi.zero_apply,
        byproductCorrectionOp, add_zero]

/-! ## The Gauging Measurement Algorithm -/

/-- The classical output of the gauging measurement algorithm. -/
structure GaugingResult (V : Type*) where
  /-- The measurement sign: 0 ↔ +1 eigenvalue of L, 1 ↔ -1 eigenvalue -/
  sign : ZMod 2
  /-- The byproduct correction vector: c(v) = 1 means apply X_v -/
  correction : V → ZMod 2

/-- The gauging measurement algorithm: given input data, measurement outcomes,
    and a choice of walks from v₀ to each vertex, computes the classical output.

    - sign = ∑_v ε_v (the product of all Gauss outcomes in ZMod 2)
    - correction(v) = walkParity(γ_v, ω) (the parity of edge outcomes along the walk) -/
noncomputable def gaugingAlgorithm (input : GaugingInput G)
    (outcomes : GaugingOutcomes G)
    (walks : (v : V) → G.Walk input.baseVertex v) : GaugingResult V where
  sign := measurementSign G outcomes
  correction := fun v => byproductCorrectionAt G outcomes.edgeOutcome (walks v)

/-- The sign is the sum of all Gauss's law measurement outcomes. -/
@[simp]
theorem gaugingAlgorithm_sign (input : GaugingInput G)
    (outcomes : GaugingOutcomes G)
    (walks : (v : V) → G.Walk input.baseVertex v) :
    (gaugingAlgorithm G input outcomes walks).sign =
    ∑ v : V, outcomes.gaussOutcome v := rfl

/-- Two different walk choices produce the same correction vector when
    all closed walks have zero parity. -/
theorem gaugingAlgorithm_correction_independent (input : GaugingInput G)
    (outcomes : GaugingOutcomes G)
    (walks₁ walks₂ : (v : V) → G.Walk input.baseVertex v)
    (hclosed : ∀ (v : V) (c : G.Walk v v), walkParity G outcomes.edgeOutcome c = 0) :
    (gaugingAlgorithm G input outcomes walks₁).correction =
    (gaugingAlgorithm G input outcomes walks₂).correction := by
  funext v
  exact byproductCorrectionAt_well_defined G outcomes.edgeOutcome hclosed (walks₁ v) (walks₂ v)

/-! ## Sign Characterization -/

/-- σ = 0 (mod 2) means the +1 eigenvalue of L was measured. -/
def signIsPlus (outcomes : GaugingOutcomes G) : Prop :=
  measurementSign G outcomes = 0

/-- σ = 1 (mod 2) means the -1 eigenvalue of L was measured. -/
def signIsMinus (outcomes : GaugingOutcomes G) : Prop :=
  measurementSign G outcomes = 1

-- In ZMod 2, every element is 0 or 1.
private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- The sign is always 0 or 1 in ZMod 2. -/
theorem sign_dichotomy (outcomes : GaugingOutcomes G) :
    signIsPlus G outcomes ∨ signIsMinus G outcomes :=
  zmod2_eq_zero_or_one (measurementSign G outcomes)

/-! ## Measured Operators -/

/-- The Gauss's law operator measured at vertex v in step 3:
    A_v = X_v ∏_{e ∋ v} X_e on the extended qubit system V ⊕ E. -/
abbrev gaussLawOperatorMeasured (v : V) : PauliOp (ExtQubit G) :=
  gaussLawOp G v

/-- The edge Z operator measured at edge e in step 4: Z_e on V ⊕ E. -/
abbrev edgeZOperatorMeasured (e : G.edgeSet) : PauliOp (ExtQubit G) :=
  PauliOp.pauliZ (Sum.inr e)

/-! ## Commutativity of Measured Operators -/

/-- All Gauss's law operators commute: they can be measured in any order in step 3. -/
theorem gaussLaw_measured_commute (v w : V) :
    PauliCommute (gaussLawOperatorMeasured G v) (gaussLawOperatorMeasured G w) :=
  gaussLaw_commute G v w

/-- All edge Z operators commute: they can be measured in any order in step 4. -/
theorem edgeZ_measured_commute (e₁ e₂ : G.edgeSet) :
    PauliCommute (edgeZOperatorMeasured G e₁) (edgeZOperatorMeasured G e₂) := by
  simp only [edgeZOperatorMeasured, PauliCommute, symplecticInner, pauliZ]
  apply Finset.sum_eq_zero
  intro q _
  simp [Pi.zero_apply]

/-- The product of all Gauss's law operators equals the logical L = ∏_v X_v.
    This is why σ = ∏_v ε_v gives the measurement result of L. -/
theorem gaussLaw_product_gives_logical :
    ∏ v : V, gaussLawOperatorMeasured G v = logicalOp G :=
  gaussLaw_product G

/-! ## Edge Z Operators are Pure Z-Type -/

/-- The edge Z operator Z_e is pure Z-type: no X-support. -/
@[simp]
theorem edgeZOperatorMeasured_xVec (e : G.edgeSet) :
    (edgeZOperatorMeasured G e).xVec = 0 := by
  simp [edgeZOperatorMeasured, pauliZ]

/-- The Gauss's law operator A_v is pure X-type: no Z-support. -/
@[simp]
theorem gaussLawOperatorMeasured_zVec (v : V) :
    (gaussLawOperatorMeasured G v).zVec = 0 := by
  simp [gaussLawOperatorMeasured]

/-! ## Self-Inverse Property of Measured Operators -/

/-- Each Gauss's law operator is self-inverse: A_v * A_v = 1. -/
theorem gaussLawOperatorMeasured_mul_self (v : V) :
    gaussLawOperatorMeasured G v * gaussLawOperatorMeasured G v = 1 :=
  PauliOp.mul_self _

/-- Each edge Z operator is self-inverse: Z_e * Z_e = 1. -/
theorem edgeZOperatorMeasured_mul_self (e : G.edgeSet) :
    edgeZOperatorMeasured G e * edgeZOperatorMeasured G e = 1 :=
  PauliOp.mul_self _

end GaugingMeasurement
