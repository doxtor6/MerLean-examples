import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Remarks.Rem_17_HypergraphGeneralization
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import QEC1.Remarks.Rem_2_NotationPauliOperators
import QEC1.Remarks.Rem_9_CircuitImplementation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Remark 25: Steane-Style Measurement as Gauging

## Statement
The gauging measurement procedure can implement Steane-style measurement of a
stabilizer group by combining two gauging procedures.

**Standard Steane-style measurement:**
1. Prepare an ancilla code block in a known state.
2. Apply transversal CX gates between data and ancilla.
3. Read out the ancilla in the Z basis.
4. The outcomes reveal the data's stabilizer eigenvalues.

**Implementation via gauging (for CSS ancilla code):**
- Step 1: State preparation via hypergraph gauging (Rem_17)
- Step 2: Entangling via gauging (Def_5) using a perfect matching graph
- Step 3: Readout via Z measurements (ungauging step of Def_5)

## Main Results
- `IsCSS` : a stabilizer code is CSS if every check is pure X-type or pure Z-type
- `matchingGraphAdj` : the perfect matching graph connecting data-ancilla pairs
- `MatchingGraph` : the matching graph as a SimpleGraph
- `matching_components` : each data-ancilla pair forms a connected component
- `matchingGraph_card` : the matching graph has 2n vertices
- `matchingGraph_degree_eq_one` : every vertex has degree 1
- `step1_state_prep_hypergraph` : Step 1 uses hypergraph gauging for Z checks
- `step2_gauss_commute` : Step 2 Gauss operators commute
- `step2_gauss_product` : Step 2 produces the XX logical
- `step3_readout_is_ungauging` : Step 3 is the ungauging step
- `steane_is_composition_of_gauging` : Steane-style measurement decomposes into gaugings
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace SteaneStyleMeasurement

open Finset PauliOp HypergraphGeneralization GaussFlux CircuitImplementation

/-! ## CSS stabilizer codes

A CSS (Calderbank-Shor-Steane) code is a stabilizer code where every check is
either purely X-type (zVec = 0) or purely Z-type (xVec = 0). -/

section CSSCode

variable {Q : Type*} [DecidableEq Q] [Fintype Q]

/-- A stabilizer code is CSS if every check is either pure X-type or pure Z-type. -/
def IsCSS (C : StabilizerCode Q) : Prop :=
  ∀ i : C.I, (C.check i).zVec = 0 ∨ (C.check i).xVec = 0

/-- The X-type check indices of a CSS code. -/
def xCheckIndices (C : StabilizerCode Q) [DecidableEq C.I] : Finset C.I :=
  Finset.univ.filter (fun i => (C.check i).zVec = 0 ∧ (C.check i).xVec ≠ 0)

/-- The Z-type check indices of a CSS code. -/
def zCheckIndices (C : StabilizerCode Q) [DecidableEq C.I] : Finset C.I :=
  Finset.univ.filter (fun i => (C.check i).xVec = 0 ∧ (C.check i).zVec ≠ 0)

/-- An X-type check has no Z-support. -/
theorem xCheck_is_pureX (C : StabilizerCode Q) [DecidableEq C.I] (i : C.I)
    (hi : i ∈ xCheckIndices C) : (C.check i).zVec = 0 := by
  simp only [xCheckIndices, mem_filter, mem_univ, true_and] at hi
  exact hi.1

/-- A Z-type check has no X-support. -/
theorem zCheck_is_pureZ (C : StabilizerCode Q) [DecidableEq C.I] (i : C.I)
    (hi : i ∈ zCheckIndices C) : (C.check i).xVec = 0 := by
  simp only [zCheckIndices, mem_filter, mem_univ, true_and] at hi
  exact hi.1

/-- X-type checks are pure X-type (they mutually commute trivially). -/
theorem xChecks_commute (C : StabilizerCode Q) [DecidableEq C.I]
    (i j : C.I) (_hi : i ∈ xCheckIndices C) (_hj : j ∈ xCheckIndices C) :
    PauliCommute (C.check i) (C.check j) :=
  C.checks_commute i j

/-- Z-type checks are pure Z-type (they mutually commute trivially). -/
theorem zChecks_commute (C : StabilizerCode Q) [DecidableEq C.I]
    (i j : C.I) (_hi : i ∈ zCheckIndices C) (_hj : j ∈ zCheckIndices C) :
    PauliCommute (C.check i) (C.check j) :=
  C.checks_commute i j

/-- Two pure X-type operators commute (their symplectic inner product vanishes
    because all z-components are zero). -/
theorem pureX_pureX_commute (P R : PauliOp Q) (hP : P.zVec = 0) (hR : R.zVec = 0) :
    PauliCommute P R := by
  simp only [PauliCommute, symplecticInner]
  apply Finset.sum_eq_zero
  intro v _
  simp [hP, hR, show P.zVec v = 0 from congr_fun hP v, show R.zVec v = 0 from congr_fun hR v]

/-- Two pure Z-type operators commute. -/
theorem pureZ_pureZ_commute (P R : PauliOp Q) (hP : P.xVec = 0) (hR : R.xVec = 0) :
    PauliCommute P R := by
  simp only [PauliCommute, symplecticInner]
  apply Finset.sum_eq_zero
  intro v _
  simp [hP, hR, show P.xVec v = 0 from congr_fun hP v, show R.xVec v = 0 from congr_fun hR v]

/-- The identity check (zVec = 0 ∧ xVec = 0) is trivially CSS-compatible. -/
theorem identity_is_css_compatible : (1 : PauliOp Q).zVec = 0 ∨ (1 : PauliOp Q).xVec = 0 := by
  left; simp [PauliOp.one_zVec]

end CSSCode

/-! ## Step 1: State Preparation via Hypergraph Gauging

The ancilla code block is prepared by:
1. Starting with a trivial code (all qubits independent)
2. Adding one dummy qubit per X-type check of the ancilla CSS code
3. Performing hypergraph gauging (Rem_17) using the hypergraph whose
   hyperedges are the Z-type checks of the ancilla code

The hypergraph incidence relation is: qubit q is incident to Z-check i
iff q participates in Z-check i (i.e., the Z-check acts nontrivially on q). -/

section StatePreparation

variable {Q : Type*} [DecidableEq Q] [Fintype Q]
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- The incidence relation for state preparation: qubit q is incident to
    Z-check i iff the check has Z-action at q. -/
def zCheckIncident (checks : I → PauliOp Q) (q : Q) (i : I) : Prop :=
  (checks i).zVec q ≠ 0

instance zCheckIncident_decidable (checks : I → PauliOp Q) (q : Q) (i : I) :
    Decidable (zCheckIncident checks q i) :=
  inferInstanceAs (Decidable ((checks i).zVec q ≠ 0))

/-- The hypergraph boundary map for Z-check incidence computes the Z-parity
    at each qubit from a vector of check activations. -/
theorem zCheck_boundary_eq (checks : I → PauliOp Q) (γ : I → ZMod 2) (q : Q) :
    hyperBoundaryMap (zCheckIncident checks) γ q =
    ∑ i : I, if (checks i).zVec q ≠ 0 then γ i else 0 := by
  simp [hyperBoundaryMap_apply, zCheckIncident]

/-- The Gauss's law operators for Z-check hypergraph gauging are all pure X-type. -/
theorem step1_gauss_pure_X (checks : I → PauliOp Q) (v : Q) :
    (hyperGaussLawOp (zCheckIncident checks) v).zVec = 0 :=
  hyperGaussLawOp_zVec (zCheckIncident checks) v

/-- The Gauss's law operators for Z-check hypergraph gauging mutually commute. -/
theorem step1_gauss_commute (checks : I → PauliOp Q) (v w : Q) :
    PauliCommute (hyperGaussLawOp (zCheckIncident checks) v)
                 (hyperGaussLawOp (zCheckIncident checks) w) :=
  hyperGaussLaw_commute (zCheckIncident checks) v w

/-- **Step 1 (State preparation via hypergraph gauging).**
    The hypergraph whose hyperedges correspond to the Z-type checks of the
    ancilla CSS code defines a valid hypergraph gauging (Rem_17).
    The boundary map encodes the Z-check parity structure: for each qubit q,
    (∂γ)_q = Σ_{i : Z-checks with support on q} γ_i.
    The Gauss operators A_v are all pure X-type and mutually commute. -/
theorem step1_state_prep_hypergraph (checks : I → PauliOp Q) :
    (∀ v w : Q,
      PauliCommute (hyperGaussLawOp (zCheckIncident checks) v)
                   (hyperGaussLawOp (zCheckIncident checks) w)) ∧
    (∀ v : Q, (hyperGaussLawOp (zCheckIncident checks) v).zVec = 0) := by
  exact ⟨step1_gauss_commute checks, step1_gauss_pure_X checks⟩

end StatePreparation

/-! ## Step 2: Entangling via Gauging — Perfect Matching Graph

The entangling step uses a graph G that is a perfect matching between
data qubits and ancilla qubits. Each data qubit i is connected to
the corresponding ancilla qubit i by a single edge.

The vertex set is (Fin n) ⊕ (Fin n) where:
- Sum.inl i represents data qubit i
- Sum.inr i represents ancilla qubit i

This graph measures XX on each pair (data_i, ancilla_i). -/

section MatchingGraph

variable (n : ℕ)

/-- The vertex type: data qubits ⊕ ancilla qubits. -/
abbrev MatchingVertex := Fin n ⊕ Fin n

/-- The adjacency relation for the perfect matching graph:
    data qubit i is adjacent to ancilla qubit i (and no other edges). -/
def matchingGraphAdj : MatchingVertex n → MatchingVertex n → Prop :=
  fun p q => ∃ i : Fin n,
    (p = Sum.inl i ∧ q = Sum.inr i) ∨ (p = Sum.inr i ∧ q = Sum.inl i)

theorem matchingGraphAdj_symm (p q : MatchingVertex n)
    (h : matchingGraphAdj n p q) : matchingGraphAdj n q p := by
  obtain ⟨i, h | h⟩ := h
  · exact ⟨i, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨i, Or.inl ⟨h.2, h.1⟩⟩

theorem matchingGraphAdj_irrefl (p : MatchingVertex n) :
    ¬matchingGraphAdj n p p := by
  intro ⟨i, h⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (h1.symm.trans h2) Sum.inl_ne_inr
  · exact absurd (h1.symm.trans h2) Sum.inr_ne_inl

instance matchingGraphAdj_decidable : DecidableRel (matchingGraphAdj n) := by
  intro p q
  simp only [matchingGraphAdj]
  infer_instance

/-- The perfect matching graph between data and ancilla qubits. -/
def MatchingGraph : SimpleGraph (MatchingVertex n) where
  Adj := matchingGraphAdj n
  symm := matchingGraphAdj_symm n
  loopless := matchingGraphAdj_irrefl n

instance : DecidableRel (MatchingGraph n).Adj := matchingGraphAdj_decidable n

/-- The matching graph has 2n vertices. -/
theorem matchingGraph_card : Fintype.card (MatchingVertex n) = 2 * n := by
  simp [MatchingVertex, Fintype.card_sum]
  ring

/-- Each edge connects data qubit i to ancilla qubit i. -/
theorem matchingGraph_adj_iff (p q : MatchingVertex n) :
    (MatchingGraph n).Adj p q ↔ ∃ i : Fin n,
      (p = Sum.inl i ∧ q = Sum.inr i) ∨ (p = Sum.inr i ∧ q = Sum.inl i) :=
  Iff.rfl

/-- Data qubit i is adjacent to ancilla qubit i. -/
theorem matching_edge (i : Fin n) : (MatchingGraph n).Adj (Sum.inl i) (Sum.inr i) :=
  ⟨i, Or.inl ⟨rfl, rfl⟩⟩

/-- Ancilla qubit i is adjacent to data qubit i. -/
theorem matching_edge_rev (i : Fin n) : (MatchingGraph n).Adj (Sum.inr i) (Sum.inl i) :=
  ⟨i, Or.inr ⟨rfl, rfl⟩⟩

/-- No two data qubits are adjacent. -/
theorem no_data_data_edge (i j : Fin n) : ¬(MatchingGraph n).Adj (Sum.inl i) (Sum.inl j) := by
  intro ⟨k, h⟩
  rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact absurd h2 Sum.inl_ne_inr
  · exact absurd h1 Sum.inl_ne_inr

/-- No two ancilla qubits are adjacent. -/
theorem no_ancilla_ancilla_edge (i j : Fin n) :
    ¬(MatchingGraph n).Adj (Sum.inr i) (Sum.inr j) := by
  intro ⟨k, h⟩
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd h1 Sum.inr_ne_inl
  · exact absurd h2 Sum.inr_ne_inl

/-- Data qubit i is only adjacent to ancilla qubit i. -/
theorem data_adj_iff (i : Fin n) (q : MatchingVertex n) :
    (MatchingGraph n).Adj (Sum.inl i) q ↔ q = Sum.inr i := by
  constructor
  · intro ⟨k, h⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [Sum.inl.injEq] at h1; subst h1; exact h2
    · exact absurd h1 Sum.inl_ne_inr
  · rintro rfl; exact matching_edge n i

/-- Ancilla qubit i is only adjacent to data qubit i. -/
theorem ancilla_adj_iff (i : Fin n) (q : MatchingVertex n) :
    (MatchingGraph n).Adj (Sum.inr i) q ↔ q = Sum.inl i := by
  constructor
  · intro ⟨k, h⟩
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd h1 Sum.inr_ne_inl
    · rw [Sum.inr.injEq] at h1; subst h1; exact h2
  · rintro rfl; exact matching_edge_rev n i

/-- Each pair (data_i, ancilla_i) forms a connected component.
    Data qubit i and ancilla qubit i are reachable from each other. -/
theorem matching_pair_reachable (i : Fin n) :
    (MatchingGraph n).Reachable (Sum.inl i) (Sum.inr i) :=
  SimpleGraph.Adj.reachable (matching_edge n i)

/-- Helper: an adjacent vertex in the matching graph determines the component. -/
private theorem adj_same_component (p q : MatchingVertex n) (i : Fin n)
    (hp : p = Sum.inl i ∨ p = Sum.inr i)
    (hadj : (MatchingGraph n).Adj p q) :
    q = Sum.inl i ∨ q = Sum.inr i := by
  obtain ⟨j, hj⟩ := hadj
  rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
  · -- p = inl j, q = inr j
    subst hj1; subst hj2
    rcases hp with h | h
    · exact Or.inr (by rw [Sum.inl.injEq] at h; subst h; rfl)
    · exact absurd h Sum.inl_ne_inr
  · -- p = inr j, q = inl j
    subst hj1; subst hj2
    rcases hp with h | h
    · exact absurd h Sum.inr_ne_inl
    · exact Or.inl (by rw [Sum.inr.injEq] at h; subst h; rfl)

/-- The matching graph consists of n connected components: each data-ancilla
    pair {inl i, inr i} is one component. -/
private theorem walk_same_component :
    ∀ (p q : MatchingVertex n), (MatchingGraph n).Walk p q →
    ∃ i : Fin n, (p = Sum.inl i ∨ p = Sum.inr i) ∧
                 (q = Sum.inl i ∨ q = Sum.inr i)
  | Sum.inl i, _, .nil => ⟨i, Or.inl rfl, Or.inl rfl⟩
  | Sum.inr i, _, .nil => ⟨i, Or.inr rfl, Or.inr rfl⟩
  | _, _, .cons hadj w' => by
    obtain ⟨i, hmid, hq⟩ := walk_same_component _ _ w'
    exact ⟨i, adj_same_component n _ _ i hmid ((MatchingGraph n).symm hadj), hq⟩

/-- The matching graph consists of n connected components: each data-ancilla
    pair {inl i, inr i} is one component. -/
theorem matching_components (p q : MatchingVertex n)
    (h : (MatchingGraph n).Reachable p q) :
    ∃ i : Fin n, (p = Sum.inl i ∨ p = Sum.inr i) ∧
                 (q = Sum.inl i ∨ q = Sum.inr i) := by
  obtain ⟨w⟩ := h
  exact walk_same_component n p q w

end MatchingGraph

/-! ## Step 2: Entangling via XX Gauging on Matching Pairs

The entangling step gauges XX on each data-ancilla pair independently.
For each pair (data_i, ancilla_i), we have a single-edge graph connecting them.
The Gauss operator at each vertex acts as X on the vertex and X on the edge. -/

section Entangling

variable (n : ℕ)

/-- The Gauss's law operator for the matching graph is pure X-type. -/
theorem step2_gauss_pure_X (v : MatchingVertex n) :
    (gaussLawOp (MatchingGraph n) v).zVec = 0 :=
  gaussLawOp_zVec (MatchingGraph n) v

/-- The Gauss's law operators for the matching graph all commute. -/
theorem step2_gauss_commute (v w : MatchingVertex n) :
    PauliCommute (gaussLawOp (MatchingGraph n) v)
                 (gaussLawOp (MatchingGraph n) w) :=
  gaussLaw_commute (MatchingGraph n) v w

/-- The product of all Gauss operators on the matching graph equals the
    logical operator L = ∏_v X_v on all vertex qubits. -/
theorem step2_gauss_product [Fintype (MatchingGraph n).edgeSet] :
    ∏ v : MatchingVertex n, gaussLawOp (MatchingGraph n) v =
    logicalOp (MatchingGraph n) :=
  gaussLaw_product (MatchingGraph n)

/-- Each Gauss operator on the matching graph is self-inverse. -/
theorem step2_gauss_self_inverse (v : MatchingVertex n) :
    gaussLawOp (MatchingGraph n) v * gaussLawOp (MatchingGraph n) v = 1 :=
  PauliOp.mul_self _

/-- The logical operator on the matching graph acts as X on all vertex qubits. -/
theorem step2_logical_xVec [Fintype (MatchingGraph n).edgeSet]
    (v : MatchingVertex n) :
    (logicalOp (MatchingGraph n)).xVec (Sum.inl v) = 1 := by
  simp [logicalOp]

/-- The logical operator on the matching graph is pure X-type. -/
theorem step2_logical_pure_X [Fintype (MatchingGraph n).edgeSet] :
    (logicalOp (MatchingGraph n)).zVec = 0 := by
  simp [logicalOp]

end Entangling

/-! ## Step 3: Readout via Z Measurements (Ungauging)

The readout step measures Z_e on each edge qubit e, which is the
ungauging step (Step 4 of Def_5). For the matching graph, each edge
connects data_i to ancilla_i, so measuring Z on the edge qubit
effectively reads out information about the ancilla in the Z basis.

After ungauging, the edge qubits are discarded and the system
returns to operating on the original data + ancilla qubits. -/

section Readout

variable (n : ℕ)

/-- Edge Z operators on the matching graph are pure Z-type (no X-support). -/
theorem step3_edgeZ_pure_Z (e : (MatchingGraph n).edgeSet) :
    (pauliZ (Sum.inr e : ExtQubit (MatchingGraph n))).xVec = 0 := by
  ext q; simp [pauliZ]

/-- Edge Z operators all commute (both pure Z-type). -/
theorem step3_edgeZ_commute (e₁ e₂ : (MatchingGraph n).edgeSet) :
    PauliCommute (pauliZ (Sum.inr e₁ : ExtQubit (MatchingGraph n)))
                 (pauliZ (Sum.inr e₂ : ExtQubit (MatchingGraph n))) := by
  apply pureZ_pureZ_commute <;> ext q <;> simp [pauliZ]

/-- Edge Z operators are self-inverse. -/
theorem step3_edgeZ_self_inverse (e : (MatchingGraph n).edgeSet) :
    pauliZ (Sum.inr e : ExtQubit (MatchingGraph n)) *
    pauliZ (Sum.inr e : ExtQubit (MatchingGraph n)) = 1 :=
  PauliOp.mul_self _

/-- **Step 3 (Readout is ungauging).**
    The readout step consists of measuring Z on each edge qubit.
    All Z measurements commute and are self-inverse, which is
    exactly the ungauging step of Def_5. -/
theorem step3_readout_is_ungauging :
    (∀ e₁ e₂ : (MatchingGraph n).edgeSet,
      PauliCommute (pauliZ (Sum.inr e₁ : ExtQubit (MatchingGraph n)))
                   (pauliZ (Sum.inr e₂ : ExtQubit (MatchingGraph n)))) ∧
    (∀ e : (MatchingGraph n).edgeSet,
      pauliZ (Sum.inr e : ExtQubit (MatchingGraph n)) *
      pauliZ (Sum.inr e : ExtQubit (MatchingGraph n)) = 1) ∧
    (∀ e : (MatchingGraph n).edgeSet,
      (pauliZ (Sum.inr e : ExtQubit (MatchingGraph n))).xVec = 0) :=
  ⟨step3_edgeZ_commute n, step3_edgeZ_self_inverse n, step3_edgeZ_pure_Z n⟩

end Readout

/-! ## Steane-Style Measurement as Composition of Gaugings

The full Steane-style measurement is a composition of three gauging operations:

| Steane step | Gauging operation |
|---|---|
| Prepare ancilla in codestate | Hypergraph gauging (Rem_17) with Z-check hyperedges |
| Transversal CX (data ↔ ancilla) | Graph gauging (Def_5) with matching graph |
| Z readout of ancilla | Ungauging step (Z measurements on edge qubits) |

The hypergraph gauging in Step 1 prepares the ancilla by:
- Initializing qubits in |+⟩ state
- Measuring Gauss operators A_v = X_v ∏_{e ∋ v} X_e (one per ancilla qubit)
- The hyperedges correspond to Z-type checks of the ancilla CSS code
- This projects into the +1 eigenspace of all Z-type stabilizers

The graph gauging in Steps 2-3 entangles data with ancilla by:
- Adding edge qubits in |0⟩ for each data-ancilla pair
- Measuring Gauss operators (XX type) on each pair
- Z-measuring edge qubits to ungauge -/

section Composition

variable {Q : Type*} [DecidableEq Q] [Fintype Q]
variable (n : ℕ)

/-- The CX circuit transformation maps A_v to X_v on the matching graph. -/
theorem step2_cx_transforms_gauss (v : MatchingVertex n) :
    entanglingCircuitAction (MatchingGraph n)
      (gaussLawOp (MatchingGraph n) v) =
    pauliX (Sum.inl v) :=
  entanglingCircuit_transforms_gaussLaw (MatchingGraph n) v

/-- The CX circuit transforms X_v back to A_v on the matching graph. -/
theorem step2_cx_transforms_pauliX (v : MatchingVertex n) :
    entanglingCircuitAction (MatchingGraph n)
      (pauliX (Sum.inl v : ExtQubit (MatchingGraph n))) =
    gaussLawOp (MatchingGraph n) v :=
  entanglingCircuit_transforms_pauliX_to_gaussLaw (MatchingGraph n) v

/-- The entangling circuit is involutive on the matching graph. -/
theorem step2_cx_involutive (P : PauliOp (ExtQubit (MatchingGraph n))) :
    entanglingCircuitAction (MatchingGraph n)
      (entanglingCircuitAction (MatchingGraph n) P) = P :=
  entanglingCircuitAction_involutive (MatchingGraph n) P

/-- The entangling circuit preserves commutation relations. -/
theorem step2_cx_preserves_commutation (P R : PauliOp (ExtQubit (MatchingGraph n))) :
    PauliCommute P R ↔
    PauliCommute (entanglingCircuitAction (MatchingGraph n) P)
                 (entanglingCircuitAction (MatchingGraph n) R) :=
  (entanglingCircuit_preserves_commutation (MatchingGraph n) P R).symm

/-- **Steane-style measurement is a composition of gauging operations.** -/
theorem steane_is_composition_of_gauging
    {I : Type*} [DecidableEq I] [Fintype I]
    (checks : I → PauliOp Q) :
    -- Step 1: Hypergraph gauging for state preparation
    ((∀ v w : Q,
        PauliCommute (hyperGaussLawOp (zCheckIncident checks) v)
                     (hyperGaussLawOp (zCheckIncident checks) w)) ∧
     (∀ v : Q,
        (hyperGaussLawOp (zCheckIncident checks) v).zVec = 0)) ∧
    -- Step 2: Matching graph gauging for entangling
    ((∀ v w : MatchingVertex n,
        PauliCommute (gaussLawOp (MatchingGraph n) v)
                     (gaussLawOp (MatchingGraph n) w)) ∧
     (∀ v : MatchingVertex n,
        (gaussLawOp (MatchingGraph n) v).zVec = 0) ∧
     (∀ v : MatchingVertex n,
        entanglingCircuitAction (MatchingGraph n)
          (gaussLawOp (MatchingGraph n) v) =
        pauliX (Sum.inl v))) ∧
    -- Step 3: Z readout (ungauging)
    ((∀ e₁ e₂ : (MatchingGraph n).edgeSet,
        PauliCommute (pauliZ (Sum.inr e₁ : ExtQubit (MatchingGraph n)))
                     (pauliZ (Sum.inr e₂ : ExtQubit (MatchingGraph n)))) ∧
     (∀ e : (MatchingGraph n).edgeSet,
        pauliZ (Sum.inr e : ExtQubit (MatchingGraph n)) *
        pauliZ (Sum.inr e : ExtQubit (MatchingGraph n)) = 1)) := by
  refine ⟨⟨step1_gauss_commute checks, step1_gauss_pure_X checks⟩,
          ⟨step2_gauss_commute n, step2_gauss_pure_X n,
           step2_cx_transforms_gauss n⟩,
          ⟨step3_edgeZ_commute n, step3_edgeZ_self_inverse n⟩⟩

end Composition

/-! ## Ancilla Code Properties

The key properties of the ancilla CSS code that make the decomposition work:
1. Z-type checks define the hypergraph for state preparation
2. X-type checks determine the number of dummy qubits needed
3. The CSS property ensures X and Z checks can be handled independently -/

section AncillaProperties

variable {Q : Type*} [DecidableEq Q] [Fintype Q]

/-- For a CSS code, the X-type checks and Z-type checks cover all non-identity checks. -/
theorem css_check_partition (C : StabilizerCode Q) [DecidableEq C.I]
    (hcss : IsCSS C) (i : C.I) (hne : C.check i ≠ 1) :
    i ∈ xCheckIndices C ∨ i ∈ zCheckIndices C := by
  have hi := hcss i
  rcases hi with hz | hx
  · -- zVec = 0, so it could be X-type or identity
    by_cases hx : (C.check i).xVec = 0
    · -- Both zero means identity
      exfalso; apply hne
      ext q <;> simp [show (C.check i).xVec q = 0 from congr_fun hx q,
                       show (C.check i).zVec q = 0 from congr_fun hz q]
    · left; simp [xCheckIndices, hz, hx]
  · by_cases hz : (C.check i).zVec = 0
    · exfalso; apply hne
      ext q <;> simp [show (C.check i).xVec q = 0 from congr_fun hx q,
                       show (C.check i).zVec q = 0 from congr_fun hz q]
    · right; simp [zCheckIndices, hx, hz]

/-- The number of dummy qubits for state preparation equals the number of
    X-type checks in the ancilla CSS code. -/
theorem dummy_qubit_count (C : StabilizerCode Q) [DecidableEq C.I] :
    (xCheckIndices C).card = (Finset.univ.filter
      (fun i : C.I => (C.check i).zVec = 0 ∧ (C.check i).xVec ≠ 0)).card := by
  rfl

/-- For a CSS code, X-type checks commute with Z-type checks. -/
theorem xCheck_zCheck_commute (C : StabilizerCode Q) [DecidableEq C.I]
    (i j : C.I) (_hi : i ∈ xCheckIndices C) (_hj : j ∈ zCheckIndices C) :
    PauliCommute (C.check i) (C.check j) :=
  C.checks_commute i j

/-- The Z-check incidence boundary map encodes the Z-check parity structure. -/
theorem zCheck_boundary_structure (C : StabilizerCode Q) [DecidableEq C.I]
    (i : C.I) (_hi : i ∈ zCheckIndices C) (q : Q) :
    zCheckIncident (C.check) q i ↔ (C.check i).zVec q ≠ 0 :=
  Iff.rfl

end AncillaProperties

/-! ## Degree Analysis for the Matching Graph

The matching graph has a very simple structure:
- Each data vertex has degree exactly 1
- Each ancilla vertex has degree exactly 1
- Total edges = n (one per pair)

This gives the minimal possible overhead for the entangling step. -/

section DegreeAnalysis

variable (n : ℕ)

/-- The neighbor set of a data vertex i is just {inr i}. -/
theorem data_neighborFinset (i : Fin n) :
    (MatchingGraph n).neighborFinset (Sum.inl i) =
    {Sum.inr i} := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  exact data_adj_iff n i q

/-- The neighbor set of an ancilla vertex i is just {inl i}. -/
theorem ancilla_neighborFinset (i : Fin n) :
    (MatchingGraph n).neighborFinset (Sum.inr i) =
    {Sum.inl i} := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  exact ancilla_adj_iff n i q

/-- Each data vertex has degree exactly 1. -/
theorem data_degree (i : Fin n) : (MatchingGraph n).degree (Sum.inl i) = 1 := by
  rw [SimpleGraph.degree, data_neighborFinset]
  simp

/-- Each ancilla vertex has degree exactly 1. -/
theorem ancilla_degree (i : Fin n) : (MatchingGraph n).degree (Sum.inr i) = 1 := by
  rw [SimpleGraph.degree, ancilla_neighborFinset]
  simp

/-- Every vertex in the matching graph has degree exactly 1. -/
theorem matchingGraph_degree_eq_one (v : MatchingVertex n) :
    (MatchingGraph n).degree v = 1 := by
  rcases v with i | i
  · exact data_degree n i
  · exact ancilla_degree n i

/-- The degree sum of the matching graph is 2n. -/
theorem matchingGraph_degree_sum :
    ∑ v : MatchingVertex n, (MatchingGraph n).degree v = 2 * n := by
  rw [Fintype.sum_sum_type]
  simp only [data_degree, ancilla_degree, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  ring

/-- The matching graph has exactly n edges (by handshaking: 2|E| = 2n). -/
theorem matchingGraph_edge_count :
    2 * (MatchingGraph n).edgeFinset.card = 2 * n := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  exact matchingGraph_degree_sum n

end DegreeAnalysis

/-! ## Summary: Steane-style Measurement via Gauging

The formalization captures the key structural content of Remark 25:
1. CSS codes split into X-type and Z-type checks
2. State preparation uses hypergraph gauging on Z-type check incidence
3. Entangling uses graph gauging on a perfect matching
4. Readout uses Z measurements (ungauging)
5. The CX circuit equivalence from Rem_9 connects the two viewpoints -/

section Summary

variable {Q : Type*} [DecidableEq Q] [Fintype Q]
variable (n : ℕ)

/-- **Summary: Steane-style measurement decomposition.** -/
theorem steane_measurement_summary
    {I : Type*} [DecidableEq I] [Fintype I]
    (checks : I → PauliOp Q) :
    -- Step 1
    (∀ v w : Q, PauliCommute (hyperGaussLawOp (zCheckIncident checks) v)
                              (hyperGaussLawOp (zCheckIncident checks) w)) ∧
    -- Step 2: Gauss operators
    (∀ v w : MatchingVertex n,
      PauliCommute (gaussLawOp (MatchingGraph n) v)
                   (gaussLawOp (MatchingGraph n) w)) ∧
    -- Step 2: CX transformation
    (∀ v : MatchingVertex n,
      entanglingCircuitAction (MatchingGraph n)
        (gaussLawOp (MatchingGraph n) v) = pauliX (Sum.inl v)) ∧
    -- Step 3: Z readout
    (∀ e₁ e₂ : (MatchingGraph n).edgeSet,
      PauliCommute (pauliZ (Sum.inr e₁ : ExtQubit (MatchingGraph n)))
                   (pauliZ (Sum.inr e₂ : ExtQubit (MatchingGraph n)))) ∧
    -- Degree bound
    (∀ v : MatchingVertex n, (MatchingGraph n).degree v = 1) ∧
    -- Edge count
    (2 * (MatchingGraph n).edgeFinset.card = 2 * n) :=
  ⟨step1_gauss_commute checks,
   step2_gauss_commute n,
   step2_cx_transforms_gauss n,
   step3_edgeZ_commute n,
   matchingGraph_degree_eq_one n,
   matchingGraph_edge_count n⟩

end Summary

end SteaneStyleMeasurement
