import QEC1.Remarks.Rem_2_GraphConvention
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Sort

/-!
# Rem_6: Circuit Implementation of the Gauging Procedure

## Statement
The gauging procedure can be implemented by a quantum circuit with no additional ancilla qubits
beyond the edge qubits. After initializing the edge qubits in |0⟩, perform the entangling circuit
∏_v ∏_{e ∋ v} CX_{v→e} where CX_{v→e} is a controlled-X gate with control qubit v and target
qubit e. Next, projectively measure X_v on all vertices v ∈ G and keep the post-measurement state.
Then repeat the same entangling circuit ∏_v ∏_{e ∋ v} CX_{v→e}. Finally, measure Z_e on all
edge qubits and discard them.

## Main Definitions
- `CircuitStep` : The steps of the gauging circuit
- `GaugingCircuit` : The complete gauging circuit specification
- `CXGate` : A controlled-X (CNOT) gate specification
- `EntanglingCircuit` : The product ∏_v ∏_{e ∋ v} CX_{v→e}

## Main Results
- `no_additional_ancilla` : The circuit uses only edge qubits as ancilla
- `circuit_sequence` : The complete circuit is init → entangle → measure X → entangle → measure Z
- `entangling_circuit_eq` : The two entangling circuits are identical

## Key Properties
The circuit has five phases:
1. Initialize edge qubits in |0⟩
2. Apply entangling circuit ∏_v ∏_{e ∋ v} CX_{v→e}
3. Measure X_v on all vertices and keep post-measurement state
4. Apply the same entangling circuit again
5. Measure Z_e on all edges and discard
-/

namespace QEC1

open SimpleGraph Finset

/-! ## Controlled-X (CNOT) Gate -/

/-- A controlled-X gate specification with control and target qubits -/
structure CXGate (QubitType : Type*) where
  /-- The control qubit -/
  control : QubitType
  /-- The target qubit -/
  target : QubitType
  /-- Control and target are different -/
  control_ne_target : control ≠ target

instance {QubitType : Type*} [DecidableEq QubitType] : DecidableEq (CXGate QubitType) :=
  fun g1 g2 => by
    cases g1; cases g2
    simp only [CXGate.mk.injEq]
    infer_instance

namespace CXGate

variable {QubitType : Type*} [DecidableEq QubitType]

-- CX gate represented abstractly as just the gate specification

end CXGate

/-! ## Circuit Steps -/

/-- The phases of the gauging circuit -/
inductive CircuitPhase where
  /-- Phase 1: Initialize edge qubits in |0⟩ -/
  | InitializeEdges : CircuitPhase
  /-- Phase 2: Apply first entangling circuit ∏_v ∏_{e ∋ v} CX_{v→e} -/
  | FirstEntangling : CircuitPhase
  /-- Phase 3: Measure X_v on all vertices -/
  | MeasureXVertices : CircuitPhase
  /-- Phase 4: Apply second entangling circuit (same as first) -/
  | SecondEntangling : CircuitPhase
  /-- Phase 5: Measure Z_e on all edges and discard -/
  | MeasureZEdges : CircuitPhase
  deriving DecidableEq, Repr

namespace CircuitPhase

/-- The natural ordering of circuit phases -/
def toNat : CircuitPhase → ℕ
  | InitializeEdges => 0
  | FirstEntangling => 1
  | MeasureXVertices => 2
  | SecondEntangling => 3
  | MeasureZEdges => 4

instance : Fintype CircuitPhase where
  elems := {InitializeEdges, FirstEntangling, MeasureXVertices, SecondEntangling, MeasureZEdges}
  complete := fun p => by cases p <;> simp

/-- The circuit has exactly 5 phases -/
theorem num_phases : Fintype.card CircuitPhase = 5 := rfl

/-- Phase ordering -/
instance : LT CircuitPhase := ⟨fun p q => p.toNat < q.toNat⟩

instance : DecidableRel (· < · : CircuitPhase → CircuitPhase → Prop) :=
  fun p q => Nat.decLt p.toNat q.toNat

/-- InitializeEdges is the first phase -/
@[simp] lemma initializeEdges_first (p : CircuitPhase) :
    InitializeEdges.toNat ≤ p.toNat := by
  cases p <;> simp [toNat]

/-- MeasureZEdges is the last phase -/
@[simp] lemma measureZEdges_last (p : CircuitPhase) :
    p.toNat ≤ MeasureZEdges.toNat := by
  cases p <;> simp [toNat]

end CircuitPhase

/-! ## Entangling Circuit Structure -/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The entangling circuit ∏_v ∏_{e ∋ v} CX_{v→e} for a graph G.

    For each vertex v, for each edge e incident to v, apply CX with control v and target e.
    The edges are represented as Sym2 V elements from the graph's edge set. -/
structure EntanglingCircuit (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The underlying graph -/
  graph : SimpleGraph V := G
  /-- The CX gates are parameterized by (vertex, incident edge) pairs -/
  gates_spec : ∀ v : V, ∀ e ∈ G.incidenceFinset v, CXGate (V ⊕ Sym2 V) :=
    fun v e _ => {
      control := Sum.inl v
      target := Sum.inr e
      control_ne_target := Sum.inl_ne_inr
    }

namespace EntanglingCircuit

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The number of CX gates equals ∑_v deg(v) = 2|E| -/
theorem num_gates_eq_twice_edges (_E : EntanglingCircuit G) :
    (Finset.univ.sum (fun v => G.degree v)) = 2 * G.edgeFinset.card := by
  exact G.sum_degrees_eq_twice_card_edges

/-- Each vertex contributes deg(v) CX gates -/
theorem vertex_contributes_degree (v : V) :
    (G.incidenceFinset v).card = G.degree v := by
  exact G.card_incidenceFinset_eq_degree v

end EntanglingCircuit

/-! ## Measurement Specifications -/

/-- Specification of measuring Pauli X on a set of qubits -/
structure XMeasurementSpec (QubitType : Type*) [DecidableEq QubitType] where
  /-- The qubits to measure -/
  qubits : Finset QubitType
  /-- Whether to keep or discard each qubit after measurement -/
  keep : QubitType → Bool

/-- Specification of measuring Pauli Z on a set of qubits -/
structure ZMeasurementSpec (QubitType : Type*) [DecidableEq QubitType] where
  /-- The qubits to measure -/
  qubits : Finset QubitType
  /-- Whether to keep or discard each qubit after measurement -/
  keep : QubitType → Bool

/-! ## Complete Gauging Circuit -/

/-- The complete gauging circuit implementing the gauging procedure.

    The circuit uses:
    - Vertex qubits (V): the original code qubits in supp(L)
    - Edge qubits (E_G): auxiliary qubits, one per edge

    No additional ancilla qubits are required beyond the edge qubits.

    The circuit proceeds in 5 phases:
    1. Initialize edge qubits in |0⟩
    2. Apply ∏_v ∏_{e ∋ v} CX_{v→e}
    3. Measure X_v on all vertices, keep post-measurement state
    4. Apply ∏_v ∏_{e ∋ v} CX_{v→e} (same circuit as step 2)
    5. Measure Z_e on all edges and discard -/
structure GaugingCircuit (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The underlying graph -/
  graph : SimpleGraph V := G
  /-- First entangling circuit -/
  entangling1 : EntanglingCircuit G
  /-- X measurement on vertices (keep the state) -/
  xMeasurement : XMeasurementSpec V
  /-- Second entangling circuit (should be identical to first) -/
  entangling2 : EntanglingCircuit G
  /-- Z measurement on edges (discard after) -/
  zMeasurement : ZMeasurementSpec (Sym2 V)
  /-- The two entangling circuits are identical -/
  entangling_identical : entangling1 = entangling2
  /-- X measurement covers all vertices -/
  x_covers_all : xMeasurement.qubits = Finset.univ
  /-- X measurement keeps qubits -/
  x_keeps : ∀ v, xMeasurement.keep v = true
  /-- Z measurement covers all edges -/
  z_covers_all : zMeasurement.qubits = G.edgeFinset
  /-- Z measurement discards qubits -/
  z_discards : ∀ e, zMeasurement.keep e = false

namespace GaugingCircuit

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Key Properties -/

/-- The two entangling circuits are identical -/
theorem entangling_circuits_identical (C : GaugingCircuit G) :
    C.entangling1 = C.entangling2 := C.entangling_identical

/-- All edge qubits are initialized (from Rem_2 convention) -/
theorem edge_qubits_initialized (_C : GaugingCircuit G) (_e : Sym2 V) (_he : _e ∈ G.edgeFinset) :
    QubitType.initialState QubitType.EdgeQubit = QubitType.InitialState.zero := by
  rfl

/-- X measurements are performed on all vertices -/
theorem x_measurement_all_vertices (C : GaugingCircuit G) :
    C.xMeasurement.qubits = Finset.univ := C.x_covers_all

/-- X measurement keeps the post-measurement state -/
theorem x_measurement_keeps_state (C : GaugingCircuit G) (v : V) :
    C.xMeasurement.keep v = true := C.x_keeps v

/-- Z measurements are performed on all edges -/
theorem z_measurement_all_edges (C : GaugingCircuit G) :
    C.zMeasurement.qubits = G.edgeFinset := C.z_covers_all

/-- Z measurement discards the edge qubits -/
theorem z_measurement_discards (C : GaugingCircuit G) (e : Sym2 V) :
    C.zMeasurement.keep e = false := C.z_discards e

/-! ## No Additional Ancilla Property -/

/-- The qubit types used in the circuit -/
inductive CircuitQubit (G : SimpleGraph V) where
  /-- Vertex qubit (original code qubit) -/
  | vertex : V → CircuitQubit G
  /-- Edge qubit (auxiliary gauge qubit) -/
  | edge : Sym2 V → CircuitQubit G
  deriving DecidableEq

/-- The set of all qubits used in the circuit -/
def allQubits (_C : GaugingCircuit G) : Finset (CircuitQubit G) :=
  (Finset.univ.image CircuitQubit.vertex) ∪
  (G.edgeFinset.image CircuitQubit.edge)

/-- No additional ancilla beyond edge qubits: every qubit is either a vertex or edge qubit -/
theorem no_additional_ancilla (C : GaugingCircuit G) :
    ∀ q ∈ C.allQubits, (∃ v, q = CircuitQubit.vertex v) ∨ (∃ e, e ∈ G.edgeFinset ∧ q = CircuitQubit.edge e) := by
  intro q hq
  simp only [allQubits, mem_union, mem_image, mem_univ, true_and, mem_edgeFinset] at hq
  cases hq with
  | inl h =>
    obtain ⟨v, hv⟩ := h
    left
    exact ⟨v, hv.symm⟩
  | inr h =>
    obtain ⟨e, he, heq⟩ := h
    right
    exact ⟨e, mem_edgeFinset.mpr he, heq.symm⟩

/-- Helper: check if a circuit qubit is an edge qubit -/
def CircuitQubit.isEdge : CircuitQubit G → Bool
  | CircuitQubit.edge _ => true
  | CircuitQubit.vertex _ => false

/-- The ancilla qubits are exactly the edge qubits -/
theorem ancilla_are_edges (C : GaugingCircuit G) :
    (C.allQubits.filter (fun q => q.isEdge)) =
    G.edgeFinset.image CircuitQubit.edge := by
  ext q
  simp only [mem_filter, allQubits, mem_union, mem_image, mem_univ, true_and, mem_edgeFinset,
    CircuitQubit.isEdge]
  constructor
  · intro ⟨hmem, hfilter⟩
    cases q with
    | vertex v => simp at hfilter
    | edge e =>
      cases hmem with
      | inl h =>
        obtain ⟨v, hv⟩ := h
        simp at hv
      | inr h => exact h
  · intro ⟨e, he, heq⟩
    constructor
    · right
      exact ⟨e, he, heq⟩
    · subst heq
      rfl

/-! ## Circuit Depth Analysis -/

/-- The circuit consists of exactly 5 phases -/
theorem circuit_has_five_phases : Fintype.card CircuitPhase = 5 :=
  CircuitPhase.num_phases

/-- The phases execute in order -/
theorem phase_order :
    CircuitPhase.InitializeEdges.toNat < CircuitPhase.FirstEntangling.toNat ∧
    CircuitPhase.FirstEntangling.toNat < CircuitPhase.MeasureXVertices.toNat ∧
    CircuitPhase.MeasureXVertices.toNat < CircuitPhase.SecondEntangling.toNat ∧
    CircuitPhase.SecondEntangling.toNat < CircuitPhase.MeasureZEdges.toNat := by
  simp only [CircuitPhase.toNat]
  omega

end GaugingCircuit

/-! ## Default Circuit Construction -/

/-- Construct the default gauging circuit for a graph G -/
def mkGaugingCircuit (G : SimpleGraph V) [DecidableRel G.Adj] : GaugingCircuit G where
  graph := G
  entangling1 := ⟨G, fun v e _ => {
    control := Sum.inl v
    target := Sum.inr e
    control_ne_target := Sum.inl_ne_inr
  }⟩
  xMeasurement := {
    qubits := Finset.univ
    keep := fun _ => true
  }
  entangling2 := ⟨G, fun v e _ => {
    control := Sum.inl v
    target := Sum.inr e
    control_ne_target := Sum.inl_ne_inr
  }⟩
  zMeasurement := {
    qubits := G.edgeFinset
    keep := fun _ => false
  }
  entangling_identical := rfl
  x_covers_all := rfl
  x_keeps := fun _ => rfl
  z_covers_all := rfl
  z_discards := fun _ => rfl

/-- The circuit sequence as a list of phases -/
def circuitSequence : List CircuitPhase :=
  [CircuitPhase.InitializeEdges,
   CircuitPhase.FirstEntangling,
   CircuitPhase.MeasureXVertices,
   CircuitPhase.SecondEntangling,
   CircuitPhase.MeasureZEdges]

theorem circuitSequence_length : circuitSequence.length = 5 := rfl

/-- The circuit sequence is strictly increasing in phase order -/
theorem circuitSequence_pairwise : circuitSequence.Pairwise (· < ·) := by
  decide

/-! ## CX Gate Count -/

/-- Total number of CX gates in one entangling circuit -/
noncomputable def numCXGates (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sum (fun v => G.degree v)

omit [DecidableEq V] in
/-- The number of CX gates equals 2|E| (each edge contributes 2 gates) -/
theorem numCXGates_eq_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    numCXGates G = 2 * G.edgeFinset.card := by
  unfold numCXGates
  exact G.sum_degrees_eq_twice_card_edges

/-- Total CX gates in the full circuit (both entangling rounds) -/
noncomputable def totalCXGates (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  2 * numCXGates G

omit [DecidableEq V] in
/-- Total CX gates equals 4|E| -/
theorem totalCXGates_eq_four_times_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    totalCXGates G = 4 * G.edgeFinset.card := by
  unfold totalCXGates
  rw [numCXGates_eq_twice_edges]
  omega

/-! ## Summary

The gauging procedure circuit implementation:
1. **Initialization**: Edge qubits start in |0⟩ (no extra work for logical qubits)
2. **First Entangling**: ∏_v ∏_{e ∋ v} CX_{v→e} creates correlations
3. **X Measurement**: Projectively measure X on all vertices, keep results
4. **Second Entangling**: Repeat the same CX pattern
5. **Z Measurement**: Measure Z on all edges and discard

Key efficiency:
- No additional ancilla beyond edge qubits
- Number of CX gates = 4|E| (twice 2|E| per entangling round)
- Circuit depth is constant (5 phases)
-/

end QEC1
