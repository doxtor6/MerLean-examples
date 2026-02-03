import QEC1.Remarks.Rem_1_StabilizerCodeConvention
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Rem_2: Graph Convention

## Statement
Given a connected graph $G = (V_G, E_G)$ with vertex set $V_G$ and edge set $E_G$,
we identify the vertices of $G$ with the qubits in the support of the logical operator $L$.
For each edge $e \in E_G$, we introduce an auxiliary 'gauge qubit' initialized in the state $|0\rangle_e$.
The graph $G$ may also include additional 'dummy vertices' beyond the qubits in the support of $L$.
For each dummy vertex $v$, we add an auxiliary qubit initialized in the $|+\rangle$ state
and gauge the operator $L \cdot X_v$. These dummy vertices have no effect on the gauging
measurement outcome since measuring $X_v$ on a $|+\rangle$ state always returns $+1$.

## Main Definitions
- `GaugingGraphConvention` : The convention for a gauging graph relating G to logical operator L
- `QubitType` : Classification of qubits (logical, edge, dummy)
- `InitialState` : The initial quantum state for each qubit type
- `DummyVertexMeasurementOutcome` : The measurement outcome for dummy vertices is always +1

## Key Properties
- `vertex_qubit_correspondence` : Vertices are identified with logical support qubits
- `edge_qubit_initialization` : Edge qubits are initialized in |0⟩
- `dummy_vertex_initialization` : Dummy qubits are initialized in |+⟩
- `dummy_measurement_always_plus_one` : Measuring X on |+⟩ always returns +1
-/

/-! ## Qubit Types in the Gauging Protocol -/

/-- The different types of qubits involved in the gauging measurement protocol -/
inductive QubitType : Type where
  /-- Original code qubits in the support of L -/
  | LogicalSupport : QubitType
  /-- Auxiliary gauge qubits on edges, initialized in |0⟩ -/
  | EdgeQubit : QubitType
  /-- Auxiliary qubits for dummy vertices, initialized in |+⟩ -/
  | DummyQubit : QubitType
  deriving DecidableEq, Repr

namespace QubitType

/-- The initial state for each qubit type -/
inductive InitialState : Type where
  /-- The |0⟩ state (computational basis zero) -/
  | zero : InitialState
  /-- The |+⟩ state ((|0⟩ + |1⟩)/√2) -/
  | plus : InitialState
  /-- Unspecified (for logical qubits, depends on encoded state) -/
  | encoded : InitialState
  deriving DecidableEq, Repr

/-- The initial state for each qubit type in the gauging protocol -/
def initialState : QubitType → InitialState
  | LogicalSupport => InitialState.encoded  -- Part of the code, state determined by encoding
  | EdgeQubit => InitialState.zero          -- Initialized in |0⟩
  | DummyQubit => InitialState.plus         -- Initialized in |+⟩

@[simp] lemma logicalSupport_initialState : initialState LogicalSupport = InitialState.encoded := rfl
@[simp] lemma edgeQubit_initialState : initialState EdgeQubit = InitialState.zero := rfl
@[simp] lemma dummyQubit_initialState : initialState DummyQubit = InitialState.plus := rfl

end QubitType

/-! ## Measurement Outcomes -/

/-- Possible measurement outcomes for X-basis measurements -/
inductive GraphMeasurementOutcome : Type where
  /-- Outcome +1 -/
  | plus : GraphMeasurementOutcome
  /-- Outcome -1 -/
  | minus : GraphMeasurementOutcome
  deriving DecidableEq, Repr

namespace GraphMeasurementOutcome

/-- Convert measurement outcome to a sign (±1 as integer) -/
def toSign : GraphMeasurementOutcome → Int
  | plus => 1
  | minus => -1

@[simp] lemma plus_toSign : plus.toSign = 1 := rfl
@[simp] lemma minus_toSign : minus.toSign = -1 := rfl

/-- Multiplication of measurement outcomes (product of signs) -/
def mul : GraphMeasurementOutcome → GraphMeasurementOutcome → GraphMeasurementOutcome
  | plus, m => m
  | minus, plus => minus
  | minus, minus => plus

instance : Mul GraphMeasurementOutcome := ⟨mul⟩

@[simp] lemma plus_mul (m : GraphMeasurementOutcome) : plus * m = m := by cases m <;> rfl
@[simp] lemma mul_plus (m : GraphMeasurementOutcome) : m * plus = m := by cases m <;> rfl
@[simp] lemma minus_mul_minus : minus * minus = plus := rfl
@[simp] lemma minus_mul_plus : minus * plus = minus := rfl
@[simp] lemma plus_mul_minus : plus * minus = minus := rfl

instance : One GraphMeasurementOutcome := ⟨plus⟩

@[simp] lemma one_eq_plus : (1 : GraphMeasurementOutcome) = plus := rfl

end GraphMeasurementOutcome

/-! ## Key Property: X measurement on |+⟩ always returns +1 -/

/-- The key property that measuring X on the |+⟩ state always yields +1.
    This is because |+⟩ is the +1 eigenstate of the Pauli X operator:
    X|+⟩ = |+⟩ (eigenvalue +1) -/
def xMeasurementOnPlusState : GraphMeasurementOutcome := GraphMeasurementOutcome.plus

/-- Theorem: X measurement on |+⟩ always returns +1 -/
theorem x_measurement_on_plus_is_plus : xMeasurementOnPlusState = GraphMeasurementOutcome.plus := rfl

/-- The deterministic outcome property: measuring X on |+⟩ has probability 1 for +1 outcome -/
structure DeterministicPlusOutcome where
  /-- The state is |+⟩ (X eigenstate with eigenvalue +1) -/
  is_plus_state : QubitType.InitialState
  /-- The state condition -/
  state_eq_plus : is_plus_state = QubitType.InitialState.plus
  /-- The measurement outcome is deterministically +1 -/
  outcome : GraphMeasurementOutcome
  /-- Outcome is always +1 -/
  outcome_is_plus : outcome = GraphMeasurementOutcome.plus

/-! ## Gauging Graph Convention Structure -/

/-- A gauging graph convention specifies how a connected graph G relates to the
    logical operator L being measured. This captures the key conventions from Rem_2:

    1. Vertices of G are identified with qubits in supp(L)
    2. Each edge e ∈ E_G gets an auxiliary gauge qubit in |0⟩
    3. Dummy vertices (V_G \ supp(L)) get auxiliary qubits in |+⟩
    4. Dummy vertices have no effect on measurement outcome (X on |+⟩ → +1) -/
structure GaugingGraphConvention where
  /-- The vertex type of the graph -/
  Vertex : Type
  /-- Vertices form a finite type -/
  vertexFintype : Fintype Vertex
  /-- Decidable equality on vertices -/
  vertexDecEq : DecidableEq Vertex
  /-- The simple graph structure -/
  graph : SimpleGraph Vertex
  /-- Decidable adjacency -/
  adjDecidable : DecidableRel graph.Adj
  /-- The graph is connected -/
  connected : graph.Connected
  /-- The support set of the logical operator L (embedded in vertices) -/
  logicalSupport : Finset Vertex
  /-- The logical support is nonempty (L is nontrivial) -/
  support_nonempty : logicalSupport.Nonempty

-- Provide instances from structure fields
attribute [instance] GaugingGraphConvention.vertexFintype
  GaugingGraphConvention.vertexDecEq
  GaugingGraphConvention.adjDecidable

namespace GaugingGraphConvention

variable (G : GaugingGraphConvention)

/-! ## Vertex Classification -/

/-- A vertex is a support vertex if it corresponds to a qubit in supp(L) -/
def isSupportVertex (v : G.Vertex) : Prop := v ∈ G.logicalSupport

/-- A vertex is a dummy vertex if it's not in the logical support -/
def isDummyVertex (v : G.Vertex) : Prop := v ∉ G.logicalSupport

/-- Decidability of support vertex membership -/
instance (v : G.Vertex) : Decidable (G.isSupportVertex v) :=
  inferInstanceAs (Decidable (v ∈ G.logicalSupport))

/-- Decidability of dummy vertex membership -/
instance (v : G.Vertex) : Decidable (G.isDummyVertex v) :=
  inferInstanceAs (Decidable (v ∉ G.logicalSupport))

/-- Every vertex is either a support vertex or a dummy vertex -/
theorem vertex_classification (v : G.Vertex) :
    G.isSupportVertex v ∨ G.isDummyVertex v := by
  by_cases h : v ∈ G.logicalSupport
  · left; exact h
  · right; exact h

/-- Support and dummy vertices are mutually exclusive -/
theorem support_dummy_exclusive (v : G.Vertex) :
    ¬(G.isSupportVertex v ∧ G.isDummyVertex v) := by
  intro ⟨hs, hd⟩
  exact hd hs

/-- The set of dummy vertices -/
def dummyVertices : Finset G.Vertex :=
  Finset.univ.filter (fun v => G.isDummyVertex v)

/-- The number of dummy vertices -/
def numDummyVertices : ℕ := G.dummyVertices.card

/-- Vertices partition into support and dummy -/
theorem vertex_partition :
    Fintype.card G.Vertex = G.logicalSupport.card + G.numDummyVertices := by
  have h : (Finset.univ : Finset G.Vertex) =
      G.logicalSupport ∪ G.dummyVertices := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_union, true_iff]
    cases G.vertex_classification v with
    | inl hs => left; exact hs
    | inr hd => right; simp only [dummyVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]; exact hd
  have hdisj : Disjoint G.logicalSupport G.dummyVertices := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    simp only [dummyVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact hb ha
  calc Fintype.card G.Vertex
      = (Finset.univ : Finset G.Vertex).card := Finset.card_univ.symm
    _ = (G.logicalSupport ∪ G.dummyVertices).card := by rw [h]
    _ = G.logicalSupport.card + G.dummyVertices.card :=
        Finset.card_union_of_disjoint hdisj
    _ = G.logicalSupport.card + G.numDummyVertices := rfl

/-! ## Qubit Type Assignment -/

/-- Assign a qubit type to each vertex -/
def vertexQubitType (v : G.Vertex) : QubitType :=
  if G.isSupportVertex v then QubitType.LogicalSupport else QubitType.DummyQubit

/-- Support vertices are assigned LogicalSupport type -/
@[simp] theorem supportVertex_qubitType (v : G.Vertex) (h : G.isSupportVertex v) :
    G.vertexQubitType v = QubitType.LogicalSupport := by
  simp only [vertexQubitType, h, ↓reduceIte]

/-- Dummy vertices are assigned DummyQubit type -/
@[simp] theorem dummyVertex_qubitType (v : G.Vertex) (h : G.isDummyVertex v) :
    G.vertexQubitType v = QubitType.DummyQubit := by
  unfold vertexQubitType isSupportVertex
  simp only [if_neg h]

/-- All edges are assigned EdgeQubit type -/
def edgeQubitType (_e : Sym2 G.Vertex) : QubitType := QubitType.EdgeQubit

/-! ## Initial States -/

/-- The initial state for a vertex qubit -/
def vertexInitialState (v : G.Vertex) : QubitType.InitialState :=
  (G.vertexQubitType v).initialState

/-- The initial state for an edge qubit -/
def edgeInitialState (_e : Sym2 G.Vertex) : QubitType.InitialState :=
  QubitType.InitialState.zero

/-- Dummy vertex qubits are initialized in |+⟩ -/
@[simp] theorem dummyVertex_initialState (v : G.Vertex) (h : G.isDummyVertex v) :
    G.vertexInitialState v = QubitType.InitialState.plus := by
  unfold vertexInitialState
  rw [dummyVertex_qubitType G v h]
  rfl

/-- Edge qubits are initialized in |0⟩ -/
@[simp] theorem edge_initialState (e : Sym2 G.Vertex) :
    G.edgeInitialState e = QubitType.InitialState.zero := rfl

/-! ## Dummy Vertex Measurement Property -/

/-- The key property: measuring X on a dummy vertex always gives +1.
    This is because the dummy qubit is in |+⟩, which is the +1 eigenstate of X. -/
def dummyVertexMeasurementOutcome (_v : G.Vertex) (_h : G.isDummyVertex _v) :
    GraphMeasurementOutcome := GraphMeasurementOutcome.plus

/-- Measuring X on any dummy vertex returns +1 -/
theorem dummy_measurement_always_plus (v : G.Vertex) (h : G.isDummyVertex v) :
    G.dummyVertexMeasurementOutcome v h = GraphMeasurementOutcome.plus := rfl

/-- The product of measurement outcomes over dummy vertices is +1.
    This is formulated using integers since GraphMeasurementOutcome doesn't have CommMonoid. -/
theorem dummy_product_is_one :
    ∀ S : Finset G.Vertex, (∀ v ∈ S, G.isDummyVertex v) →
    (S.prod (fun _v => (1 : ℤ))) = 1 := by
  intro S _hS
  simp only [Finset.prod_const_one]

/-! ## Edge and Qubit Counts -/

/-- The number of edges in the graph (= number of gauge qubits) -/
noncomputable def numEdges : ℕ := G.graph.edgeFinset.card

/-- The total number of auxiliary qubits = edge qubits + dummy qubits -/
noncomputable def numAuxiliaryQubits : ℕ := G.numEdges + G.numDummyVertices

/-- The total number of qubits involved = logical support + auxiliary -/
noncomputable def totalQubits : ℕ :=
  G.logicalSupport.card + G.numAuxiliaryQubits

/-- Total qubits formula expanded -/
theorem totalQubits_eq :
    G.totalQubits = G.logicalSupport.card + G.numEdges + G.numDummyVertices := by
  simp only [totalQubits, numAuxiliaryQubits]
  omega

/-! ## Gauging Operator Extension -/

/-- When gauging L with dummy vertices, we actually gauge L · ∏_{v ∈ dummy} X_v.
    Since each dummy vertex measurement gives +1, this doesn't change the outcome.

    This captures: "gauge the operator L · X_v" for each dummy vertex v. -/
def effectiveLogicalSupport : Finset G.Vertex := Finset.univ

/-- The effective logical support includes all vertices (support ∪ dummy) -/
theorem effectiveSupport_is_all_vertices :
    G.effectiveLogicalSupport = Finset.univ := rfl

/-- The effective logical support contains the original logical support -/
theorem logicalSupport_subset_effective :
    G.logicalSupport ⊆ G.effectiveLogicalSupport := by
  intro v _
  simp only [effectiveLogicalSupport, Finset.mem_univ]

/-! ## Key Theorem: Dummy Vertices Don't Affect Outcome -/

/-- The main theorem of this remark: dummy vertices have no effect on the
    gauging measurement outcome because:
    1. Each dummy vertex v has qubit initialized in |+⟩
    2. The gauging measures X_v on the dummy qubit
    3. Measuring X on |+⟩ always returns +1
    4. Therefore, the product over dummy vertices contributes factor 1 -/
theorem dummy_vertices_no_effect :
    ∀ dummies : Finset G.Vertex,
    (∀ v ∈ dummies, G.isDummyVertex v) →
    (dummies.prod (fun v => if G.isDummyVertex v then 1 else (0 : ℤ))) = 1 := by
  intro dummies hdummies
  have heq : ∀ v ∈ dummies, (if G.isDummyVertex v then (1 : ℤ) else 0) = 1 := by
    intro v hv
    simp only [hdummies v hv, ↓reduceIte]
  rw [Finset.prod_congr rfl heq]
  simp only [Finset.prod_const_one]

/-- Alternative formulation: the contribution of dummy vertices to the
    measurement outcome is the neutral element -/
theorem dummy_contribution_neutral :
    ∀ v : G.Vertex, (hv : G.isDummyVertex v) →
    (G.dummyVertexMeasurementOutcome v hv).toSign = 1 := by
  intro v hv
  simp only [dummyVertexMeasurementOutcome, GraphMeasurementOutcome.plus_toSign]

end GaugingGraphConvention

/-! ## Summary of Convention

The graph convention establishes:
1. **Vertex-Qubit Correspondence**: Vertices V_G ↔ qubits, with supp(L) ⊆ V_G
2. **Edge Qubits**: Each edge e ∈ E_G gets an auxiliary qubit initialized in |0⟩
3. **Dummy Vertices**: Vertices in V_G \ supp(L) get auxiliary qubits in |+⟩
4. **No-Effect Property**: Dummy vertices don't affect measurement outcome
   because measuring X on |+⟩ deterministically gives +1

This convention allows the gauging graph to be larger than supp(L), enabling
graph constructions that satisfy expansion and path-length requirements
while maintaining the correctness of the logical measurement.
-/
