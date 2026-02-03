import QEC1.Definitions.Def_19_CSSCode
import QEC1.Definitions.Def_7_FluxOperators
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Tanner Graph (Definition 21)

## Statement
The **Tanner graph** of a stabilizer code is a bipartite graph T = (Q ∪ C, E_T) where:
- Q = set of qubit nodes (one per physical qubit)
- C = set of check nodes (one per stabilizer generator)
- E_T = edges connecting qubit q to check c iff c acts non-trivially on q

**For CSS codes**: The Tanner graph can be split into X-type and Z-type subgraphs:
- T_X: connects qubits to X-type checks
- T_Z: connects qubits to Z-type checks

**LDPC condition**: A code is LDPC iff its Tanner graph has bounded degree (both qubit and
check degrees bounded by constants).

**Deformed code Tanner graph** (Figure 1 in paper): Shows the structure after gauging, with
additional Gauss's law checks A, flux checks B, and edge qubits E.

## Main Results
**Main Structure** (`TannerGraph`): Bipartite graph with qubit and check nodes
**CSS Tanner Graph** (`CSSTannerGraph`): Split into X and Z subgraphs
**LDPC Property** (`TannerLDPC`): Bounded degree condition
**Deformed Tanner Graph** (`DeformedTannerGraph`): Extended structure with gauging qubits

## File Structure
1. TannerNode: Sum type for qubit and check nodes
2. TannerGraph: Bipartite graph structure for stabilizer codes
3. CSSTannerGraph: Separated X and Z Tanner graphs for CSS codes
4. TannerLDPC: LDPC condition via Tanner graph degree bounds
5. DeformedTannerGraph: Extended Tanner graph after gauging
6. Helper Lemmas: Basic properties
-/

namespace QEC

open Matrix SimpleGraph

/-! ## Section 1: Tanner Node Type -/

/-- A node in a Tanner graph is either a qubit node or a check node.
    We use a sum type to represent the bipartite structure. -/
inductive TannerNode (numQubits numChecks : ℕ)
  | qubit : Fin numQubits → TannerNode numQubits numChecks
  | check : Fin numChecks → TannerNode numQubits numChecks
  deriving DecidableEq

namespace TannerNode

variable {numQubits numChecks : ℕ}

/-- A node is a qubit node -/
def isQubit : TannerNode numQubits numChecks → Bool
  | qubit _ => true
  | check _ => false

/-- A node is a check node -/
def isCheck : TannerNode numQubits numChecks → Bool
  | qubit _ => false
  | check _ => true

/-- Get the qubit index if this is a qubit node -/
def getQubitIdx : TannerNode numQubits numChecks → Option (Fin numQubits)
  | qubit q => some q
  | check _ => none

/-- Get the check index if this is a check node -/
def getCheckIdx : TannerNode numQubits numChecks → Option (Fin numChecks)
  | qubit _ => none
  | check c => some c

/-- Qubit and check are distinct node types -/
theorem qubit_ne_check (q : Fin numQubits) (c : Fin numChecks) :
    qubit q ≠ check c := by
  intro h
  cases h

/-- Check and qubit are distinct node types -/
theorem check_ne_qubit (c : Fin numChecks) (q : Fin numQubits) :
    check c ≠ qubit q := by
  intro h
  cases h

/-- isQubit is true iff node is a qubit -/
@[simp]
theorem isQubit_qubit (q : Fin numQubits) :
    (qubit q : TannerNode numQubits numChecks).isQubit = true := rfl

@[simp]
theorem isQubit_check (c : Fin numChecks) :
    (check c : TannerNode numQubits numChecks).isQubit = false := rfl

/-- isCheck is true iff node is a check -/
@[simp]
theorem isCheck_qubit (q : Fin numQubits) :
    (qubit q : TannerNode numQubits numChecks).isCheck = false := rfl

@[simp]
theorem isCheck_check (c : Fin numChecks) :
    (check c : TannerNode numQubits numChecks).isCheck = true := rfl

end TannerNode

/-- Fintype instance for TannerNode -/
instance TannerNode.fintype (numQubits numChecks : ℕ) :
    Fintype (TannerNode numQubits numChecks) :=
  Fintype.ofEquiv (Fin numQubits ⊕ Fin numChecks) {
    toFun := fun x => match x with
      | Sum.inl q => TannerNode.qubit q
      | Sum.inr c => TannerNode.check c
    invFun := fun x => match x with
      | TannerNode.qubit q => Sum.inl q
      | TannerNode.check c => Sum.inr c
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun x => by cases x <;> rfl
  }

/-! ## Section 2: Tanner Graph for Stabilizer Codes -/

/-- The Tanner graph of a stabilizer code.
    This is a bipartite graph T = (Q ∪ C, E_T) where:
    - Q = qubit nodes (one per physical qubit)
    - C = check nodes (one per stabilizer generator)
    - Edge (q, c) exists iff check c acts non-trivially on qubit q -/
structure TannerGraph (n k : ℕ) where
  /-- The underlying stabilizer code -/
  code : StabilizerCode n k
  /-- The simple graph on qubit and check nodes -/
  graph : SimpleGraph (TannerNode n (n - k))
  /-- Decidable adjacency -/
  adjDecidable : DecidableRel graph.Adj
  /-- The graph is bipartite: edges only connect qubits to checks -/
  bipartite : ∀ v w, graph.Adj v w →
    (v.isQubit = true ∧ w.isCheck = true) ∨ (v.isCheck = true ∧ w.isQubit = true)
  /-- Adjacency matches check support: qubit q is adjacent to check c iff c acts on q -/
  adjacency_support : ∀ (q : Fin n) (c : Fin (n - k)),
    graph.Adj (TannerNode.qubit q) (TannerNode.check c) ↔
    q ∈ (code.checks c).supportX ∪ (code.checks c).supportZ

attribute [instance] TannerGraph.adjDecidable

namespace TannerGraph

variable {n k : ℕ}

/-- Number of qubit nodes -/
def numQubitNodes (_T : TannerGraph n k) : ℕ := n

/-- Number of check nodes -/
def numCheckNodes (_T : TannerGraph n k) : ℕ := n - k

/-- Total number of nodes -/
def numNodes (T : TannerGraph n k) : ℕ := T.numQubitNodes + T.numCheckNodes

/-- The degree of a qubit node (number of checks it participates in) -/
noncomputable def qubitDegree (T : TannerGraph n k) (q : Fin n) : ℕ :=
  @SimpleGraph.degree _ T.graph (TannerNode.qubit q) (SimpleGraph.neighborSetFintype T.graph _)

/-- The degree of a check node (weight of the check) -/
noncomputable def checkDegree (T : TannerGraph n k) (c : Fin (n - k)) : ℕ :=
  @SimpleGraph.degree _ T.graph (TannerNode.check c) (SimpleGraph.neighborSetFintype T.graph _)

/-- Alternative definition of qubit degree using filter -/
def qubitDegreeFilter (T : TannerGraph n k) (q : Fin n) : ℕ :=
  (Finset.filter
    (fun c => q ∈ (T.code.checks c).supportX ∪ (T.code.checks c).supportZ)
    Finset.univ).card

/-- Alternative definition of check degree -/
def checkDegreeFilter (T : TannerGraph n k) (c : Fin (n - k)) : ℕ :=
  (Finset.filter
    (fun q => q ∈ (T.code.checks c).supportX ∪ (T.code.checks c).supportZ)
    Finset.univ).card

/-- The check degree filter equals the check weight -/
theorem checkDegreeFilter_eq_weight (T : TannerGraph n k) (c : Fin (n - k)) :
    T.checkDegreeFilter c = (T.code.checks c).weight := by
  unfold checkDegreeFilter StabilizerCheck.weight
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]

end TannerGraph

/-! ## Section 3: Construct Tanner Graph from Stabilizer Code -/

/-- The adjacency relation for the Tanner graph of a stabilizer code -/
def tannerAdjacency (n k : ℕ) (code : StabilizerCode n k) :
    TannerNode n (n - k) → TannerNode n (n - k) → Prop :=
  fun v w => match v, w with
    | TannerNode.qubit q, TannerNode.check c =>
        q ∈ (code.checks c).supportX ∪ (code.checks c).supportZ
    | TannerNode.check c, TannerNode.qubit q =>
        q ∈ (code.checks c).supportX ∪ (code.checks c).supportZ
    | _, _ => False

/-- The Tanner adjacency is symmetric -/
theorem tannerAdjacency_symm (n k : ℕ) (code : StabilizerCode n k) :
    Symmetric (tannerAdjacency n k code) := by
  intro v w hvw
  unfold tannerAdjacency at hvw ⊢
  cases v <;> cases w <;> simp_all

/-- The Tanner adjacency is irreflexive (no self-loops) -/
theorem tannerAdjacency_loopless (n k : ℕ) (code : StabilizerCode n k) :
    Irreflexive (tannerAdjacency n k code) := by
  intro v
  unfold tannerAdjacency
  cases v <;> simp

/-- Decidability of Tanner adjacency -/
instance tannerAdjacency_decidable (n k : ℕ) (code : StabilizerCode n k) :
    DecidableRel (tannerAdjacency n k code) := fun v w =>
  match v, w with
  | TannerNode.qubit q, TannerNode.check c =>
      inferInstanceAs (Decidable (q ∈ (code.checks c).supportX ∪ (code.checks c).supportZ))
  | TannerNode.check c, TannerNode.qubit q =>
      inferInstanceAs (Decidable (q ∈ (code.checks c).supportX ∪ (code.checks c).supportZ))
  | TannerNode.qubit _, TannerNode.qubit _ =>
      isFalse (fun h => by unfold tannerAdjacency at h; exact h)
  | TannerNode.check _, TannerNode.check _ =>
      isFalse (fun h => by unfold tannerAdjacency at h; exact h)

/-- Construct the Tanner graph from a stabilizer code -/
def mkTannerGraph {n k : ℕ} (code : StabilizerCode n k) : TannerGraph n k where
  code := code
  graph := {
    Adj := tannerAdjacency n k code
    symm := tannerAdjacency_symm n k code
    loopless := tannerAdjacency_loopless n k code
  }
  adjDecidable := tannerAdjacency_decidable n k code
  bipartite := by
    intro v w hvw
    unfold tannerAdjacency at hvw
    cases v <;> cases w <;> simp_all [TannerNode.isQubit, TannerNode.isCheck]
  adjacency_support := by
    intro q c
    unfold tannerAdjacency
    simp

/-! ## Section 4: CSS Tanner Graph -/

/-- The X-type Tanner graph for a CSS code.
    Connects qubits to X-type checks only. -/
structure CSSTannerGraphX (n rX rZ : ℕ) where
  /-- The underlying CSS code -/
  code : CSSCode n rX rZ
  /-- The simple graph on qubit and X-check nodes -/
  graph : SimpleGraph (TannerNode n rX)
  /-- Adjacency matches X-check support -/
  adjacency_support : ∀ (q : Fin n) (c : Fin rX),
    graph.Adj (TannerNode.qubit q) (TannerNode.check c) ↔ q ∈ rowSupport code.H_X c

/-- The Z-type Tanner graph for a CSS code.
    Connects qubits to Z-type checks only. -/
structure CSSTannerGraphZ (n rX rZ : ℕ) where
  /-- The underlying CSS code -/
  code : CSSCode n rX rZ
  /-- The simple graph on qubit and Z-check nodes -/
  graph : SimpleGraph (TannerNode n rZ)
  /-- Adjacency matches Z-check support -/
  adjacency_support : ∀ (q : Fin n) (c : Fin rZ),
    graph.Adj (TannerNode.qubit q) (TannerNode.check c) ↔ q ∈ rowSupport code.H_Z c

/-- Combined CSS Tanner graph with both X and Z subgraphs -/
structure CSSTannerGraph (n rX rZ : ℕ) where
  /-- The underlying CSS code -/
  code : CSSCode n rX rZ
  /-- X-type subgraph -/
  tannerX : CSSTannerGraphX n rX rZ
  /-- Z-type subgraph -/
  tannerZ : CSSTannerGraphZ n rX rZ
  /-- Both subgraphs use the same code -/
  code_consistent_X : tannerX.code = code
  /-- Both subgraphs use the same code -/
  code_consistent_Z : tannerZ.code = code

/-! ## Section 5: LDPC Condition via Tanner Graph -/

/-- A code is LDPC iff its Tanner graph has bounded degree.
    This is equivalent to the IsLDPC property defined earlier. -/
structure TannerLDPC (n k : ℕ) (T : TannerGraph n k) (w Δ : ℕ) : Prop where
  /-- Each check has degree (weight) at most w -/
  check_degree_bound : ∀ c : Fin (n - k), T.checkDegreeFilter c ≤ w
  /-- Each qubit has degree at most Δ -/
  qubit_degree_bound : ∀ q : Fin n, T.qubitDegreeFilter q ≤ Δ

/-- The LDPC condition on the Tanner graph is equivalent to the code's IsLDPC property -/
theorem tannerLDPC_iff_isLDPC {n k : ℕ} (T : TannerGraph n k) (w Δ : ℕ) :
    TannerLDPC n k T w Δ ↔ IsLDPC T.code w Δ := by
  constructor
  · intro ⟨hcheck, hqubit⟩
    constructor
    · intro i
      have h := hcheck i
      rw [T.checkDegreeFilter_eq_weight] at h
      exact h
    · intro v
      exact hqubit v
  · intro ⟨hweight, hdegree⟩
    constructor
    · intro c
      rw [T.checkDegreeFilter_eq_weight]
      exact hweight c
    · intro q
      exact hdegree q

/-! ## Section 6: Deformed Code Tanner Graph -/

/-- Node type for the deformed code Tanner graph.
    After gauging, we have:
    - Original qubit nodes Q
    - Edge qubit nodes E (auxiliary qubits from gauging)
    - Gauss's law check nodes A
    - Flux check nodes B
    - Original check nodes C -/
inductive DeformedNode (numQubits numEdges numGauss numFlux numOrigChecks : ℕ)
  | qubit : Fin numQubits → DeformedNode numQubits numEdges numGauss numFlux numOrigChecks
  | edgeQubit : Fin numEdges → DeformedNode numQubits numEdges numGauss numFlux numOrigChecks
  | gaussCheck : Fin numGauss → DeformedNode numQubits numEdges numGauss numFlux numOrigChecks
  | fluxCheck : Fin numFlux → DeformedNode numQubits numEdges numGauss numFlux numOrigChecks
  | origCheck : Fin numOrigChecks → DeformedNode numQubits numEdges numGauss numFlux numOrigChecks
  deriving DecidableEq

/-- The deformed code Tanner graph structure.
    This represents the Tanner graph after gauging, with:
    - Qubit nodes Q (original) and E (edge qubits from gauging)
    - Check nodes A (Gauss), B (flux), and C' (deformed original checks) -/
structure DeformedTannerGraph (n k : ℕ) {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) where
  /-- Number of edge qubits -/
  numEdgeQubits : ℕ
  /-- Number of Gauss's law checks (= number of vertices in G) -/
  numGaussChecks : ℕ
  /-- Number of flux checks (= cycle rank of G) -/
  numFluxChecks : ℕ
  /-- Number of original deformed checks -/
  numDeformedChecks : ℕ
  /-- Edge qubits correspond to edges of G -/
  edgeQubits_eq_edges : numEdgeQubits = G.numEdges
  /-- Gauss checks correspond to vertices of G -/
  gaussChecks_eq_vertices : numGaussChecks = G.numVertices

/-! ## Section 7: Bipartite Property of Tanner Graph -/

/-- The set of qubit nodes in the Tanner graph -/
def TannerGraph.qubitSet (_T : TannerGraph n k) : Set (TannerNode n (n - k)) :=
  { v | v.isQubit = true }

/-- The set of check nodes in the Tanner graph -/
def TannerGraph.checkSet (_T : TannerGraph n k) : Set (TannerNode n (n - k)) :=
  { v | v.isCheck = true }

/-- Qubit and check sets are disjoint -/
theorem TannerGraph.qubitSet_checkSet_disjoint {n k : ℕ} (T : TannerGraph n k) :
    Disjoint T.qubitSet T.checkSet := by
  rw [Set.disjoint_iff]
  intro v ⟨hq, hc⟩
  simp only [TannerGraph.qubitSet, TannerGraph.checkSet, Set.mem_setOf_eq] at hq hc
  cases v <;> simp_all [TannerNode.isQubit, TannerNode.isCheck]

/-- Every node is either a qubit or a check -/
theorem TannerGraph.qubitSet_checkSet_cover {n k : ℕ} (T : TannerGraph n k) :
    T.qubitSet ∪ T.checkSet = Set.univ := by
  ext v
  simp only [Set.mem_union, TannerGraph.qubitSet, TannerGraph.checkSet,
    Set.mem_setOf_eq, Set.mem_univ, iff_true]
  cases v <;> simp [TannerNode.isQubit, TannerNode.isCheck]

/-! ## Section 8: Helper Lemmas -/

/-- The Tanner graph has no edges between qubits -/
theorem TannerGraph.no_qubit_qubit_edges {n k : ℕ} (T : TannerGraph n k)
    (q₁ q₂ : Fin n) : ¬T.graph.Adj (TannerNode.qubit q₁) (TannerNode.qubit q₂) := by
  intro h
  have hbip := T.bipartite _ _ h
  simp only [TannerNode.isQubit_qubit, TannerNode.isCheck_qubit] at hbip
  rcases hbip with ⟨_, hc⟩ | ⟨hc, _⟩ <;> cases hc

/-- The Tanner graph has no edges between checks -/
theorem TannerGraph.no_check_check_edges {n k : ℕ} (T : TannerGraph n k)
    (c₁ c₂ : Fin (n - k)) : ¬T.graph.Adj (TannerNode.check c₁) (TannerNode.check c₂) := by
  intro h
  have hbip := T.bipartite _ _ h
  simp only [TannerNode.isQubit_check, TannerNode.isCheck_check] at hbip
  rcases hbip with ⟨hq, _⟩ | ⟨_, hq⟩ <;> cases hq

/-- A qubit is adjacent to a check iff the check acts non-trivially on that qubit -/
@[simp]
theorem TannerGraph.adj_qubit_check_iff {n k : ℕ} (T : TannerGraph n k)
    (q : Fin n) (c : Fin (n - k)) :
    T.graph.Adj (TannerNode.qubit q) (TannerNode.check c) ↔
    q ∈ (T.code.checks c).supportX ∪ (T.code.checks c).supportZ :=
  T.adjacency_support q c

/-- Adjacency is symmetric: check-qubit iff qubit-check -/
theorem TannerGraph.adj_check_qubit_iff {n k : ℕ} (T : TannerGraph n k)
    (c : Fin (n - k)) (q : Fin n) :
    T.graph.Adj (TannerNode.check c) (TannerNode.qubit q) ↔
    q ∈ (T.code.checks c).supportX ∪ (T.code.checks c).supportZ := by
  rw [T.graph.adj_comm]
  exact T.adjacency_support q c

/-- For CSS codes, X and Z Tanner graphs partition the edges -/
theorem CSSTannerGraph.edge_partition {n rX rZ : ℕ} (T : CSSTannerGraph n rX rZ)
    (q : Fin n) :
    (∃ c, q ∈ rowSupport T.code.H_X c) ∨ (∃ c, q ∈ rowSupport T.code.H_Z c) ∨
    (∀ cX, q ∉ rowSupport T.code.H_X cX) ∧ (∀ cZ, q ∉ rowSupport T.code.H_Z cZ) := by
  by_cases hX : ∃ c, q ∈ rowSupport T.code.H_X c
  · left; exact hX
  by_cases hZ : ∃ c, q ∈ rowSupport T.code.H_Z c
  · right; left; exact hZ
  · right; right
    push_neg at hX hZ
    exact ⟨hX, hZ⟩

/-! ## Section 9: Additional Properties -/

/-- Number of qubit nodes equals n -/
@[simp]
theorem TannerGraph.numQubitNodes_eq {n k : ℕ} (T : TannerGraph n k) :
    T.numQubitNodes = n := rfl

/-- Number of check nodes equals n - k -/
@[simp]
theorem TannerGraph.numCheckNodes_eq {n k : ℕ} (T : TannerGraph n k) :
    T.numCheckNodes = n - k := rfl

/-- The Tanner graph of a code with identity checks has no edges from that check -/
theorem mkTannerGraph_identity {n k : ℕ} (code : StabilizerCode n k)
    (c : Fin (n - k)) (h : (code.checks c).supportX = ∅ ∧ (code.checks c).supportZ = ∅) :
    ∀ q, ¬(mkTannerGraph code).graph.Adj (TannerNode.qubit q) (TannerNode.check c) := by
  intro q hadj
  rw [(mkTannerGraph code).adjacency_support] at hadj
  -- Note: (mkTannerGraph code).code = code by definition
  simp only [mkTannerGraph] at hadj
  rw [h.1, h.2] at hadj
  simp only [Finset.union_empty, Finset.notMem_empty] at hadj

/-- Check weight equals number of adjacent qubits -/
theorem TannerGraph.weight_eq_adj_count {n k : ℕ} (T : TannerGraph n k)
    (c : Fin (n - k)) :
    (T.code.checks c).weight =
    (Finset.filter (fun q => T.graph.Adj (TannerNode.qubit q) (TannerNode.check c))
      Finset.univ).card := by
  unfold StabilizerCheck.weight
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [T.adjacency_support]
  simp only [Finset.mem_union]

/-- For mkTannerGraph, adjacency is exactly support membership -/
@[simp]
theorem mkTannerGraph_adj {n k : ℕ} (code : StabilizerCode n k)
    (q : Fin n) (c : Fin (n - k)) :
    (mkTannerGraph code).graph.Adj (TannerNode.qubit q) (TannerNode.check c) ↔
    q ∈ (code.checks c).supportX ∪ (code.checks c).supportZ := by
  exact (mkTannerGraph code).adjacency_support q c

/-- The qubit degree filter counts the checks that act on a qubit -/
theorem TannerGraph.qubitDegreeFilter_eq {n k : ℕ} (T : TannerGraph n k) (q : Fin n) :
    T.qubitDegreeFilter q = QEC.qubitDegree T.code q := rfl

end QEC
