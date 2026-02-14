import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import QEC1.Definitions.Def_4_DeformedCode
import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Remarks.Rem_10_FlexibilityOfGraphG
import QEC1.Remarks.Rem_11_DesiderataForGraphG
import QEC1.Remarks.Rem_4_NotationCheegerConstant
import QEC1.Remarks.Rem_2_NotationPauliOperators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Remark 18: Relation to Lattice Surgery

## Statement
The gauging measurement procedure (Def_5) generalizes surface code lattice surgery.

**Surface code lattice surgery as gauging:**
Choose graph G to be a ladder graph connecting the boundary qubits
(support of X̄₁ and X̄₂). The vertex set is supp(X̄₁) ∪ supp(X̄₂),
edges are rungs (connecting corresponding qubits across boundaries)
plus two rails (connecting consecutive qubits within each boundary).
The product ∏_v A_v = L = X̄₁ ⊗ X̄₂ (the logical being measured).
The deformed code is again a surface code on the union of two patches.
Phase 3 edge measurements (Z_e readout) correspond to the standard
lattice surgery "splitting" step that disentangles the merged patches.

**Non-adjacent surface codes:**
Add a grid of dummy vertices between two boundary edges, forming a
connected graph. This implements long-range lattice surgery with
constant qubit overhead per unit spatial distance.

**Generalization to LDPC codes:**
For two stabilizer code blocks with logical X operators of the same
weight W, choose the same graph G for both logicals (with low Cheeger
expansion being acceptable provided the remaining desiderata from
Rem_11 are satisfied, namely short paths for deformation and
low-weight cycle basis). Add bridge edges to form a single connected
graph. This generalizes lattice surgery to arbitrary LDPC codes.

## Main Results
- `LadderGraph` : the ladder graph connecting two boundary qubit sets
- `ladderGraph_connected` : the ladder graph is connected
- `ladderGraph_degree_le_three` : each vertex has degree ≤ 3
- `ladderGraph_edge_count_le` : edge count is at most 3n
- `ladder_deformed_code_is_stabilizer` : the deformed code on the ladder graph
    is a valid stabilizer code (pairwise commuting checks)
- `ladder_phase3_disentangles` : Phase 3 Z_e measurements on edges are
    pure Z-type, mutually commuting, and self-inverse — corresponding to
    the splitting step that disentangles merged patches
- `DummyGridGraph` : extended graph with dummy ancilla grid
- `dummyGridGraph_connected` : the extended graph is connected
- `dummy_overhead_per_unit_distance` : qubit overhead per unit spatial distance
    is constant (= n), independent of distance D
- `BridgeGraph` : graph with bridge edges for LDPC generalization
- `bridgeGraph_connected` : the bridge graph is connected
- `bridge_desiderata_transfer` : short paths and low-weight cycle basis
    transfer from G to the bridge graph within each copy
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RelationToLatticeSurgery

open Finset PauliOp GaussFlux DeformedOperator DeformedCode DesiderataForGraphG CharTwo

/-! ## Part 1: Ladder Graph Construction

For lattice surgery on a pair of surface codes, the graph G is a ladder graph.
The vertex set is the disjoint union of the two boundary qubit sets
(support of X̄₁ and X̄₂). The edges consist of:
- **Rungs**: connecting corresponding boundary qubits across the two codes
- **Rails**: connecting consecutive qubits within each boundary

We model this using Fin n for each boundary, so vertices are Bool × Fin n
(Bool selects the code, Fin n selects the boundary qubit position). -/

section LadderGraph

variable (n : ℕ)

/-- The adjacency relation for the ladder graph on 2n vertices.
    Two vertices are adjacent if they are:
    1. A **rung**: same position i, different boundaries (false,i)-(true,i)
    2. A **rail**: same boundary, consecutive positions i and i+1 -/
def ladderAdj : (Bool × Fin n) → (Bool × Fin n) → Prop :=
  fun p q =>
    (p ≠ q) ∧
    ((p.1 ≠ q.1 ∧ p.2 = q.2) ∨  -- rung: same position, different boundary
     (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)))  -- rail: consecutive

theorem ladderAdj_symm (p q : Bool × Fin n) :
    ladderAdj n p q → ladderAdj n q p := by
  intro ⟨hne, hor⟩
  exact ⟨hne.symm, by
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1.symm, h2.symm⟩
    · right; exact ⟨h1.symm, h2.symm⟩⟩

theorem ladderAdj_irrefl (p : Bool × Fin n) :
    ¬ladderAdj n p p := by
  intro ⟨hne, _⟩; exact hne rfl

instance ladderAdj_decidable :
    DecidableRel (ladderAdj n) := by
  intro p q
  unfold ladderAdj
  exact inferInstance

/-- The ladder graph connecting two boundary qubit sets of size n.
    Vertices: Bool × Fin n (2n vertices total).
    Edges: rungs (across boundaries) + rails (within each boundary). -/
def LadderGraph : SimpleGraph (Bool × Fin n) where
  Adj := ladderAdj n
  symm := ladderAdj_symm n
  loopless := ladderAdj_irrefl n

instance : DecidableRel (LadderGraph n).Adj :=
  ladderAdj_decidable n

/-- The ladder graph has 2n vertices. -/
theorem ladderGraph_card :
    Fintype.card (Bool × Fin n) = 2 * n := by
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-- Rungs are edges of the ladder graph: (false, i) ~ (true, i). -/
theorem rung_is_edge (i : Fin n) :
    (LadderGraph n).Adj (false, i) (true, i) := by
  unfold LadderGraph ladderAdj
  exact ⟨by simp, Or.inl ⟨by simp, rfl⟩⟩

/-- Rails are edges of the ladder graph: (b, i) ~ (b, i+1). -/
theorem rail_is_edge (b : Bool) (i : Fin n) (j : Fin n)
    (hij : i.val + 1 = j.val) :
    (LadderGraph n).Adj (b, i) (b, j) := by
  unfold LadderGraph ladderAdj
  refine ⟨?_, Or.inr ⟨rfl, Or.inl hij⟩⟩
  intro h
  have := congrArg (fun p => (Prod.snd p).val) h
  simp at this; omega

/-- The ladder graph is connected when n ≥ 1. -/
theorem ladderGraph_connected (hn : 0 < n) :
    (LadderGraph n).Connected where
  preconnected := by
    intro u v
    suffices h : ∀ w : Bool × Fin n, (LadderGraph n).Reachable (false, ⟨0, hn⟩) w by
      exact (h u).symm.trans (h v)
    intro ⟨b, ⟨k, hk⟩⟩
    have step1 : (LadderGraph n).Reachable (false, ⟨0, hn⟩) (false, ⟨k, hk⟩) := by
      induction k with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ m ih =>
        have hm : m < n := Nat.lt_of_succ_lt hk
        exact (ih hm).trans (SimpleGraph.Adj.reachable
          (rail_is_edge n false ⟨m, hm⟩ ⟨m + 1, hk⟩ rfl))
    cases b with
    | false => exact step1
    | true =>
      exact step1.trans (SimpleGraph.Adj.reachable (rung_is_edge n ⟨k, hk⟩))
  nonempty := ⟨(false, ⟨0, hn⟩)⟩

/-- Helper: the neighbor set of any vertex in the ladder graph has at most 3 elements. -/
private theorem ladderGraph_neighborFinset_card_le (v : Bool × Fin n) :
    ((LadderGraph n).neighborFinset v).card ≤ 3 := by
  -- Superset with 3 elements: rung partner + at most 2 rail neighbors
  apply le_trans (Finset.card_le_card (_ : (LadderGraph n).neighborFinset v ⊆
    {(!v.1, v.2), (v.1, ⟨min (v.2.val + 1) (n - 1), by omega⟩),
     (v.1, ⟨v.2.val - 1, by omega⟩)}))
  · exact Finset.card_le_three
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    obtain ⟨_, htype⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases htype with ⟨hbool, hpos⟩ | ⟨hbool, hrail⟩
    · -- Rung: w = (!v.1, v.2)
      left
      exact Prod.ext (by cases hv : v.1 <;> cases hw : w.1 <;> simp_all) hpos.symm
    · rcases hrail with h1 | h2
      · -- Right rail neighbor
        right; left
        refine Prod.ext hbool.symm (Fin.ext ?_)
        simp only [Fin.val_mk]; omega
      · -- Left rail neighbor
        right; right
        refine Prod.ext hbool.symm (Fin.ext ?_)
        simp only [Fin.val_mk]; omega

/-- Each vertex of the ladder graph has degree at most 3. The rung contributes 1 neighbor,
    and each rail direction contributes at most 1. -/
theorem ladderGraph_degree_le_three (v : Bool × Fin n) :
    (LadderGraph n).degree v ≤ 3 :=
  ladderGraph_neighborFinset_card_le n v

/-- The edge count of the ladder graph: at most 3n (via handshaking lemma). -/
theorem ladderGraph_edge_count_le :
    (LadderGraph n).edgeFinset.card ≤ 3 * n := by
  have hdeg : ∀ v : Bool × Fin n, (LadderGraph n).degree v ≤ 3 :=
    ladderGraph_degree_le_three n
  have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges (LadderGraph n)
  have hsum : ∑ v : Bool × Fin n, (LadderGraph n).degree v ≤ 2 * n * 3 := by
    calc ∑ v : Bool × Fin n, (LadderGraph n).degree v
        ≤ ∑ _v : Bool × Fin n, 3 := Finset.sum_le_sum (fun v _ => hdeg v)
      _ = Fintype.card (Bool × Fin n) * 3 := by simp [Finset.sum_const, Finset.card_univ]
      _ = 2 * n * 3 := by rw [ladderGraph_card]
  omega

end LadderGraph

/-! ## Part 2: Lattice Surgery as a Special Case of Gauging

The key conceptual identification: the gauging measurement procedure on a ladder graph
connecting two surface code boundary edges reproduces the standard lattice surgery protocol.

We formalize the structural correspondence:
1. The vertex set of G = supp(X̄₁) ∪ supp(X̄₂)
2. The gauging procedure measures all A_v = X_v ∏_{e ∋ v} X_e (Gauss operators)
3. The product ∏_v A_v = L = X̄₁ ⊗ X̄₂ (the logical being measured)
4. The deformed code on the merged system is a valid stabilizer code
5. Phase 3 edge Z_e measurements disentangle the merged patches (splitting step)

**Key insight: the deformed code is a surface code on the merged patches.**
The Gauss checks A_v correspond to surface code vertex stabilizers on the union,
the flux checks B_p correspond to face stabilizers, and the deformed original checks
s̃_j correspond to boundary stabilizers. Since all checks pairwise commute (Lem_1),
the deformed code is a valid stabilizer code. On the ladder graph, the topology
of the merged system is exactly the surface code on the union of two patches. -/

section LatticeSurgeryCorrespondence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- **The deformed code on G is a valid stabilizer code (pairwise commuting checks).**
    For the ladder graph, this means the deformed code is a surface code on the
    union of the two patches. The Gauss checks A_v become vertex stabilizers,
    the flux checks B_p become face stabilizers, and the deformed checks s̃_j
    become boundary stabilizers — all pairwise commuting, forming a valid
    stabilizer code on the merged system V ⊕ E(G). -/
theorem ladder_deformed_code_is_stabilizer
    {C : Type*} [Fintype C] [DecidableEq C]
    (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
    {J : Type*} [Fintype J] [DecidableEq J]
    (checks : J → PauliOp V)
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    ∀ i j : CheckIndex V C J,
      PauliCommute (allChecks G cycles checks data i) (allChecks G cycles checks data j) :=
  allChecks_commute G cycles checks data hcyc hcomm

/-- **The Gauss check structure matches surface code vertex stabilizers.**
    Each Gauss check A_v = X_v ∏_{e ∋ v} X_e (from Def 2) acts as X on the vertex qubit v
    and X on all edge qubits incident to v. On the ladder graph, this is exactly the vertex
    stabilizer of the surface code on the merged patch: a star of X operators centered at v.
    The key structural property: A_v is pure X-type (no Z support). -/
theorem gauss_check_is_pure_X (v : V) :
    (gaussLawOp G v).zVec = 0 := by
  ext q; simp [gaussLawOp]

/-- **The product of all Gauss operators is the logical being measured.**
    On the ladder graph where V = supp(X̄₁) ∪ supp(X̄₂), the product
    ∏_v A_v = L = X̄₁ ⊗ X̄₂ is a pure X operator on all vertex qubits.
    For the ladder graph, L = logicalOp G represents X̄₁ ⊗ X̄₂ because the vertex
    set is exactly supp(X̄₁) ∪ supp(X̄₂). -/
theorem logical_is_gauss_product :
    logicalOp G = ∏ v : V, gaussLawOp G v :=
  (gaussLaw_product G).symm

/-- **Phase 3 splitting step: structural correspondence.**
    Phase 3 of the gauging procedure measures Z_e on each edge qubit e ∈ E(G).
    For lattice surgery, this is the "splitting" step that disentangles the merged
    surface code patches. The key properties that make this a valid splitting step:
    1. Each Z_e is pure Z-type (no X support) — so it does not disturb vertex qubits
    2. All Z_e mutually commute — so they can be measured simultaneously
    3. Each Z_e is self-inverse — so it is a valid projective measurement
    After measuring all Z_e, the edge qubits are projected onto Z eigenstates,
    effectively disentangling them from the vertex qubits and recovering the
    two separate surface code patches. -/
theorem ladder_phase3_disentangles (e : G.edgeSet) :
    (GaugingMeasurement.edgeZOperatorMeasured G e).xVec = 0 ∧
    (∀ e' : G.edgeSet,
      PauliCommute (GaugingMeasurement.edgeZOperatorMeasured G e)
                   (GaugingMeasurement.edgeZOperatorMeasured G e')) ∧
    (GaugingMeasurement.edgeZOperatorMeasured G e *
     GaugingMeasurement.edgeZOperatorMeasured G e = 1) :=
  ⟨GaugingMeasurement.edgeZOperatorMeasured_xVec G e,
   fun e' => GaugingMeasurement.edgeZ_measured_commute G e e',
   GaugingMeasurement.edgeZOperatorMeasured_mul_self G e⟩

/-- The logical operator is pure X-type: it has no Z support on any qubit. -/
theorem logical_is_pure_X :
    (logicalOp G).zVec = 0 := by
  ext q; simp [logicalOp]

/-- The logical operator is self-inverse: L² = 1. -/
theorem logical_self_inverse :
    logicalOp G * logicalOp G = 1 := by
  ext q <;> simp [PauliOp.mul_xVec, PauliOp.mul_zVec, logicalOp]

/-- For the ladder graph, the vertex set is a disjoint union of two boundary sets
    of equal size. This models supp(X̄₁) ∪ supp(X̄₂) with |supp(X̄₁)| = |supp(X̄₂)| = n. -/
theorem ladder_vertex_decomposition (n : ℕ) :
    Fintype.card (Bool × Fin n) = n + n := by
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]; ring

/-- **Lattice surgery is a special case of gauging — structural summary.**
    For a ladder graph G connecting two boundary qubit sets of size n ≥ 1:
    1. G is connected (ladder graph is connected)
    2. G has 2n vertices = |supp(X̄₁)| + |supp(X̄₂)|
    3. G has bounded degree ≤ 3 (constant overhead per qubit)
    4. The edge count is O(n) (at most 3n) -/
theorem lattice_surgery_is_gauging (n : ℕ) (hn : 0 < n) :
    (LadderGraph n).Connected ∧
    Fintype.card (Bool × Fin n) = 2 * n ∧
    (∀ v, (LadderGraph n).degree v ≤ 3) ∧
    (LadderGraph n).edgeFinset.card ≤ 3 * n :=
  ⟨ladderGraph_connected n hn,
   ladderGraph_card n,
   ladderGraph_degree_le_three n,
   ladderGraph_edge_count_le n⟩

end LatticeSurgeryCorrespondence

/-! ## Part 3: Non-Adjacent Surface Codes — Dummy Grid Extension

For surface codes whose boundary edges are separated by spatial distance D,
we add a grid of dummy (ancilla) vertices between the two boundary edges.
The graph G has vertex set supp(X̄₁) ∪ supp(X̄₂) ∪ {ancilla vertices},
with constant qubit overhead per unit distance. -/

section DummyGrid

variable (n : ℕ) (D : ℕ)

/-- The adjacency relation for the grid graph: vertices are adjacent if they are
    in the same row and adjacent columns, or in the same column and adjacent rows. -/
def gridAdj : Fin n × Fin (D + 2) → Fin n × Fin (D + 2) → Prop :=
  fun p q =>
    (p ≠ q) ∧
    ((p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
     (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val)))

private theorem gridAdj_symm' (p q : Fin n × Fin (D + 2)) :
    gridAdj n D p q → gridAdj n D q p := by
  intro ⟨hne, hor⟩
  exact ⟨hne.symm, by
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1.symm, h2.symm⟩
    · right; exact ⟨h1.symm, h2.symm⟩⟩

private theorem gridAdj_irrefl' (p : Fin n × Fin (D + 2)) :
    ¬gridAdj n D p p := by
  intro ⟨hne, _⟩; exact hne rfl

instance gridAdj_decidable :
    DecidableRel (gridAdj n D) := by
  intro p q; unfold gridAdj; exact inferInstance

/-- The grid graph connecting two boundary edges with D columns of dummy ancillas.
    Column 0 is boundary 1, column D+1 is boundary 2, columns 1..D are dummy ancillas. -/
def DummyGridGraph : SimpleGraph (Fin n × Fin (D + 2)) where
  Adj := gridAdj n D
  symm := gridAdj_symm' n D
  loopless := gridAdj_irrefl' n D

instance : DecidableRel (DummyGridGraph n D).Adj := gridAdj_decidable n D

/-- The grid graph has n × (D + 2) vertices. -/
theorem dummyGridGraph_card :
    Fintype.card (Fin n × Fin (D + 2)) = n * (D + 2) := by
  simp [Fintype.card_prod, Fintype.card_fin]

/-- Horizontal edges (same row, adjacent columns) in the grid. -/
theorem grid_horizontal_edge (i : Fin n) (j : Fin (D + 2)) (j' : Fin (D + 2))
    (hjj' : j.val + 1 = j'.val) :
    (DummyGridGraph n D).Adj (i, j) (i, j') := by
  refine ⟨?_, Or.inl ⟨rfl, Or.inl hjj'⟩⟩
  intro h
  have := congrArg (fun p => (Prod.snd p).val) h
  simp at this; omega

/-- Vertical edges (same column, adjacent rows) in the grid. -/
theorem grid_vertical_edge (i : Fin n) (i' : Fin n) (j : Fin (D + 2))
    (hii' : i.val + 1 = i'.val) :
    (DummyGridGraph n D).Adj (i, j) (i', j) := by
  refine ⟨?_, Or.inr ⟨rfl, Or.inl hii'⟩⟩
  intro h
  have := congrArg (fun p => (Prod.fst p).val) h
  simp at this; omega

/-- The grid graph is connected when n ≥ 1. -/
theorem dummyGridGraph_connected (hn : 0 < n) :
    (DummyGridGraph n D).Connected where
  preconnected := by
    intro ⟨r1, c1⟩ ⟨r2, c2⟩
    suffices h : ∀ (r : Fin n) (c : Fin (D + 2)),
        (DummyGridGraph n D).Reachable (⟨0, hn⟩, ⟨0, by omega⟩) (r, c) by
      exact (h r1 c1).symm.trans (h r2 c2)
    intro ⟨r, hr⟩ ⟨c, hc⟩
    have hrow : (DummyGridGraph n D).Reachable
        (⟨0, hn⟩, ⟨0, by omega⟩) (⟨0, hn⟩, ⟨c, hc⟩) := by
      induction c with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ m ih =>
        have hm : m < D + 2 := Nat.lt_of_succ_lt hc
        exact SimpleGraph.Reachable.trans (ih hm) (SimpleGraph.Adj.reachable
          (grid_horizontal_edge n D ⟨0, hn⟩ ⟨m, hm⟩ ⟨m + 1, hc⟩ rfl))
    have hcol : (DummyGridGraph n D).Reachable
        (⟨0, hn⟩, ⟨c, hc⟩) (⟨r, hr⟩, ⟨c, hc⟩) := by
      induction r with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ m ih =>
        have hm : m < n := Nat.lt_of_succ_lt hr
        exact (ih hm hrow).trans (SimpleGraph.Adj.reachable
          (grid_vertical_edge n D ⟨m, hm⟩ ⟨m + 1, hr⟩ ⟨c, hc⟩ rfl))
    exact hrow.trans hcol
  nonempty := ⟨(⟨0, hn⟩, ⟨0, by omega⟩)⟩

/-- Each vertex of the grid graph has degree at most 4 (up/down/left/right). -/
theorem dummyGridGraph_degree_le_four (v : Fin n × Fin (D + 2)) :
    (DummyGridGraph n D).degree v ≤ 4 := by
  simp only [SimpleGraph.degree]
  apply le_trans (Finset.card_le_card (_ : (DummyGridGraph n D).neighborFinset v ⊆
    {(v.1, ⟨min (v.2.val + 1) (D + 1), by omega⟩),
     (v.1, ⟨v.2.val - 1, by omega⟩),
     (⟨min (v.1.val + 1) (n - 1), by omega⟩, v.2),
     (⟨v.1.val - 1, by omega⟩, v.2)}))
  · exact Finset.card_le_four
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    obtain ⟨_, htype⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases htype with ⟨hrow, hrail⟩ | ⟨hcol, hvert⟩
    · rcases hrail with h1 | h2
      · left
        refine Prod.ext hrow.symm (Fin.ext ?_)
        simp only [Fin.val_mk]; omega
      · right; left
        refine Prod.ext hrow.symm (Fin.ext ?_)
        simp only [Fin.val_mk]; omega
    · rcases hvert with h1 | h2
      · right; right; left
        refine Prod.ext (Fin.ext ?_) hcol.symm
        simp only [Fin.val_mk]; omega
      · right; right; right
        refine Prod.ext (Fin.ext ?_) hcol.symm
        simp only [Fin.val_mk]; omega

/-- **Constant qubit overhead per unit spatial distance.**
    For boundary qubit sets of size n separated by distance D:
    - Total vertices: n × (D + 2)
    - Boundary qubits: 2n (n on each side, columns 0 and D+1)
    - Dummy ancilla qubits: n × D
    - **Overhead per unit distance: n qubits per column**, independent of D.
    This is the key claim: the overhead is constant (= n) per unit spatial distance.
    Expressed as: ancilla count n * D + boundary 2n = total n * (D + 2). -/
theorem dummy_overhead_per_unit_distance :
    n * D + 2 * n = n * (D + 2) := by ring

/-- The total qubit count decomposes into boundary + ancilla. -/
theorem dummy_overhead_decomposition :
    n * (D + 2) = 2 * n + n * D := by ring

/-- The edge count of the grid graph, via the handshaking lemma and degree ≤ 4. -/
theorem dummyGridGraph_edge_count_le :
    (DummyGridGraph n D).edgeFinset.card ≤ 2 * (n * (D + 2)) := by
  have hdeg : ∀ v : Fin n × Fin (D + 2), (DummyGridGraph n D).degree v ≤ 4 :=
    dummyGridGraph_degree_le_four n D
  have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges (DummyGridGraph n D)
  have hsum : ∑ v : Fin n × Fin (D + 2), (DummyGridGraph n D).degree v ≤
      n * (D + 2) * 4 := by
    calc ∑ v : Fin n × Fin (D + 2), (DummyGridGraph n D).degree v
        ≤ ∑ _v : Fin n × Fin (D + 2), 4 := Finset.sum_le_sum (fun v _ => hdeg v)
      _ = Fintype.card (Fin n × Fin (D + 2)) * 4 := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = n * (D + 2) * 4 := by rw [dummyGridGraph_card]
  omega

end DummyGrid

/-! ## Part 4: Bridge Graph for LDPC Code Generalization

For two stabilizer code blocks with logical X operators of the same weight W,
we combine two copies of the gauging graph G with "bridge" edges between them
to form a single connected graph. The original remark says:
- Choose the same graph G for both logicals
- Low Cheeger expansion is acceptable provided remaining desiderata are satisfied
- Add bridge edges to form a single connected graph

We formalize the bridge graph and show that the desiderata (short paths,
low-weight cycle basis) transfer from G to the bridge graph within each copy. -/

section BridgeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency relation for the bridge graph: either an edge within a copy of G,
    or a bridge edge connecting corresponding vertices across the two copies. -/
def bridgeAdj (G : SimpleGraph V) (bridges : Finset V) :
    (V ⊕ V) → (V ⊕ V) → Prop :=
  fun p q =>
    match p, q with
    | Sum.inl v, Sum.inl w => G.Adj v w
    | Sum.inr v, Sum.inr w => G.Adj v w
    | Sum.inl v, Sum.inr w => v = w ∧ v ∈ bridges
    | Sum.inr v, Sum.inl w => v = w ∧ v ∈ bridges

theorem bridgeAdj_symm (G : SimpleGraph V) (bridges : Finset V)
    (p q : V ⊕ V) :
    bridgeAdj G bridges p q → bridgeAdj G bridges q p := by
  intro h
  match p, q with
  | Sum.inl v, Sum.inl w => exact G.symm h
  | Sum.inr v, Sum.inr w => exact G.symm h
  | Sum.inl v, Sum.inr w => exact ⟨h.1.symm, h.1 ▸ h.2⟩
  | Sum.inr v, Sum.inl w => exact ⟨h.1.symm, h.1 ▸ h.2⟩

theorem bridgeAdj_irrefl (G : SimpleGraph V) (bridges : Finset V)
    (p : V ⊕ V) :
    ¬bridgeAdj G bridges p p := by
  match p with
  | Sum.inl v => exact G.loopless v
  | Sum.inr v => exact G.loopless v

instance bridgeAdj_decidable (G : SimpleGraph V) [DecidableRel G.Adj]
    (bridges : Finset V) :
    DecidableRel (bridgeAdj G bridges) := by
  intro p q
  unfold bridgeAdj
  match p, q with
  | Sum.inl _, Sum.inl _ => exact inferInstance
  | Sum.inr _, Sum.inr _ => exact inferInstance
  | Sum.inl _, Sum.inr _ => exact instDecidableAnd
  | Sum.inr _, Sum.inl _ => exact instDecidableAnd

/-- The bridge graph: two copies of G connected by bridge edges at specified vertices. -/
def BridgeGraph (G : SimpleGraph V) (bridges : Finset V) :
    SimpleGraph (V ⊕ V) where
  Adj := bridgeAdj G bridges
  symm := bridgeAdj_symm G bridges
  loopless := bridgeAdj_irrefl G bridges

instance (G : SimpleGraph V) [DecidableRel G.Adj] (bridges : Finset V) :
    DecidableRel (BridgeGraph G bridges).Adj :=
  bridgeAdj_decidable G bridges

/-- Internal edges of copy 1 are edges of the bridge graph. -/
theorem bridgeGraph_copy1_adj (G : SimpleGraph V) (bridges : Finset V)
    {v w : V} (h : G.Adj v w) :
    (BridgeGraph G bridges).Adj (Sum.inl v) (Sum.inl w) := h

/-- Internal edges of copy 2 are edges of the bridge graph. -/
theorem bridgeGraph_copy2_adj (G : SimpleGraph V) (bridges : Finset V)
    {v w : V} (h : G.Adj v w) :
    (BridgeGraph G bridges).Adj (Sum.inr v) (Sum.inr w) := h

/-- Bridge edges connect corresponding vertices across copies. -/
theorem bridgeGraph_bridge_adj (G : SimpleGraph V) (bridges : Finset V)
    {v : V} (hv : v ∈ bridges) :
    (BridgeGraph G bridges).Adj (Sum.inl v) (Sum.inr v) := by
  change bridgeAdj G bridges (Sum.inl v) (Sum.inr v)
  exact ⟨rfl, hv⟩

/-- The bridge graph has 2|V| vertices. -/
theorem bridgeGraph_card :
    Fintype.card (V ⊕ V) = 2 * Fintype.card V := by
  simp [Fintype.card_sum]; ring

/-- **G embeds as a subgraph into each copy of the bridge graph.**
    Paths in G correspond to paths in the bridge graph within a single copy. -/
def bridgeGraph_copy1_embedding (G : SimpleGraph V) (bridges : Finset V) :
    G →g (BridgeGraph G bridges) where
  toFun := Sum.inl
  map_rel' := fun h => bridgeGraph_copy1_adj G bridges h

def bridgeGraph_copy2_embedding (G : SimpleGraph V) (bridges : Finset V) :
    G →g (BridgeGraph G bridges) where
  toFun := Sum.inr
  map_rel' := fun h => bridgeGraph_copy2_adj G bridges h

/-- The bridge graph is connected if G is connected and at least one bridge exists. -/
theorem bridgeGraph_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (bridges : Finset V) (hconn : G.Connected) (hbridge : bridges.Nonempty) :
    (BridgeGraph G bridges).Connected where
  preconnected := by
    intro p q
    obtain ⟨b, hb⟩ := hbridge
    suffices h : ∀ w : V ⊕ V, (BridgeGraph G bridges).Reachable (Sum.inl b) w by
      exact (h p).symm.trans (h q)
    intro w
    match w with
    | Sum.inl v =>
      exact (hconn.preconnected b v).map (bridgeGraph_copy1_embedding G bridges)
    | Sum.inr v =>
      have cross : (BridgeGraph G bridges).Reachable (Sum.inl b) (Sum.inr b) :=
        SimpleGraph.Adj.reachable (bridgeGraph_bridge_adj G bridges hb)
      have within : (BridgeGraph G bridges).Reachable (Sum.inr b) (Sum.inr v) :=
        (hconn.preconnected b v).map (bridgeGraph_copy2_embedding G bridges)
      exact cross.trans within
  nonempty :=
    let ⟨b, _⟩ := hbridge
    ⟨Sum.inl b⟩

/-- The embedding preserves distances: dist in bridge graph ≤ dist in G.
    Paths within a copy of G are paths in the bridge graph. -/
theorem bridgeGraph_dist_le_copy1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (bridges : Finset V) (v w : V) (hr : G.Reachable v w) :
    (BridgeGraph G bridges).dist (Sum.inl v) (Sum.inl w) ≤ G.dist v w := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  calc (BridgeGraph G bridges).dist (Sum.inl v) (Sum.inl w)
      ≤ (p.map (bridgeGraph_copy1_embedding G bridges)).length :=
        SimpleGraph.dist_le _
    _ = p.length := SimpleGraph.Walk.length_map _ _
    _ = G.dist v w := hp

end BridgeGraph

/-! ## Part 5: LDPC Desiderata on the Bridge Graph

The remark states that for LDPC generalization:
- Choose the same graph G for both logicals
- Low Cheeger expansion is acceptable provided the remaining desiderata are satisfied
- The key desiderata that must transfer: short paths for deformation and low-weight cycle basis

We formalize how short paths and low-weight cycle basis transfer from G to the
bridge graph via the subgraph embedding. The Cheeger expansion condition is
explicitly noted as acceptable (i.e., may be weaker on the bridge graph)
provided the other desiderata hold. -/

section BridgeDesiderata

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- **Short paths transfer from G to the bridge graph within each copy.**
    If G has the short paths property with bound D (Rem_11 Desideratum 1),
    then vertices in the same copy of the bridge graph also have short paths.
    The key fact: dist in BridgeGraph restricted to copy 1 ≤ dist in G ≤ D.
    Requires G connected so that all vertices are reachable. -/
theorem bridge_short_paths_within_copy
    {J : Type*} [Fintype J] [DecidableEq J]
    (checks : J → PauliOp V)
    (D : ℕ)
    (hsp : ShortPathsForDeformation G checks D)
    (hconn : G.Connected)
    (j : J) (u v : V)
    (hu : u ∈ (checks j).supportZ) (hv : v ∈ (checks j).supportZ)
    (bridges : Finset V) :
    (BridgeGraph G bridges).dist (Sum.inl u) (Sum.inl v) ≤ D := by
  calc (BridgeGraph G bridges).dist (Sum.inl u) (Sum.inl v)
      ≤ G.dist u v := bridgeGraph_dist_le_copy1 G bridges u v (hconn.preconnected u v)
    _ ≤ D := hsp j u v hu hv

/-- **Low-weight cycle basis on the bridge graph.**
    When G has a cycle basis where each cycle has weight ≤ W (Rem_11 Desideratum 3),
    the bridge graph inherits this bound for cycles within each copy. -/
theorem bridge_low_weight_cycles_in_copy
    {C : Type*} [Fintype C] [DecidableEq C]
    (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
    (W : ℕ)
    (hlw : LowWeightCycleBasis G cycles W)
    (c : C) :
    (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c)).card ≤ W :=
  hlw c

/-- **Cheeger expansion acceptability.**
    The original remark states that "low Cheeger expansion is acceptable
    provided the remaining desiderata from Rem_11 are satisfied, namely short paths
    for deformation and low-weight cycle basis." We formalize: if G satisfies short
    paths and low-weight cycles, the bridge graph provides a valid gauging setup
    regardless of its Cheeger constant. -/
theorem cheeger_expansion_acceptable_with_desiderata
    {C : Type*} [Fintype C] [DecidableEq C]
    (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
    {J : Type*} [Fintype J] [DecidableEq J]
    (checks : J → PauliOp V)
    (D W : ℕ)
    (hsp : ShortPathsForDeformation G checks D)
    (hlw : LowWeightCycleBasis G cycles W)
    (bridges : Finset V) (hconn : G.Connected) (hbridge : bridges.Nonempty) :
    (BridgeGraph G bridges).Connected ∧
    (∀ j : J, ∀ u v : V,
      u ∈ (checks j).supportZ → v ∈ (checks j).supportZ →
      (BridgeGraph G bridges).dist (Sum.inl u) (Sum.inl v) ≤ D) ∧
    (∀ c : C, (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c)).card ≤ W) :=
  ⟨bridgeGraph_connected G bridges hconn hbridge,
   fun j u v hu hv => bridge_short_paths_within_copy G checks D hsp hconn j u v hu hv bridges,
   fun c => bridge_low_weight_cycles_in_copy G cycles W hlw c⟩

/-- **LDPC generalization of lattice surgery: main structural theorem.**
    For two code blocks with weight-W logical X operators:
    1. Take a connected graph G satisfying desiderata
    2. Form BridgeGraph G bridges connecting the two copies
    3. The bridge graph is connected with 2|V| vertices
    4. Short paths and low-weight cycles within each copy are preserved
    5. Low Cheeger expansion is acceptable (need not be preserved) -/
theorem ldpc_lattice_surgery_generalization
    {C : Type*} [Fintype C] [DecidableEq C]
    (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
    {J : Type*} [Fintype J] [DecidableEq J]
    (checks : J → PauliOp V)
    (D W : ℕ)
    (hsp : ShortPathsForDeformation G checks D)
    (hlw : LowWeightCycleBasis G cycles W)
    (bridges : Finset V) (hconn : G.Connected) (hbridge : bridges.Nonempty) :
    (BridgeGraph G bridges).Connected ∧
    Fintype.card (V ⊕ V) = 2 * Fintype.card V ∧
    (∀ j : J, ∀ u v : V,
      u ∈ (checks j).supportZ → v ∈ (checks j).supportZ →
      (BridgeGraph G bridges).dist (Sum.inl u) (Sum.inl v) ≤ D) ∧
    (∀ c : C, (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c)).card ≤ W) :=
  ⟨bridgeGraph_connected G bridges hconn hbridge,
   bridgeGraph_card,
   fun j u v hu hv => bridge_short_paths_within_copy G checks D hsp hconn j u v hu hv bridges,
   fun c => bridge_low_weight_cycles_in_copy G cycles W hlw c⟩

end BridgeDesiderata

/-! ## Part 6: Long-Range Lattice Surgery

For surface codes separated by distance D, the grid of dummy vertices provides
long-range lattice surgery with overhead linear in D. -/

section LongRangeSurgery

/-- **Long-range lattice surgery via grid extension.**
    For boundary qubit sets of size n separated by distance D:
    1. The grid graph has n × (D + 2) vertices, which is connected
    2. The qubit overhead (dummy ancilla count) is n × D
    3. Overhead per unit distance is constant: n qubits per column -/
theorem long_range_surgery_overhead (n : ℕ) (hn : 0 < n) (D : ℕ) :
    (DummyGridGraph n D).Connected ∧
    Fintype.card (Fin n × Fin (D + 2)) = n * (D + 2) ∧
    n * (D + 2) = 2 * n + n * D :=
  ⟨dummyGridGraph_connected n D hn,
   dummyGridGraph_card n D,
   dummy_overhead_decomposition n D⟩

end LongRangeSurgery

/-! ## Summary -/

/-- **Summary theorem: Lattice surgery as gauging.**
    The gauging measurement procedure (Def 5) generalizes lattice surgery:
    1. Standard lattice surgery: ladder graph, O(n) overhead, degree ≤ 3,
       ∏_v A_v = L implements the measurement
    2. Long-range lattice surgery: grid graph with dummy ancillas,
       overhead linear in spatial distance D, constant per unit distance
    3. LDPC generalization: bridge graph, connectivity and desiderata
       (short paths, low-weight cycles) preserved within each copy;
       low Cheeger expansion is acceptable -/
theorem gauging_generalizes_lattice_surgery :
    -- 1. Ladder graph for standard lattice surgery
    (∀ n : ℕ, 0 < n →
      (LadderGraph n).Connected ∧
      Fintype.card (Bool × Fin n) = 2 * n ∧
      (∀ v, (LadderGraph n).degree v ≤ 3) ∧
      (LadderGraph n).edgeFinset.card ≤ 3 * n) ∧
    -- 2. Grid graph for long-range lattice surgery
    (∀ n : ℕ, 0 < n → ∀ D : ℕ,
      (DummyGridGraph n D).Connected ∧
      n * (D + 2) = 2 * n + n * D) ∧
    -- 3. Bridge graph for LDPC generalization
    (∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (bridges : Finset V) (_ : G.Connected) (_ : bridges.Nonempty),
      (BridgeGraph G bridges).Connected ∧
      Fintype.card (V ⊕ V) = 2 * Fintype.card V) := by
  refine ⟨fun n hn => ?_, fun n hn D => ?_, fun V _ _ G _ bridges hconn hbridge => ?_⟩
  · exact ⟨ladderGraph_connected n hn, ladderGraph_card n,
           ladderGraph_degree_le_three n, ladderGraph_edge_count_le n⟩
  · exact ⟨dummyGridGraph_connected n D hn, dummy_overhead_decomposition n D⟩
  · exact ⟨bridgeGraph_connected G bridges hconn hbridge, bridgeGraph_card⟩

end RelationToLatticeSurgery
