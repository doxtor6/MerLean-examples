import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Remarks.Rem_10_FlexibilityOfGraphG
import QEC1.Remarks.Rem_9_CircuitImplementation
import QEC1.Remarks.Rem_2_NotationPauliOperators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Remark 24: Shor-Style Measurement as Gauging

## Statement
The gauging measurement procedure (Def_5) recovers Shor-style logical measurement
as a special case. Let L be a Pauli logical operator with weight W = |supp(L)|.

**Shor-style measurement** uses an auxiliary GHZ state on W qubits, transversal CX
gates, and X measurements on the auxiliary qubits.

**Gauging measurement viewpoint:**
Choose a graph G with vertex set supp(L) ∪ {d_1, ..., d_W} where:
1. W dummy vertices d_i (one per qubit in supp(L))
2. A connected subgraph on the dummy vertices
3. Each d_i connected by a single edge to the corresponding qubit i

After measuring the edges of the dummy subgraph first (ungauging step of Def_5),
the remaining state on dummy qubits is equivalent to a GHZ state entangled with
supp(L), recovering Shor-style measurement.

## Main Results
- `ShorVertex` : the vertex type supp(L) ⊕ D (support qubits + dummy qubits)
- `shorGraphAdj` : adjacency relation for the Shor-style graph
- `ShorGraph` : the Shor-style gauging graph
- `shorGraph_connected` : the graph is connected (when dummy subgraph is connected)
- `shorGraph_card` : the graph has 2W vertices
- `shor_gauss_product_eq_logical` : ∏_v A_v = L'
- `shor_pairing_edge` : d_i is adjacent to i in the Shor graph
- `shor_style_structural_correspondence` : structural summary
- `shor_dummy_degree_eq` : deg(d_i) in ShorGraph = 1 + deg(d_i) in Gdummy
- `shor_max_degree_bound` : max degree in ShorGraph ≤ max_degree(Gdummy) + 1
- `shor_edge_count_via_handshaking` : 2|E| = W + (W + Σ deg_Gdummy(i))
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace ShorStyleMeasurement

open Finset PauliOp GaussFlux FlexibilityOfGraphG

/-! ## Shor-style graph construction

The vertex type is Q ⊕ Q where Q = Fin W represents the support of L.
The first copy (Sum.inl i) represents the original support qubits.
The second copy (Sum.inr i) represents the dummy vertices d_i.

The edge set consists of:
1. **Pairing edges**: (Sum.inl i, Sum.inr i) connecting each support qubit to its dummy
2. **Dummy subgraph edges**: edges among dummy vertices forming a connected subgraph
-/

section ShorGraph

variable (W : ℕ)

/-- The vertex type for the Shor-style gauging graph: support qubits ⊕ dummy qubits.
    Both are indexed by Fin W, so the total vertex count is 2W. -/
abbrev ShorVertex := Fin W ⊕ Fin W

variable (Gdummy : SimpleGraph (Fin W)) [DecidableRel Gdummy.Adj]

/-- The adjacency relation for the Shor-style gauging graph.
    Two vertices are adjacent if:
    1. A pairing edge: (inl i, inr i) connecting support qubit i to dummy d_i
    2. A dummy subgraph edge: (inr i, inr j) where i ~ j in Gdummy -/
def shorGraphAdj : ShorVertex W → ShorVertex W → Prop :=
  fun p q => p ≠ q ∧
    ((∃ i : Fin W, p = Sum.inl i ∧ q = Sum.inr i) ∨
     (∃ i : Fin W, p = Sum.inr i ∧ q = Sum.inl i) ∨
     (∃ i j : Fin W, p = Sum.inr i ∧ q = Sum.inr j ∧ Gdummy.Adj i j))

theorem shorGraphAdj_symm (p q : ShorVertex W) :
    shorGraphAdj W Gdummy p q → shorGraphAdj W Gdummy q p := by
  intro ⟨hne, hor⟩
  refine ⟨hne.symm, ?_⟩
  rcases hor with ⟨i, hp, hq⟩ | ⟨i, hp, hq⟩ | ⟨i, j, hp, hq, hadj⟩
  · exact Or.inr (Or.inl ⟨i, hq, hp⟩)
  · exact Or.inl ⟨i, hq, hp⟩
  · exact Or.inr (Or.inr ⟨j, i, hq, hp, hadj.symm⟩)

theorem shorGraphAdj_irrefl (p : ShorVertex W) :
    ¬shorGraphAdj W Gdummy p p := by
  intro ⟨hne, _⟩; exact hne rfl

instance shorGraphAdj_decidable :
    DecidableRel (shorGraphAdj W Gdummy) := by
  intro p q
  unfold shorGraphAdj
  exact inferInstance

/-- The Shor-style gauging graph on 2W vertices.
    Edges: W pairing edges {(inl i, inr i)} plus the dummy subgraph. -/
def ShorGraph : SimpleGraph (ShorVertex W) where
  Adj := shorGraphAdj W Gdummy
  symm := shorGraphAdj_symm W Gdummy
  loopless := shorGraphAdj_irrefl W Gdummy

instance : DecidableRel (ShorGraph W Gdummy).Adj :=
  shorGraphAdj_decidable W Gdummy

/-- The Shor graph has 2W vertices. -/
theorem shorGraph_card :
    Fintype.card (ShorVertex W) = 2 * W := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Each pairing edge connects support qubit i to its dummy d_i. -/
theorem shor_pairing_edge (i : Fin W) :
    (ShorGraph W Gdummy).Adj (Sum.inl i) (Sum.inr i) := by
  refine ⟨by simp, Or.inl ⟨i, rfl, rfl⟩⟩

/-- Dummy subgraph edges are edges of the Shor graph. -/
theorem shor_dummy_edge (i j : Fin W) (hadj : Gdummy.Adj i j) :
    (ShorGraph W Gdummy).Adj (Sum.inr i) (Sum.inr j) := by
  constructor
  · intro h; simp only [Sum.inr.injEq] at h; exact Gdummy.loopless i (h ▸ hadj)
  · exact Or.inr (Or.inr ⟨i, j, rfl, rfl, hadj⟩)

/-- The embedding of the dummy subgraph into the Shor graph via Sum.inr. -/
def shorDummyHom : Gdummy →g ShorGraph W Gdummy where
  toFun := Sum.inr
  map_rel' := fun hadj => shor_dummy_edge W Gdummy _ _ hadj

/-- The Shor graph is connected when the dummy subgraph is connected and W ≥ 1. -/
theorem shorGraph_connected (hW : 0 < W) (hconn : Gdummy.Connected) :
    (ShorGraph W Gdummy).Connected where
  preconnected := by
    intro u v
    suffices h : ∀ w : ShorVertex W, (ShorGraph W Gdummy).Reachable (Sum.inr ⟨0, hW⟩) w by
      exact (h u).symm.trans (h v)
    intro w
    cases w with
    | inr j =>
      have hreach := hconn.preconnected ⟨0, hW⟩ j
      exact hreach.map (shorDummyHom W Gdummy)
    | inl i =>
      have hreach := hconn.preconnected ⟨0, hW⟩ i
      have hreach' : (ShorGraph W Gdummy).Reachable (Sum.inr ⟨0, hW⟩) (Sum.inr i) :=
        hreach.map (shorDummyHom W Gdummy)
      exact hreach'.trans (SimpleGraph.Adj.reachable
        (shorGraphAdj_symm W Gdummy _ _ (shor_pairing_edge W Gdummy i)))
  nonempty := ⟨Sum.inr ⟨0, hW⟩⟩

/-- Each dummy vertex d_i has degree ≥ 1 in the Shor graph (the pairing edge to i). -/
theorem shor_dummy_degree_ge_one (_hW : 0 < W) (i : Fin W) :
    0 < (ShorGraph W Gdummy).degree (Sum.inr i) := by
  rw [SimpleGraph.degree]
  apply Finset.card_pos.mpr
  refine ⟨Sum.inl i, ?_⟩
  rw [SimpleGraph.mem_neighborFinset]
  exact (ShorGraph W Gdummy).symm (shor_pairing_edge W Gdummy i)

/-- Each support vertex has degree ≥ 1 in the Shor graph (the pairing edge to d_i). -/
theorem shor_support_degree_ge_one (_hW : 0 < W) (i : Fin W) :
    0 < (ShorGraph W Gdummy).degree (Sum.inl i) := by
  rw [SimpleGraph.degree]
  apply Finset.card_pos.mpr
  refine ⟨Sum.inr i, ?_⟩
  rw [SimpleGraph.mem_neighborFinset]
  exact shor_pairing_edge W Gdummy i

/-- The edge set trichotomy: every edge of the Shor graph is either a pairing edge or
    a dummy subgraph edge. -/
theorem shor_edge_trichotomy {p q : ShorVertex W}
    (hadj : (ShorGraph W Gdummy).Adj p q) :
    (∃ i : Fin W, (p = Sum.inl i ∧ q = Sum.inr i) ∨ (p = Sum.inr i ∧ q = Sum.inl i)) ∨
    (∃ i j : Fin W, p = Sum.inr i ∧ q = Sum.inr j ∧ Gdummy.Adj i j) := by
  obtain ⟨_, hor⟩ := hadj
  rcases hor with ⟨i, hp, hq⟩ | ⟨i, hp, hq⟩ | ⟨i, j, hp, hq, h⟩
  · exact Or.inl ⟨i, Or.inl ⟨hp, hq⟩⟩
  · exact Or.inl ⟨i, Or.inr ⟨hp, hq⟩⟩
  · exact Or.inr ⟨i, j, hp, hq, h⟩

end ShorGraph

/-! ## Extended logical operator on the Shor graph

The vertex set of the Shor graph is (Fin W) ⊕ (Fin W), where the first copy
represents supp(L) and the second copy represents the dummy vertices.
The logical operator being measured is L' = ∏_v X_v over ALL vertices
(both support and dummy), exactly as in Rem_10's extendedLogicalOp. -/

section LogicalOperator

variable (W : ℕ)

/-- The logical operator L' on the Shor graph vertex set: L' = ∏_{v ∈ V ⊕ D} X_v.
    This is the extended logical from Rem_10 with V = D = Fin W. -/
def shorLogicalOp : PauliOp (ShorVertex W) where
  xVec := fun _ => 1
  zVec := 0

/-- L' is pure X-type: no Z-support. -/
theorem shorLogicalOp_pure_X : (shorLogicalOp W).zVec = 0 := rfl

/-- L' is self-inverse: L' · L' = 1. -/
theorem shorLogicalOp_self_inverse :
    shorLogicalOp W * shorLogicalOp W = 1 :=
  mul_self _

/-- L' has X-support on all vertices. -/
@[simp]
theorem shorLogicalOp_xVec (v : ShorVertex W) :
    (shorLogicalOp W).xVec v = 1 := rfl

/-- L' has no Z-support on any vertex. -/
@[simp]
theorem shorLogicalOp_zVec (v : ShorVertex W) :
    (shorLogicalOp W).zVec v = 0 := rfl

/-- The weight of L' is 2W. -/
theorem shorLogicalOp_weight :
    (shorLogicalOp W).weight = 2 * W := by
  simp only [weight, support]
  have : ∀ x : ShorVertex W, (shorLogicalOp W).xVec x ≠ 0 ∨ (shorLogicalOp W).zVec x ≠ 0 := by
    intro x; left; simp [shorLogicalOp]
  rw [Finset.filter_true_of_mem (fun x _ => this x), Finset.card_univ,
    Fintype.card_sum, Fintype.card_fin]
  omega

/-- The support-restricted logical: L on the original support qubits only.
    Acts as X on all Sum.inl qubits and I on Sum.inr qubits. -/
def shorOriginalLogical : PauliOp (ShorVertex W) where
  xVec := fun q => match q with
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  zVec := 0

/-- The dummy product: ∏_{d ∈ D} X_d on dummy qubits only. -/
def shorDummyProduct : PauliOp (ShorVertex W) where
  xVec := fun q => match q with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  zVec := 0

/-- The factorization L' = L · ∏_d X_d.
    The full logical is the product of the support-restricted logical and dummy X product. -/
theorem shorLogicalOp_eq_mul :
    shorLogicalOp W = shorOriginalLogical W * shorDummyProduct W := by
  ext q <;> cases q <;> simp [shorLogicalOp, shorOriginalLogical, shorDummyProduct, mul_xVec, mul_zVec]

/-- L restricted to support qubits is pure X-type. -/
theorem shorOriginalLogical_pure_X :
    (shorOriginalLogical W).zVec = 0 := rfl

/-- Dummy product is pure X-type. -/
theorem shorDummyProduct_pure_X :
    (shorDummyProduct W).zVec = 0 := rfl

/-- L and the dummy product commute (both pure X-type). -/
theorem shorOriginalLogical_comm_dummyProduct :
    shorOriginalLogical W * shorDummyProduct W =
    shorDummyProduct W * shorOriginalLogical W :=
  PauliOp.mul_comm _ _

/-- L restricted to support is self-inverse. -/
theorem shorOriginalLogical_self_inverse :
    shorOriginalLogical W * shorOriginalLogical W = 1 :=
  mul_self _

/-- Dummy product is self-inverse. -/
theorem shorDummyProduct_self_inverse :
    shorDummyProduct W * shorDummyProduct W = 1 :=
  mul_self _

end LogicalOperator

/-! ## Measurement sign and dummy vertices

When dummy vertices are initialized in |+⟩ (eigenstate of X with eigenvalue +1),
measuring A_v on a dummy vertex always gives outcome +1 (= 0 in ZMod 2).
Therefore σ(L') = σ(L): the measurement sign of the extended logical equals
that of the original logical. This is the same result as Rem_10. -/

section MeasurementSign

variable (W : ℕ)

/-- Measurement sign with dummies: if all dummy outcomes are 0, the sign equals
    the sum over support outcomes only. -/
theorem shor_measurement_sign_dummies
    (supportOutcomes : Fin W → ZMod 2)
    (dummyOutcomes : Fin W → ZMod 2)
    (h_dummy : ∀ d : Fin W, dummyOutcomes d = 0) :
    ∑ v : ShorVertex W, Sum.elim supportOutcomes dummyOutcomes v =
    ∑ i : Fin W, supportOutcomes i := by
  rw [Fintype.sum_sum_type]
  simp [h_dummy]

end MeasurementSign

/-! ## Gauging structure on the Shor graph

The gauging measurement on the Shor graph has the following structure:
- The Gauss's law operators A_v (Def_2) on V ⊕ E are pure X-type
- Their product equals L' = ∏_v X_v (the logical being measured)
- The CX circuit (Rem_9) transforms A_v to X_v
- Measuring X on the dummy vertices corresponds to the Shor-style X measurements

The key observation: after measuring the dummy subgraph edges in the ungauging step,
the remaining state on dummy qubits is a GHZ-like state entangled with the support
qubits via the pairing edges {d_i, i}. This is exactly the Shor-style structure. -/

section GaugingStructure

variable (W : ℕ)
variable (Gdummy : SimpleGraph (Fin W)) [DecidableRel Gdummy.Adj]
         [Fintype (ShorGraph W Gdummy).edgeSet]

/-- The Gauss's law operator A_v on the Shor graph is pure X-type. -/
theorem shor_gaussLaw_pure_X (v : ShorVertex W) :
    (gaussLawOp (ShorGraph W Gdummy) v).zVec = 0 := by
  ext q; simp [gaussLawOp]

/-- The product of all Gauss operators on the Shor graph equals the logical L'.
    This is the structural content of Def_2's gaussLaw_product applied to the Shor graph. -/
theorem shor_gauss_product_eq_logical :
    logicalOp (ShorGraph W Gdummy) = ∏ v : ShorVertex W, gaussLawOp (ShorGraph W Gdummy) v :=
  (gaussLaw_product (ShorGraph W Gdummy)).symm

/-- The logical operator on the Shor graph's extended system (V ⊕ E)
    acts as X on all vertex qubits and I on edge qubits.
    On vertex qubits, this is L' = ∏_{v ∈ V ⊕ D} X_v. -/
@[simp]
theorem shor_logicalOp_xVec_vertex (v : ShorVertex W) :
    (logicalOp (ShorGraph W Gdummy)).xVec (Sum.inl v) = 1 := by
  simp [logicalOp]

@[simp]
theorem shor_logicalOp_xVec_edge (e : (ShorGraph W Gdummy).edgeSet) :
    (logicalOp (ShorGraph W Gdummy)).xVec (Sum.inr e) = 0 := by
  simp [logicalOp]

@[simp]
theorem shor_logicalOp_zVec (q : ExtQubit (ShorGraph W Gdummy)) :
    (logicalOp (ShorGraph W Gdummy)).zVec q = 0 := by
  simp [logicalOp]

end GaugingStructure

/-! ## Circuit correspondence

The CX entangling circuit (Rem_9) transforms A_v into X_v.
On the Shor graph, this means:
- Measuring X on support vertex (inl i) after the circuit = measuring A_{inl i} before
- Measuring X on dummy vertex (inr i) after the circuit = measuring A_{inr i} before
- The dummy X measurements in Shor-style correspond to measuring A_{d_i}
- The product of all A_v measurements = L' measurement (by gaussLaw_product)

This is the content of Rem_9's entanglingCircuit_transforms_gaussLaw applied
to the Shor graph. -/

section CircuitCorrespondence

variable (W : ℕ)
variable (Gdummy : SimpleGraph (Fin W)) [DecidableRel Gdummy.Adj]
         [Fintype (ShorGraph W Gdummy).edgeSet]

/-- The entangling circuit transforms A_v to X_v on the Shor graph.
    Here v is a vertex of the Shor graph (a ShorVertex W), and the result is
    pauliX (Sum.inl v) on the ExtQubit type. -/
theorem shor_circuit_transforms_gaussLaw (v : ShorVertex W) :
    CircuitImplementation.entanglingCircuitAction (ShorGraph W Gdummy)
      (gaussLawOp (ShorGraph W Gdummy) v) =
    pauliX (Sum.inl v) :=
  CircuitImplementation.entanglingCircuit_transforms_gaussLaw (ShorGraph W Gdummy) v

/-- The inverse: the CX circuit transforms X_v back to A_v. -/
theorem shor_circuit_transforms_pauliX (v : ShorVertex W) :
    CircuitImplementation.entanglingCircuitAction (ShorGraph W Gdummy) (pauliX (Sum.inl v)) =
    gaussLawOp (ShorGraph W Gdummy) v :=
  CircuitImplementation.entanglingCircuit_transforms_pauliX_to_gaussLaw
    (ShorGraph W Gdummy) v

/-- The circuit is involutive: applying it twice gives the identity. -/
theorem shor_circuit_involutive (P : PauliOp (ExtQubit (ShorGraph W Gdummy))) :
    CircuitImplementation.entanglingCircuitAction (ShorGraph W Gdummy)
      (CircuitImplementation.entanglingCircuitAction (ShorGraph W Gdummy) P) = P :=
  CircuitImplementation.entanglingCircuitAction_involutive (ShorGraph W Gdummy) P

/-- The circuit preserves Pauli commutation. -/
theorem shor_circuit_preserves_commutation (P Q : PauliOp (ExtQubit (ShorGraph W Gdummy))) :
    PauliCommute P Q ↔
    PauliCommute (CircuitImplementation.entanglingCircuitAction (ShorGraph W Gdummy) P)
                 (CircuitImplementation.entanglingCircuitAction (ShorGraph W Gdummy) Q) :=
  (CircuitImplementation.entanglingCircuit_preserves_commutation
    (ShorGraph W Gdummy) P Q).symm

end CircuitCorrespondence

/-! ## Edge structure of the Shor graph

The edge set of the Shor graph decomposes into:
1. W pairing edges {(inl i, inr i)} for i ∈ Fin W
2. The edges of the dummy subgraph Gdummy (lifted to Sum.inr)

We prove properties about this decomposition. -/

section EdgeStructure

variable (W : ℕ)
variable (Gdummy : SimpleGraph (Fin W)) [DecidableRel Gdummy.Adj]

/-- Support-support edges don't exist: no two support qubits are adjacent. -/
theorem shor_no_support_support_edges (i j : Fin W) :
    ¬(ShorGraph W Gdummy).Adj (Sum.inl i) (Sum.inl j) := by
  intro ⟨_, hor⟩
  rcases hor with ⟨k, hk1, hk2⟩ | ⟨k, hk1, _⟩ | ⟨a, _, ha, _, _⟩
  · exact absurd hk2 (by simp [Sum.inl_ne_inr])
  · exact absurd hk1 (by simp [Sum.inr_ne_inl])
  · exact absurd ha (by simp [Sum.inr_ne_inl])

/-- Support-dummy edges are exactly pairing edges: (inl i) ~ (inr j) iff i = j. -/
theorem shor_support_dummy_iff (i j : Fin W) :
    (ShorGraph W Gdummy).Adj (Sum.inl i) (Sum.inr j) ↔ i = j := by
  constructor
  · intro ⟨_, hor⟩
    rcases hor with ⟨k, hk1, hk2⟩ | ⟨k, hk1, _⟩ | ⟨_, _, ha, _, _⟩
    · exact (Sum.inl.inj hk1).trans (Sum.inr.inj hk2.symm)
    · exact absurd hk1 (by simp [Sum.inr_ne_inl])
    · exact absurd ha (by simp [Sum.inr_ne_inl])
  · intro heq; subst heq; exact shor_pairing_edge W Gdummy i

/-- Dummy-dummy edges are exactly the dummy subgraph edges. -/
theorem shor_dummy_dummy_iff (i j : Fin W) :
    (ShorGraph W Gdummy).Adj (Sum.inr i) (Sum.inr j) ↔ Gdummy.Adj i j := by
  constructor
  · intro ⟨_, hor⟩
    rcases hor with ⟨_, hk1, _⟩ | ⟨_, _, hk2⟩ | ⟨a, b, ha, hb, hadj⟩
    · exact absurd hk1 (by simp [Sum.inr_ne_inl])
    · exact absurd hk2 (by simp [Sum.inr_ne_inl])
    · rw [Sum.inr.inj ha, Sum.inr.inj hb]; exact hadj
  · intro hadj; exact shor_dummy_edge W Gdummy i j hadj

/-- The degree of a support vertex i in the Shor graph is exactly 1
    (only the pairing edge to d_i). -/
theorem shor_support_degree (i : Fin W) :
    (ShorGraph W Gdummy).neighborFinset (Sum.inl i) = {Sum.inr i} := by
  ext q
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro hadj
    cases q with
    | inl j => exact absurd hadj (shor_no_support_support_edges W Gdummy i j)
    | inr j =>
      have h := (shor_support_dummy_iff W Gdummy i j).mp hadj
      exact congrArg Sum.inr h.symm
  · intro heq; subst heq; exact shor_pairing_edge W Gdummy i

/-- The degree of each support vertex is exactly 1. -/
theorem shor_support_degree_eq_one (i : Fin W) :
    (ShorGraph W Gdummy).degree (Sum.inl i) = 1 := by
  rw [SimpleGraph.degree, shor_support_degree]
  simp

/-- The neighbor set of a dummy vertex i in the Shor graph is
    {inl i} ∪ (Gdummy neighbors of i lifted to Sum.inr). -/
theorem shor_dummy_neighborFinset (i : Fin W) :
    (ShorGraph W Gdummy).neighborFinset (Sum.inr i) =
    {Sum.inl i} ∪ (Gdummy.neighborFinset i).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext q
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_map]
  constructor
  · intro hadj
    cases q with
    | inl j =>
      left
      have hsymm := (ShorGraph W Gdummy).symm hadj
      have h := (shor_support_dummy_iff W Gdummy j i).mp hsymm
      exact congrArg Sum.inl h
    | inr j =>
      right
      refine ⟨j, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact (shor_dummy_dummy_iff W Gdummy i j).mp hadj
  · intro hor
    rcases hor with heq | ⟨j, hj, hq⟩
    · subst heq; exact (ShorGraph W Gdummy).symm (shor_pairing_edge W Gdummy i)
    · have heq : q = Sum.inr j := hq.symm
      subst heq
      rw [SimpleGraph.mem_neighborFinset] at hj
      exact shor_dummy_edge W Gdummy i j hj

end EdgeStructure

/-! ## Structural correspondence with Shor-style measurement

The Shor-style measurement protocol corresponds to the gauging procedure as follows:

| Shor-style step | Gauging step |
|---|---|
| GHZ state preparation on W dummy qubits | Connected dummy subgraph edges |
| Transversal CX_{d_i → i} | Pairing edges {d_i, i} |
| Measure X on each d_i | Measure A_{d_i} (Gauss operator at dummy vertex) |
| Product of outcomes = σ | σ = ∑_v ε_v (measurement sign) |

The key insight: after measuring the dummy subgraph edges (during ungauging),
the remaining dummy qubits form a GHZ state entangled with support qubits
via the W pairing edges. This is exactly the Shor-style entanglement structure.

The advantage of the gauging viewpoint: the dummy subgraph can be chosen freely
(path graph, star graph, expander, etc.) to optimize for hardware constraints. -/

section StructuralCorrespondence

variable (W : ℕ)
variable (Gdummy : SimpleGraph (Fin W)) [DecidableRel Gdummy.Adj]
         [Fintype (ShorGraph W Gdummy).edgeSet]

/-- The Shor graph is connected. -/
theorem shor_graph_is_connected (hW : 0 < W) (hconn : Gdummy.Connected) :
    (ShorGraph W Gdummy).Connected :=
  shorGraph_connected W Gdummy hW hconn

/-- All Gauss operators on the Shor graph mutually commute. -/
theorem shor_gauss_operators_commute (v w : ShorVertex W) :
    PauliCommute (gaussLawOp (ShorGraph W Gdummy) v) (gaussLawOp (ShorGraph W Gdummy) w) :=
  gaussLaw_commute (ShorGraph W Gdummy) v w

/-- Each Gauss operator is self-inverse. -/
theorem shor_gauss_self_inverse (v : ShorVertex W) :
    gaussLawOp (ShorGraph W Gdummy) v * gaussLawOp (ShorGraph W Gdummy) v = 1 :=
  mul_self _

/-- Measuring all A_v and taking the product gives the measurement of L'.
    This is the fundamental equivalence that makes the gauging procedure work. -/
theorem shor_product_measurement :
    ∏ v : ShorVertex W, gaussLawOp (ShorGraph W Gdummy) v =
    logicalOp (ShorGraph W Gdummy) :=
  gaussLaw_product (ShorGraph W Gdummy)

/-- The Gauss operator at a dummy vertex d_i is pure X-type. -/
theorem shor_gauss_at_dummy_is_X_type (i : Fin W) :
    (gaussLawOp (ShorGraph W Gdummy) (Sum.inr i)).zVec = 0 :=
  gaussLawOp_zVec (ShorGraph W Gdummy) (Sum.inr i)

/-- The Gauss operator at a support vertex i is pure X-type. -/
theorem shor_gauss_at_support_is_X_type (i : Fin W) :
    (gaussLawOp (ShorGraph W Gdummy) (Sum.inl i)).zVec = 0 :=
  gaussLawOp_zVec (ShorGraph W Gdummy) (Sum.inl i)

/-- **Structural correspondence summary.** -/
theorem shor_style_structural_correspondence (hW : 0 < W) (hconn : Gdummy.Connected) :
    (ShorGraph W Gdummy).Connected ∧
    Fintype.card (ShorVertex W) = 2 * W ∧
    (∀ v w : ShorVertex W,
      PauliCommute (gaussLawOp (ShorGraph W Gdummy) v)
                   (gaussLawOp (ShorGraph W Gdummy) w)) ∧
    (∀ v : ShorVertex W,
      gaussLawOp (ShorGraph W Gdummy) v * gaussLawOp (ShorGraph W Gdummy) v = 1) ∧
    (∏ v : ShorVertex W, gaussLawOp (ShorGraph W Gdummy) v =
      logicalOp (ShorGraph W Gdummy)) ∧
    (∀ i : Fin W, (ShorGraph W Gdummy).degree (Sum.inl i) = 1) :=
  ⟨shor_graph_is_connected W Gdummy hW hconn,
   shorGraph_card W,
   shor_gauss_operators_commute W Gdummy,
   shor_gauss_self_inverse W Gdummy,
   shor_product_measurement W Gdummy,
   shor_support_degree_eq_one W Gdummy⟩

end StructuralCorrespondence

/-! ## Degree sum and edge count analysis

The Shor graph has a special structure: support vertices have degree 1,
and dummy vertex degrees are determined by the dummy subgraph. We derive
degree sums and edge count bounds from these structural properties. -/

section DegreeAnalysis

variable (W : ℕ)
variable (Gdummy : SimpleGraph (Fin W)) [DecidableRel Gdummy.Adj]

/-- The degree of dummy vertex i in the Shor graph is 1 + its degree in Gdummy. -/
theorem shor_dummy_degree_eq (i : Fin W) :
    (ShorGraph W Gdummy).degree (Sum.inr i) =
    1 + Gdummy.degree i := by
  rw [SimpleGraph.degree, shor_dummy_neighborFinset]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_singleton, Finset.card_map, SimpleGraph.degree]
  · rw [Finset.disjoint_left]
    intro q hq hq'
    rw [Finset.mem_singleton] at hq
    subst hq
    rw [Finset.mem_map] at hq'
    obtain ⟨_, _, habs⟩ := hq'
    exact absurd habs (by simp [Sum.inl_ne_inr])

/-- The sum of degrees of support vertices is W (each has degree 1). -/
theorem shor_support_degree_sum :
    ∑ i : Fin W, (ShorGraph W Gdummy).degree (Sum.inl i) = W := by
  simp only [shor_support_degree_eq_one]
  simp

/-- The sum of degrees of dummy vertices is W + ∑ deg_Gdummy(i). -/
theorem shor_dummy_degree_sum :
    ∑ i : Fin W, (ShorGraph W Gdummy).degree (Sum.inr i) =
    W + ∑ i : Fin W, Gdummy.degree i := by
  simp only [shor_dummy_degree_eq]
  rw [Finset.sum_add_distrib]
  simp

/-- Total degree sum of the Shor graph equals 2 × |E(ShorGraph)|. -/
theorem shor_total_degree_sum :
    ∑ v : ShorVertex W, (ShorGraph W Gdummy).degree v =
    2 * ((ShorGraph W Gdummy).edgeFinset).card :=
  (ShorGraph W Gdummy).sum_degrees_eq_twice_card_edges

/-- The total degree sum decomposes as support + dummy contributions. -/
theorem shor_degree_sum_decompose :
    ∑ v : ShorVertex W, (ShorGraph W Gdummy).degree v =
    (∑ i : Fin W, (ShorGraph W Gdummy).degree (Sum.inl i)) +
    (∑ i : Fin W, (ShorGraph W Gdummy).degree (Sum.inr i)) :=
  Fintype.sum_sum_type _

/-- A connected dummy subgraph on W vertices has at least W-1 edges. -/
theorem shor_connected_dummy_edge_bound (hconn : Gdummy.Connected) :
    Nat.card (Fin W) ≤ Nat.card Gdummy.edgeSet + 1 :=
  hconn.card_vert_le_card_edgeSet_add_one

end DegreeAnalysis

/-! ## Optimization flexibility: degree bounds

The key advantage of the gauging viewpoint over standard Shor-style measurement:
the dummy subgraph can be optimized for specific constraints.

If Gdummy has maximum degree d, then every vertex in the Shor graph has degree
at most max(1, d+1). For a path graph (d=2), the Shor graph has max degree 3.
We formalize this max degree transfer property. -/

section Optimization

variable (W : ℕ)
variable (Gdummy : SimpleGraph (Fin W)) [DecidableRel Gdummy.Adj]

/-- If every dummy vertex has degree ≤ d in Gdummy, then every dummy vertex
    has degree ≤ d + 1 in the Shor graph (adding the pairing edge). -/
theorem shor_dummy_degree_bound (d : ℕ)
    (hbound : ∀ i : Fin W, Gdummy.degree i ≤ d) (i : Fin W) :
    (ShorGraph W Gdummy).degree (Sum.inr i) ≤ d + 1 := by
  rw [shor_dummy_degree_eq]
  have := hbound i
  omega

/-- Max degree of the entire Shor graph is bounded by d + 1. -/
theorem shor_max_degree_bound (d : ℕ)
    (hbound : ∀ i : Fin W, Gdummy.degree i ≤ d)
    (v : ShorVertex W) :
    (ShorGraph W Gdummy).degree v ≤ d + 1 := by
  cases v with
  | inl i =>
    rw [shor_support_degree_eq_one]
    omega
  | inr i =>
    exact shor_dummy_degree_bound W Gdummy d hbound i

/-- The Shor graph edge count via the handshaking identity. -/
theorem shor_edge_count_via_handshaking :
    2 * ((ShorGraph W Gdummy).edgeFinset).card =
    W + (W + ∑ i : Fin W, Gdummy.degree i) := by
  rw [← shor_total_degree_sum, shor_degree_sum_decompose,
    shor_support_degree_sum, shor_dummy_degree_sum]

/-- The handshaking lemma applied to the dummy subgraph. -/
theorem shor_dummy_handshaking :
    ∑ i : Fin W, Gdummy.degree i = 2 * (Gdummy.edgeFinset).card :=
  Gdummy.sum_degrees_eq_twice_card_edges

end Optimization

end ShorStyleMeasurement
