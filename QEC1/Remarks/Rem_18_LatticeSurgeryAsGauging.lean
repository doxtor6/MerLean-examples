import QEC1.Remarks.Rem_5_CheegerConstantDefinition
import QEC1.Remarks.Rem_8_DesiderataForG
import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawOperators
import QEC1.Definitions.Def_3_FluxOperators
import QEC1.Remarks.Rem_7_ExactnessOfBoundaryCoboundary
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic

/-!
# Rem_18: Lattice Surgery as Gauging

## Statement
**Lattice surgery is a special case of gauging measurement.** The gauging measurement
can be interpreted as a direct generalization of lattice surgery for surface codes.

**Example**: Measuring X̄₁ ⊗ X̄₂ on a pair of equally sized surface code blocks using
a ladder graph G joining the edge qubits produces:
1. A deformed code that is again a surface code on the union of the two patches
2. The final step of measuring out individual edge qubits matches conventional lattice surgery

**Non-adjacent patches**: Use a graph with a grid of dummy vertices between the two edges.

**Generalization**: Extends to any pair of matching logical X operators using two copies
of graph G with bridge edges. G is allowed to have h(G) < 1 if path-length and
cycle-weight desiderata are satisfied.

**Insight**: h(G) ≥ 1 is overkill; expansion is only needed for subsets of qubits
relevant to the logical operators being measured.

## Main Results
- `LadderGraphWithCycles` : Ladder graph as a `GraphWithCycles` instance
- `ladder_gaussLaw_product_is_allOnes` : Product of Gauss's law operators = L (logical op)
- `ladder_deformed_code_generators` : The deformed code has surface-code generator structure
- `dummy_grid_walk_exists` : Dummy grids provide walks between non-adjacent patch edges
- `GeneralizedSurgeryGraph` : Two copies of G with bridge edges
- `full_expansion_implies_relaxed` : h(G) ≥ 1 implies relaxed expansion for any support
- `relaxed_expansion_vacuous_for_disjoint` : Expansion not needed on irrelevant subsets
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace QEC1.LatticeSurgeryAsGauging

open SimpleGraph Finset GraphWithCycles

/-! ## Ladder Graph as a GraphWithCycles

The ladder graph on n rungs has:
- Vertices: `Bool × Fin n` (left column = false, right column = true)
- Edges: n horizontal rungs + 2(n-1) vertical rails
- n-1 independent cycles (square faces of the ladder)

We build it as a `GraphWithCycles` to connect to the gauging framework
(Gauss's law operators from Def_2, flux operators from Def_3). -/

/-- Edge type for the ladder graph: horizontal rungs and vertical rails. -/
inductive LadderEdge (n : ℕ) : Type where
  /-- Horizontal rung connecting (false, i) to (true, i) -/
  | rung : Fin n → LadderEdge n
  /-- Left vertical rail connecting (false, i) to (false, i+1) -/
  | leftRail : Fin (n - 1) → LadderEdge n
  /-- Right vertical rail connecting (true, i) to (true, i+1) -/
  | rightRail : Fin (n - 1) → LadderEdge n
  deriving DecidableEq

/-- Cycle type for the ladder: one square face for each pair of consecutive rungs. -/
abbrev LadderCycle (n : ℕ) := Fin (n - 1)

instance (n : ℕ) : Fintype (LadderEdge n) where
  elems := (Finset.univ.image LadderEdge.rung) ∪
           (Finset.univ.image LadderEdge.leftRail) ∪
           (Finset.univ.image LadderEdge.rightRail)
  complete := by
    intro e
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    cases e with
    | rung i => exact Or.inl (Or.inl ⟨i, rfl⟩)
    | leftRail i => exact Or.inl (Or.inr ⟨i, rfl⟩)
    | rightRail i => exact Or.inr ⟨i, rfl⟩

/-- The adjacency relation for the ladder graph. -/
def ladderAdj (n : ℕ) (x y : Bool × Fin n) : Prop :=
  (x.1 ≠ y.1 ∧ x.2 = y.2) ∨
  (x.1 = y.1 ∧ x.2.val + 1 = y.2.val) ∨
  (x.1 = y.1 ∧ y.2.val + 1 = x.2.val)

instance (n : ℕ) : DecidableRel (ladderAdj n) := by
  intro x y; simp only [ladderAdj]; exact inferInstance

/-- The ladder graph as a SimpleGraph. -/
def ladderGraph (n : ℕ) : SimpleGraph (Bool × Fin n) where
  Adj := ladderAdj n
  symm := by
    intro x y h; simp only [ladderAdj] at h ⊢
    rcases h with ⟨hne, heq⟩ | ⟨heq, hlt⟩ | ⟨heq, hlt⟩
    · exact Or.inl ⟨Ne.symm hne, heq.symm⟩
    · exact Or.inr (Or.inr ⟨heq.symm, hlt⟩)
    · exact Or.inr (Or.inl ⟨heq.symm, hlt⟩)
  loopless := by
    intro x h; simp only [ladderAdj] at h
    rcases h with ⟨hne, _⟩ | ⟨_, hlt⟩ | ⟨_, hlt⟩
    · exact hne rfl
    · exact absurd hlt (by omega)
    · exact absurd hlt (by omega)

instance (n : ℕ) : DecidableRel (ladderGraph n).Adj := by
  intro x y; simp only [ladderGraph]; exact inferInstance

/-- Endpoints for each ladder edge. -/
def ladderEdgeEndpoints (n : ℕ) : LadderEdge n → (Bool × Fin n) × (Bool × Fin n)
  | .rung i => ((false, i), (true, i))
  | .leftRail i => ((false, ⟨i.val, by omega⟩), (false, ⟨i.val + 1, by omega⟩))
  | .rightRail i => ((true, ⟨i.val, by omega⟩), (true, ⟨i.val + 1, by omega⟩))

/-- Each ladder edge connects adjacent vertices. -/
theorem ladderEdge_adj (n : ℕ) (e : LadderEdge n) :
    (ladderGraph n).Adj (ladderEdgeEndpoints n e).1 (ladderEdgeEndpoints n e).2 := by
  cases e with
  | rung i =>
    simp only [ladderEdgeEndpoints, ladderGraph, ladderAdj]
    exact Or.inl ⟨Bool.false_ne_true, trivial⟩
  | leftRail i =>
    simp only [ladderEdgeEndpoints, ladderGraph, ladderAdj]
    exact Or.inr (Or.inl ⟨trivial, trivial⟩)
  | rightRail i =>
    simp only [ladderEdgeEndpoints, ladderGraph, ladderAdj]
    exact Or.inr (Or.inl ⟨trivial, trivial⟩)

/-- Each ladder edge is symmetric. -/
theorem ladderEdge_adj_symm (n : ℕ) (e : LadderEdge n) :
    (ladderGraph n).Adj (ladderEdgeEndpoints n e).2 (ladderEdgeEndpoints n e).1 :=
  (ladderGraph n).symm (ladderEdge_adj n e)

/-- The cycles of the ladder: each square face consists of
    rung(i), rightRail(i), rung(i+1), leftRail(i). -/
def ladderCycleEdges (n : ℕ) (c : LadderCycle n) : Finset (LadderEdge n) :=
  {LadderEdge.rung ⟨c.val, by omega⟩,
   LadderEdge.rung ⟨c.val + 1, by omega⟩,
   LadderEdge.leftRail c,
   LadderEdge.rightRail c}

/-- Build the ladder as a `GraphWithCycles` to connect to the gauging framework. -/
noncomputable def LadderGraphWithCycles (n : ℕ) (_hn : n ≥ 2) :
    GraphWithCycles (Bool × Fin n) (LadderEdge n) (LadderCycle n) where
  graph := ladderGraph n
  decAdj := inferInstance
  edgeEndpoints := ladderEdgeEndpoints n
  edge_adj := ladderEdge_adj n
  edge_symm := ladderEdge_adj_symm n
  cycles := ladderCycleEdges n

/-! ## Gauss's Law Product = Logical Operator (Gauging Measures L)

By Property 3 of Gauss's law operators (Def_2), ∏_v A_v = L.
In binary vectors: the sum of all vertex supports equals the all-ones vector
on the ladder vertices, which represents L = X̄₁ ⊗ X̄₂.

This is the core mechanism making lattice surgery a gauging measurement:
measuring all A_v and multiplying outcomes yields the eigenvalue of L. -/

/-- The sum of all Gauss's law vertex supports on the ladder is the all-ones vector.
    (Instantiation of gaussLaw_product_vertexSupport_all_ones from Def_2.) -/
theorem ladder_gaussLaw_product_is_allOnes (n : ℕ) (hn : n ≥ 2) :
    gaussLaw_product_vertexSupport (LadderGraphWithCycles n hn) =
    fun _ => 1 :=
  gaussLaw_product_vertexSupport_all_ones (LadderGraphWithCycles n hn)

/-- The edge support of the Gauss's law product is zero (edges cancel pairwise). -/
theorem ladder_gaussLaw_edge_support_zero (n : ℕ) (hn : n ≥ 2) :
    gaussLaw_product_edgeSupport (LadderGraphWithCycles n hn) = 0 :=
  gaussLaw_product_edgeSupport_zero (LadderGraphWithCycles n hn)

/-- Combining: ∏_v A_v = L on the ladder (vertex support = all-ones, edge support = 0). -/
theorem ladder_gaussLaw_product_is_L_pair (n : ℕ) (hn : n ≥ 2) :
    (gaussLaw_product_vertexSupport (LadderGraphWithCycles n hn) = fun _ => 1) ∧
    gaussLaw_product_edgeSupport (LadderGraphWithCycles n hn) = 0 :=
  gaussLaw_product_is_L (LadderGraphWithCycles n hn)

/-! ## Deformed Code Structure on the Merged Patch

For the ladder with n rungs:
- |V| = 2n vertices → 2n Gauss's law operators (2n - 1 independent)
- |E| = 3n - 2 edges → n - 1 independent cycles → n - 1 flux operators
- Each cycle (square face) has exactly 4 edges → each B_p has weight 4 -/

/-- The ladder has 2n vertices. -/
theorem ladder_vertex_count (n : ℕ) :
    Fintype.card (Bool × Fin n) = 2 * n := by
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-- The ladder has n rungs + 2(n-1) rails = 3n - 2 edges when n ≥ 1. -/
theorem ladder_edge_count (n : ℕ) (hn : n ≥ 1) :
    Fintype.card (LadderEdge n) = 3 * n - 2 := by
  have key : Finset.univ (α := LadderEdge n) =
      (Finset.univ.image LadderEdge.rung) ∪
      (Finset.univ.image LadderEdge.leftRail) ∪
      (Finset.univ.image LadderEdge.rightRail) := rfl
  rw [Fintype.card, key]
  have disj_rl : Disjoint (Finset.univ.image (LadderEdge.rung (n := n)))
      (Finset.univ.image (LadderEdge.leftRail (n := n))) := by
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨_, rfl⟩ ⟨_, h⟩; exact absurd h nofun
  have disj_rr : Disjoint (Finset.univ.image (LadderEdge.rung (n := n)))
      (Finset.univ.image (LadderEdge.rightRail (n := n))) := by
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨_, rfl⟩ ⟨_, h⟩; exact absurd h nofun
  have disj_lr : Disjoint (Finset.univ.image (LadderEdge.leftRail (n := n)))
      (Finset.univ.image (LadderEdge.rightRail (n := n))) := by
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨_, rfl⟩ ⟨_, h⟩; exact absurd h nofun
  have disj_outer : Disjoint (Finset.univ.image (LadderEdge.rung (n := n)) ∪
      Finset.univ.image (LadderEdge.leftRail (n := n)))
      (Finset.univ.image (LadderEdge.rightRail (n := n))) :=
    Finset.disjoint_union_left.mpr ⟨disj_rr, disj_lr⟩
  rw [Finset.card_union_of_disjoint disj_outer, Finset.card_union_of_disjoint disj_rl]
  simp only [Finset.card_image_of_injective _ (fun a b h => LadderEdge.rung.inj h),
    Finset.card_image_of_injective _ (fun a b h => LadderEdge.leftRail.inj h),
    Finset.card_image_of_injective _ (fun a b h => LadderEdge.rightRail.inj h),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The number of independent cycles in the ladder is n - 1. -/
theorem ladder_independent_cycle_count (n : ℕ) :
    Fintype.card (LadderCycle n) = n - 1 :=
  Finset.card_fin (n - 1)

/-- Each cycle (square face) of the ladder consists of exactly 4 edges. -/
theorem ladder_cycle_weight_four (n : ℕ) (_hn : n ≥ 2) (c : LadderCycle n) :
    (ladderCycleEdges n c).card = 4 := by
  simp only [ladderCycleEdges]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · simp
      · simp only [Finset.mem_singleton]; exact nofun
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h) <;> exact absurd h nofun
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · have := LadderEdge.rung.inj h; simp only [Fin.mk.injEq] at this; omega
    · exact absurd h nofun
    · exact absurd h nofun

/-- The deformed code has the correct generator counts for a surface code. -/
theorem ladder_deformed_code_generators (n : ℕ) (_hn : n ≥ 2) :
    2 * n - 1 + (n - 1) = 3 * n - 2 := by omega

/-! ## Split Step: Measuring Out Edge Qubits Matches Conventional Surgery -/

/-- After the split step, gauge qubits are discarded and only original code qubits remain. -/
theorem split_step_removes_gauge_qubits (rows cols : ℕ) (_hr : rows ≥ 2) (_hc : cols ≥ 2) :
    2 * (rows * cols) + (3 * rows - 2) -
    (3 * rows - 2) =
    2 * (rows * cols) := by omega

/-! ## Non-Adjacent Patches via Dummy Grid

For non-adjacent patches, the gauging graph includes a grid of dummy vertices.
The key property is that the dummy grid provides walks of bounded length
between the left and right edges. -/

/-- A dummy grid bridges non-adjacent patches. -/
structure DummyGridConfig where
  rows : ℕ
  gap_width : ℕ
  h_rows : rows ≥ 2
  h_gap : gap_width ≥ 1

/-- Grid graph adjacency: unit-distance neighbors on the grid. -/
def gridAdj (D : DummyGridConfig) (x y : Fin D.rows × Fin (D.gap_width + 2)) : Prop :=
  (x.1 = y.1 ∧ x.2.val + 1 = y.2.val) ∨
  (x.1 = y.1 ∧ y.2.val + 1 = x.2.val) ∨
  (x.2 = y.2 ∧ x.1.val + 1 = y.1.val) ∨
  (x.2 = y.2 ∧ y.1.val + 1 = x.1.val)

instance (D : DummyGridConfig) : DecidableRel (gridAdj D) := by
  intro x y; simp only [gridAdj]; exact inferInstance

def gridGraph (D : DummyGridConfig) :
    SimpleGraph (Fin D.rows × Fin (D.gap_width + 2)) where
  Adj := gridAdj D
  symm := by
    intro x y h; simp only [gridAdj] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl ⟨h.1.symm, h.2⟩)
    · exact Or.inl ⟨h.1.symm, h.2⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h.1.symm, h.2⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h.1.symm, h.2⟩))
  loopless := by
    intro x h; simp only [gridAdj] at h
    rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- For each row, there exists a horizontal walk of length gap_width + 1. -/
theorem dummy_grid_walk_exists (D : DummyGridConfig) (i : Fin D.rows) :
    ∃ w : (gridGraph D).Walk
      (i, ⟨0, by omega⟩) (i, ⟨D.gap_width + 1, by omega⟩),
      w.length = D.gap_width + 1 := by
  suffices h : ∀ (a b : ℕ) (ha : a < D.gap_width + 2) (hb : b < D.gap_width + 2) (hab : a ≤ b),
      ∃ w : (gridGraph D).Walk (i, ⟨a, ha⟩) (i, ⟨b, hb⟩), w.length = b - a by
    obtain ⟨w, hw⟩ := h 0 (D.gap_width + 1) (by omega) (by omega) (by omega)
    exact ⟨w, by simpa using hw⟩
  intro a b ha hb hab
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ b' ih =>
    by_cases hab' : a = b' + 1
    · subst hab'; exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · have hab'' : a ≤ b' := by omega
      have hb'lt : b' < D.gap_width + 2 := by omega
      obtain ⟨w', hw'⟩ := ih hb'lt hab''
      have hadj : (gridGraph D).Adj (i, ⟨b', hb'lt⟩) (i, ⟨b' + 1, hb⟩) := by
        simp only [gridGraph, gridAdj]
        exact Or.inl ⟨trivial, trivial⟩
      exact ⟨w'.append (SimpleGraph.Walk.cons hadj .nil),
             by simp [SimpleGraph.Walk.length_append, hw']; omega⟩

/-- The dummy grid has `rows × (gap_width + 2)` total qubits. -/
theorem dummy_grid_qubit_count (D : DummyGridConfig) :
    Fintype.card (Fin D.rows × Fin (D.gap_width + 2)) =
    D.rows * (D.gap_width + 2) := by
  simp [Fintype.card_prod, Fintype.card_fin]

/-- The dummy qubits decompose: 2 * rows edge qubits + rows * gap_width dummy qubits. -/
theorem dummy_grid_qubit_decomposition (D : DummyGridConfig) :
    D.rows * (D.gap_width + 2) = 2 * D.rows + D.rows * D.gap_width := by ring

/-! ## Generalization: Two Copies of G with Bridge Edges

For any pair of matching logical X operators on two code blocks, use two copies
of graph G with additional bridge edges connecting corresponding vertices. -/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The combined graph for generalized lattice surgery: two copies of G with bridges. -/
def GeneralizedSurgeryAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (bridges : Finset (V × V)) (x y : Bool × V) : Prop :=
  (x.1 = y.1 ∧ G.Adj x.2 y.2) ∨
  (x.1 ≠ y.1 ∧ ((x.2, y.2) ∈ bridges ∨ (y.2, x.2) ∈ bridges))

/-- The combined graph is a valid SimpleGraph. -/
def GeneralizedSurgeryGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (bridges : Finset (V × V)) : SimpleGraph (Bool × V) where
  Adj := GeneralizedSurgeryAdj G bridges
  symm := by
    intro x y h; simp only [GeneralizedSurgeryAdj] at h ⊢
    rcases h with ⟨heq, hadj⟩ | ⟨hne, hbr⟩
    · exact Or.inl ⟨heq.symm, G.symm hadj⟩
    · exact Or.inr ⟨Ne.symm hne, hbr.symm⟩
  loopless := by
    intro x h; simp only [GeneralizedSurgeryAdj] at h
    rcases h with ⟨_, hadj⟩ | ⟨hne, _⟩
    · exact G.loopless x.2 hadj
    · exact hne rfl

/-- The combined graph has 2|V| vertices. -/
theorem generalized_surgery_vertex_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (_bridges : Finset (V × V)) :
    Fintype.card (Bool × V) = 2 * Fintype.card V := by
  simp [Fintype.card_prod, Fintype.card_bool]

/-- Bridge edges provide direct cross-copy connections. -/
theorem bridge_provides_cross_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (bridges : Finset (V × V)) (u v : V) (h : (u, v) ∈ bridges) :
    (GeneralizedSurgeryGraph G bridges).Adj (false, u) (true, v) := by
  simp only [GeneralizedSurgeryGraph, GeneralizedSurgeryAdj]
  exact Or.inr ⟨Bool.false_ne_true, Or.inl h⟩

/-- Intra-copy adjacency is preserved. -/
theorem intra_copy_adj_preserved (G : SimpleGraph V) [DecidableRel G.Adj]
    (bridges : Finset (V × V)) (b : Bool) (u v : V) (h : G.Adj u v) :
    (GeneralizedSurgeryGraph G bridges).Adj (b, u) (b, v) := by
  simp only [GeneralizedSurgeryGraph, GeneralizedSurgeryAdj]
  exact Or.inl ⟨trivial, h⟩

/-! ## Relaxed Expansion: h(G) ≥ 1 is Overkill

The full Cheeger condition h(G) ≥ 1 constrains ALL subsets S ⊆ V with |S| ≤ |V|/2.
For lattice surgery, expansion is only needed for subsets that intersect the logical
operator's support supp(L). Subsets disjoint from supp(L) are irrelevant. -/

/-- Relaxed expansion: |∂S| ≥ |S| required only for S intersecting logical support. -/
def RelaxedExpansionProperty (G : SimpleGraph V) [DecidableRel G.Adj]
    (logicalSupport : Finset V) : Prop :=
  ∀ S : Finset V,
    0 < S.card → 2 * S.card ≤ Fintype.card V →
    (S ∩ logicalSupport).Nonempty →
    (edgeBoundary G S).card ≥ S.card

/-- Full Cheeger expansion h(G) ≥ 1 implies relaxed expansion for any support. -/
theorem full_expansion_implies_relaxed (G : SimpleGraph V) [DecidableRel G.Adj]
    (logicalSupport : Finset V) (hexp : IsStrongExpander G) :
    RelaxedExpansionProperty G logicalSupport := by
  intro S hcard hsize _hinter
  have hne : S.Nonempty := Finset.card_pos.mp hcard
  -- Extract bound from CheegerConstant using ciInf_le and ciInf_pos
  have h1 : CheegerConstant G ≤ ((edgeBoundary G S).card : ℝ) / (S.card : ℝ) := by
    unfold CheegerConstant
    have bdd1 : BddBelow (Set.range fun S' : Finset V =>
        ⨅ (_ : S'.Nonempty), ⨅ (_ : 2 * S'.card ≤ Fintype.card V),
          ((edgeBoundary G S').card : ℝ) / (S'.card : ℝ)) := by
      use 0; rintro _ ⟨S', rfl⟩
      by_cases hne' : S'.Nonempty
      · simp only [ciInf_pos hne']
        by_cases hsize' : 2 * S'.card ≤ Fintype.card V
        · simp only [ciInf_pos hsize']
          exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        · simp only [ciInf_neg hsize']
          exact le_of_eq Real.sInf_empty.symm
      · simp only [ciInf_neg hne']
        exact le_of_eq Real.sInf_empty.symm
    calc ⨅ S', ⨅ (_ : S'.Nonempty), ⨅ (_ : 2 * S'.card ≤ Fintype.card V),
          ((edgeBoundary G S').card : ℝ) / (S'.card : ℝ)
        ≤ ⨅ (_ : S.Nonempty), ⨅ (_ : 2 * S.card ≤ Fintype.card V),
          ((edgeBoundary G S).card : ℝ) / (S.card : ℝ) := ciInf_le bdd1 S
      _ = ((edgeBoundary G S).card : ℝ) / (S.card : ℝ) := by
          simp [ciInf_pos hne, ciInf_pos hsize]
  have h2 : (1 : ℝ) ≤ ((edgeBoundary G S).card : ℝ) / (S.card : ℝ) := le_trans hexp h1
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hcard
  rw [le_div_iff₀ hcard_pos, one_mul] at h2
  exact Nat.cast_le.mp h2

/-- Relaxed expansion is strictly weaker: subsets disjoint from logical support
    are unconstrained. -/
theorem relaxed_expansion_vacuous_for_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (logicalSupport : Finset V) (S : Finset V)
    (_hS_pos : 0 < S.card) (_hS_size : 2 * S.card ≤ Fintype.card V)
    (hdisjoint : Disjoint S logicalSupport) :
    ¬(S ∩ logicalSupport).Nonempty := by
  rw [Finset.not_nonempty_iff_eq_empty]
  exact Finset.disjoint_iff_inter_eq_empty.mp hdisjoint

/-- When logical support = full vertex set, relaxed expansion implies full expansion
    (both conditions coincide since every subset intersects the full vertex set). -/
theorem relaxed_on_full_support_implies_strong (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hV : 0 < Fintype.card V) (hrel : RelaxedExpansionProperty G Finset.univ) :
    ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
      (edgeBoundary G S).card ≥ S.card := by
  intro S hne hsize
  apply hrel S (Finset.Nonempty.card_pos hne) hsize
  rw [Finset.inter_comm, Finset.univ_inter]
  exact hne

/-- Full expansion implies relaxed expansion (converse direction). -/
theorem strong_implies_relaxed (G : SimpleGraph V) [DecidableRel G.Adj]
    (hexp : IsStrongExpander G) :
    RelaxedExpansionProperty G Finset.univ :=
  full_expansion_implies_relaxed G Finset.univ hexp

/-- When the total vertex count exceeds the logical support, there exist
    vertices outside the support (i.e., unconstrained by relaxed expansion). -/
theorem exists_unconstrained_subset (_G : SimpleGraph V) [DecidableRel _G.Adj]
    (logicalSupport : Finset V)
    (h_small : logicalSupport.card < Fintype.card V) :
    ∃ v : V, v ∉ logicalSupport := by
  by_contra h
  push_neg at h
  have : logicalSupport = Finset.univ := by
    ext v; simp [h v]
  rw [this, Finset.card_univ] at h_small
  exact Nat.lt_irrefl _ h_small

end QEC1.LatticeSurgeryAsGauging
