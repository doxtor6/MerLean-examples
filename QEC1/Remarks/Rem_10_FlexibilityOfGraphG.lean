import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import QEC1.Definitions.Def_4_DeformedCode
import QEC1.Lemmas.Lem_1_DeformedCodeChecks
import QEC1.Remarks.Rem_4_NotationCheegerConstant
import Mathlib.Tactic

/-!
# Remark 10: Flexibility of Graph G

## Statement
The gauging measurement procedure (Definition 5) allows arbitrary choice of the
connected graph G with vertex set equal to the support of L. The properties of
the deformed code depend strongly on this choice.

**Additional flexibility:**
1. **Dummy vertices:** G can have additional vertices beyond the support of L,
   achieved by gauging L' = L · ∏_{dummy} X_v.
2. **Graph properties:** The choice of G determines |E| (edge qubit count),
   deformed check weights (path lengths), and distance (expansion).

## Main Results
- `extendedLogicalOp` : L' on V ⊕ D, the extended logical with dummy vertices
- `extendedLogicalOp_eq_mul` : L' = L · ∏_{d ∈ D} X_d (factorization)
- `extendedLogicalOp_self_inverse` : L' is self-inverse
- `measurement_sign_with_dummies` : σ(L') = σ(L) when dummies give +1
- `deformed_code_edge_overhead` : the deformed code has |V| + |E| qubits,
  so different graphs give different overhead via |E|
- `deformed_code_check_overhead` : the deformed code has |V| + |C| + |J| checks
- `edge_expansion_lower_bounds_boundary` : expansion of G controls distance
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace FlexibilityOfGraphG

open Finset PauliOp GaussFlux DeformedOperator DeformedCode DeformedCodeChecks
     GaugingMeasurement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Dummy vertices

The graph G can have additional "dummy" vertices beyond the support of L.
We formalize this by considering a type V ⊕ D that extends V with dummy vertices,
and defining L' = L · ∏_{d ∈ D} X_d = ∏_{q ∈ V ⊕ D} X_q.

The key insight: since dummy qubits are in |+⟩ (eigenstate of X with eigenvalue +1),
measuring X on a dummy vertex always gives +1 (outcome 0 in ZMod 2). Therefore
the measurement sign of L' equals that of L. -/

section DummyVertices

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The original logical operator L on V: L = ∏_{v ∈ V} X_v. -/
def originalLogicalOp : PauliOp V where
  xVec := fun _ => 1
  zVec := 0

/-- The extended logical operator L' on the extended vertex type V ⊕ D.
    L' = ∏_{q ∈ V ⊕ D} X_q = L · ∏_{d ∈ D} X_d. -/
def extendedLogicalOp : PauliOp (V ⊕ D) where
  xVec := fun _ => 1
  zVec := 0

/-- The dummy X product: ∏_{d ∈ D} X_d acting on V ⊕ D. -/
def dummyXProduct : PauliOp (V ⊕ D) where
  xVec := fun q => match q with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  zVec := 0

/-- L lifted to V ⊕ D: acts as X on all V-qubits and I on D-qubits. -/
def liftedLogicalOp : PauliOp (V ⊕ D) where
  xVec := fun q => match q with
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  zVec := 0

/-- **Key factorization**: L' = L_lift · ∏_{d ∈ D} X_d on V ⊕ D.
    The extended logical is the product of the lifted original logical
    and the dummy X product. -/
theorem extendedLogicalOp_eq_mul :
    extendedLogicalOp (V := V) (D := D) =
    liftedLogicalOp (V := V) (D := D) * dummyXProduct (V := V) (D := D) := by
  ext q <;> cases q <;> simp [extendedLogicalOp, liftedLogicalOp, dummyXProduct, mul_xVec, mul_zVec]

/-- L' is self-inverse: L' · L' = 1. -/
theorem extendedLogicalOp_self_inverse :
    (extendedLogicalOp (V := V) (D := D)) * extendedLogicalOp = 1 :=
  mul_self _

/-- L' is pure X-type: it has no Z-support. -/
theorem extendedLogicalOp_pure_X :
    (extendedLogicalOp (V := V) (D := D)).zVec = 0 := by
  ext q; simp [extendedLogicalOp]

/-- The X-support of L' is all of V ⊕ D. -/
theorem extendedLogicalOp_supportX_eq_univ :
    (extendedLogicalOp (V := V) (D := D)).supportX = Finset.univ := by
  ext q; simp [supportX, extendedLogicalOp]

/-- L' equals prodX(univ) on V ⊕ D. -/
theorem extendedLogicalOp_eq_prodX_univ :
    extendedLogicalOp (V := V) (D := D) = prodX Finset.univ := by
  ext q <;> simp [extendedLogicalOp, prodX]

/-- L' restricted to original vertices matches L: xVec on Sum.inl v is 1. -/
@[simp]
theorem extendedLogicalOp_xVec_original (v : V) :
    (extendedLogicalOp (V := V) (D := D)).xVec (Sum.inl v) = 1 := by
  simp [extendedLogicalOp]

/-- L' on dummy vertices: xVec on Sum.inr d is 1. -/
@[simp]
theorem extendedLogicalOp_xVec_dummy (d : D) :
    (extendedLogicalOp (V := V) (D := D)).xVec (Sum.inr d) = 1 := by
  simp [extendedLogicalOp]

/-- L' has no Z-action on any qubit. -/
@[simp]
theorem extendedLogicalOp_zVec_eq_zero (q : V ⊕ D) :
    (extendedLogicalOp (V := V) (D := D)).zVec q = 0 := by
  simp [extendedLogicalOp]

/-- The lifted logical matches the original on V-qubits. -/
@[simp]
theorem liftedLogicalOp_xVec_original (v : V) :
    (liftedLogicalOp (V := V) (D := D)).xVec (Sum.inl v) = 1 := by
  simp [liftedLogicalOp]

/-- The lifted logical is identity on D-qubits. -/
@[simp]
theorem liftedLogicalOp_xVec_dummy (d : D) :
    (liftedLogicalOp (V := V) (D := D)).xVec (Sum.inr d) = 0 := by
  simp [liftedLogicalOp]

/-- The dummy X product is identity on V-qubits. -/
@[simp]
theorem dummyXProduct_xVec_original (v : V) :
    (dummyXProduct (V := V) (D := D)).xVec (Sum.inl v) = 0 := by
  simp [dummyXProduct]

/-- The dummy X product acts as X on D-qubits. -/
@[simp]
theorem dummyXProduct_xVec_dummy (d : D) :
    (dummyXProduct (V := V) (D := D)).xVec (Sum.inr d) = 1 := by
  simp [dummyXProduct]

/-- **Measurement sign with dummies**: the measurement sign of L' equals that of L
    when dummy vertices give +1 outcomes (outcome 0 in ZMod 2).
    This is the formal content of "dummy vertices don't affect the logical measurement." -/
theorem measurement_sign_with_dummies
    (originalOutcomes : V → ZMod 2)
    (dummyOutcomes : D → ZMod 2)
    (h_dummy_plus : ∀ d : D, dummyOutcomes d = 0) :
    ∑ q : V ⊕ D, (Sum.elim originalOutcomes dummyOutcomes q) =
    ∑ v : V, originalOutcomes v := by
  rw [Fintype.sum_sum_type]
  simp [h_dummy_plus]

/-- The weight of L' equals |V| + |D|. -/
theorem extendedLogicalOp_weight :
    (extendedLogicalOp (V := V) (D := D)).weight =
    Fintype.card V + Fintype.card D := by
  unfold weight support
  simp [extendedLogicalOp, Fintype.card_sum]

/-- When D is empty, L' restricted to V has the same weight as L. -/
theorem extendedLogicalOp_no_dummies [IsEmpty D] :
    (extendedLogicalOp (V := V) (D := D)).weight = Fintype.card V := by
  rw [extendedLogicalOp_weight, Fintype.card_eq_zero (α := D), add_zero]

/-- The Z-support of the dummy X product is empty on all qubits.
    This means dummyXProduct commutes with everything on the Z side,
    and adding dummy X operators never changes Z-support parity. -/
theorem dummyXProduct_zVec_zero (q : V ⊕ D) :
    (dummyXProduct (V := V) (D := D)).zVec q = 0 := by
  simp [dummyXProduct]

/-- The lifted logical has empty Z-support (pure X-type). -/
theorem liftedLogicalOp_zVec_zero (q : V ⊕ D) :
    (liftedLogicalOp (V := V) (D := D)).zVec q = 0 := by
  simp [liftedLogicalOp]

/-- The dummy X product is self-inverse. -/
theorem dummyXProduct_self_inverse :
    (dummyXProduct (V := V) (D := D)) * dummyXProduct = 1 :=
  mul_self _

/-- The lifted logical is self-inverse. -/
theorem liftedLogicalOp_self_inverse :
    (liftedLogicalOp (V := V) (D := D)) * liftedLogicalOp = 1 :=
  mul_self _

/-- The lifted logical and dummy X product commute (both pure X-type). -/
theorem liftedLogicalOp_comm_dummyXProduct :
    (liftedLogicalOp (V := V) (D := D)) * dummyXProduct =
    dummyXProduct * liftedLogicalOp := by
  exact PauliOp.mul_comm _ _

end DummyVertices

/-! ## Graph properties affect deformed code overhead

The choice of graph G determines the parameters of the deformed code:
- Number of edge qubits = |E(G)| (from deformedStabilizerCode_numQubits)
- Number of Gauss checks = |V| (one per vertex)
- Number of flux checks = |C| (one per cycle)
These facts connect existing definitions to the remark's claims. -/

section GraphOverhead

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-- The deformed code's qubit count is |V| + |E|, so the edge qubit overhead
    (the additional qubits beyond the original |V|) is exactly |E(G)|.
    Different graphs G give different overhead via their edge count. -/
theorem deformed_code_edge_overhead
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numQubits =
    Fintype.card V + Fintype.card G.edgeSet :=
  deformedStabilizerCode_numQubits G cycles checks data hcyc hcomm

/-- The deformed code's check count is |V| + |C| + |J|: |V| Gauss checks,
    |C| flux checks, and |J| deformed original checks. The overhead in checks
    beyond the original |J| is |V| + |C|. -/
theorem deformed_code_check_overhead
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numChecks =
    Fintype.card V + Fintype.card C + Fintype.card J :=
  deformedStabilizerCode_numChecks G cycles checks data hcyc hcomm

/-- Two graphs with different edge counts produce deformed codes with
    different qubit counts. The qubit overhead difference equals the
    edge count difference. -/
theorem different_graphs_different_qubit_count
    (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [Fintype G₁.edgeSet]
    [DecidableRel G₂.Adj] [Fintype G₂.edgeSet]
    (h_ne : Fintype.card G₁.edgeSet ≠ Fintype.card G₂.edgeSet) :
    Fintype.card V + Fintype.card G₁.edgeSet ≠
    Fintype.card V + Fintype.card G₂.edgeSet := by
  omega

end GraphOverhead

/-! ## Expansion and code distance

The Cheeger constant of G affects the distance of the deformed code.
By Rem_4, for any valid subset S ⊆ V with |S| ≤ |V|/2:
  h(G) · |S| ≤ |∂S|
This means an expander graph ensures that small vertex subsets have
large edge boundaries, which prevents low-weight logical operators
in the deformed code from surviving the deformation. -/

section ExpansionAndDistance

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- For an expander graph, every valid subset has proportionally large boundary.
    This is the mechanism by which expansion of G controls the distance
    of the deformed code: logical operators supported on small subsets
    necessarily have large edge boundary. -/
theorem edge_expansion_lower_bounds_boundary
    (c : ℝ) (hexp : QEC1.SimpleGraph.IsExpander G c)
    (S : Finset V) (hne : S.Nonempty)
    (hsize : 2 * S.card ≤ Fintype.card V) :
    c * S.card ≤ (QEC1.SimpleGraph.edgeBoundary G S).card :=
  QEC1.SimpleGraph.edgeBoundary_card_ge_of_cheeger G c hexp.2 S hne hsize

/-- For a connected graph on ≥ 2 vertices, the edge set is nonempty
    (at least one edge exists). This means gauging always introduces
    at least one auxiliary qubit. -/
theorem connected_has_edge (hconn : G.Connected)
    (hcard : 2 ≤ Fintype.card V) :
    0 < Fintype.card G.edgeSet := by
  -- Connected graph on ≥ 2 vertices has at least one edge
  rw [Fintype.card_pos_iff]
  obtain ⟨S, hS⟩ := QEC1.SimpleGraph.cheegerValidSubsets'_nonempty_of_card_ge_two hcard
  -- S is nonempty and valid; we need to show G has an edge
  -- A connected graph on ≥ 2 vertices must have an adjacent pair
  have hV : ∃ a b : V, a ≠ b := by
    have : 1 < Fintype.card V := by omega
    rw [Fintype.one_lt_card_iff_nontrivial] at this
    exact let ⟨a, b, hab⟩ := this; ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hV
  have := hconn a b
  obtain ⟨w⟩ := this
  induction w with
  | nil => exact absurd rfl hab
  | @cons u v' _ hadj _ _ =>
    exact ⟨⟨s(u, v'), G.mem_edgeSet.mpr hadj⟩⟩

end ExpansionAndDistance

/-! ## Deformed check weight depends on edge-path length

The weight of the deformed check s̃_j on the extended system V ⊕ E depends on:
- The original check s_j (its X- and Z-support on V)
- The edge-path γ_j (determines the Z-support on E)

The Z-support of s̃_j on edges is exactly the support of γ_j, so the deformed
check weight includes a contribution from the number of edges in γ_j.
Shorter paths in G lead to lower-weight deformed checks. -/

section DeformedCheckWeight

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- The edge Z-support of a deformed check equals the support of the edge-path γ.
    More edges in γ means more Z-support on edge qubits, hence higher weight.
    This connects the graph structure (path lengths) to check weights. -/
theorem deformedCheck_zSupport_on_edges
    (s : PauliOp V) (γ : G.edgeSet → ZMod 2) (e : G.edgeSet) :
    (deformedCheck G s γ).zVec (Sum.inr e) = γ e :=
  deformedOpExt_zVec_edge G s γ e

/-- The edge X-support of a deformed check is empty: deformed checks have
    no X-action on edge qubits. -/
theorem deformedCheck_xSupport_on_edges
    (s : PauliOp V) (γ : G.edgeSet → ZMod 2) (e : G.edgeSet) :
    (deformedCheck G s γ).xVec (Sum.inr e) = 0 :=
  deformedOpExt_xVec_edge G s γ e

/-- The number of edge qubits where the deformed check acts non-trivially
    (via Z) equals the number of edges in γ with γ(e) ≠ 0.
    This is the "edge contribution" to the deformed check weight. -/
theorem deformedCheck_edge_action_count
    (s : PauliOp V) (γ : G.edgeSet → ZMod 2) :
    (Finset.univ.filter (fun e : G.edgeSet =>
      (deformedCheck G s γ).zVec (Sum.inr e) ≠ 0)).card =
    (Finset.univ.filter (fun e : G.edgeSet => γ e ≠ 0)).card := by
  congr 1

/-- A zero edge-path adds no edge weight: the deformed check acts only on vertices. -/
theorem deformedCheck_zero_path_edge_count
    (s : PauliOp V) :
    (Finset.univ.filter (fun e : G.edgeSet =>
      (deformedCheck G s (0 : G.edgeSet → ZMod 2)).zVec (Sum.inr e) ≠ 0)).card = 0 := by
  simp [deformedCheck_zSupport_on_edges]

end DeformedCheckWeight

end FlexibilityOfGraphG
