import QEC1.Remarks.Rem_10_FlexibilityOfGraphG
import QEC1.Remarks.Rem_4_NotationCheegerConstant
import QEC1.Lemmas.Lem_1_DeformedCodeChecks
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Remark 11: Desiderata for Graph G

## Statement
When choosing a constant-degree graph G for the gauging measurement, the goals are:

1. **Short paths for deformation:** G should contain a constant-length edge-path between
   any pair of vertices in the Z-type support of the same original check. This ensures
   the deformed checks have bounded weight.

2. **Sufficient expansion:** The Cheeger constant should satisfy h(G) ≥ 1. This ensures
   the deformed code has distance at least d (the original distance).

3. **Low-weight cycle basis:** There should exist a generating set of cycles where each
   cycle has weight at most some constant. This ensures the flux operators B_p have
   bounded weight.

When all three conditions are satisfied with constants independent of n, the gauging
measurement procedure has constant overhead per qubit, LDPC property preserved, and
no distance reduction.

## Main Results
- `ShortPathsForDeformation` : Desideratum 1 — bounded graph distance within Z-support
- `SufficientExpansion` : Desideratum 2 — Cheeger constant ≥ 1
- `LowWeightCycleBasis` : Desideratum 3 — bounded cycle weights
- `AllDesiderataSatisfied` : All three conditions bundled
- `sufficient_expansion_implies_expander` : h(G) ≥ 1 ⟹ G is a 1-expander
- `low_weight_cycles_bound_flux_weight` : bounded cycle weight ⟹ bounded flux weight
- `constant_degree_bounds_edges` : constant degree ⟹ linear edge overhead
- `desiderata_consequences` : combined summary theorem
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace DesiderataForGraphG

open Finset PauliOp GaussFlux DeformedOperator DeformedCode DeformedCodeChecks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Desideratum 1: Short Paths for Deformation

G should contain a constant-length edge-path between any pair of vertices that are
in the Z-type support of the same original check. This ensures that the edge-path γ
used in the deformation has bounded length, giving bounded-weight deformed checks. -/

section ShortPaths

variable (G : SimpleGraph V) [DecidableRel G.Adj]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-- Desideratum 1: Short paths for deformation. For every original check s_j,
any two vertices in the Z-support of s_j have graph distance at most D in G. -/
def ShortPathsForDeformation (D : ℕ) : Prop :=
  ∀ j : J, ∀ u v : V,
    u ∈ (checks j).supportZ → v ∈ (checks j).supportZ →
    G.dist u v ≤ D

/-- Short paths give a direct distance bound. -/
theorem short_paths_bound_distance
    (D : ℕ) (hsp : ShortPathsForDeformation G checks D)
    (j : J) (u v : V) (hu : u ∈ (checks j).supportZ) (hv : v ∈ (checks j).supportZ) :
    G.dist u v ≤ D :=
  hsp j u v hu hv

/-- On a connected graph, short paths guarantee reachability: vertices in the same
Z-support are reachable from each other. -/
theorem short_paths_imply_reachable
    (hconn : G.Connected) (j : J) (u v : V)
    (_hu : u ∈ (checks j).supportZ) (_hv : v ∈ (checks j).supportZ) :
    G.Reachable u v :=
  hconn u v

/-- The Z-support of a check is a subset of the full support, so its cardinality
is bounded by the check weight. -/
theorem zSupport_card_le_weight (j : J) :
    (checks j).supportZ.card ≤ (checks j).weight := by
  unfold PauliOp.weight
  apply Finset.card_le_card
  intro v hv
  rw [PauliOp.mem_supportZ] at hv
  rw [PauliOp.mem_support]
  exact Or.inr hv

/-- Short paths bound the edge contribution to deformed checks. The deformed
check s̃_j(γ) has Z-action on exactly those edges where γ(e) ≠ 0.
If γ has at most B nonzero entries, the edge contribution is at most B. -/
theorem deformed_check_edge_bound
    [Fintype G.edgeSet]
    (j : J) (γ : G.edgeSet → ZMod 2) (B : ℕ)
    (hγ : (Finset.univ.filter (fun e : G.edgeSet => γ e ≠ 0)).card ≤ B) :
    (Finset.univ.filter (fun e : G.edgeSet =>
      (deformedCheck G (checks j) γ).zVec (Sum.inr e) ≠ 0)).card ≤ B := by
  rw [FlexibilityOfGraphG.deformedCheck_edge_action_count]
  exact hγ

/-- Zero edge-path adds no edge weight to the deformed check. -/
@[simp]
theorem deformed_check_zero_path_no_edges
    [Fintype G.edgeSet] (j : J) :
    (Finset.univ.filter (fun e : G.edgeSet =>
      (deformedCheck G (checks j) (0 : G.edgeSet → ZMod 2)).zVec (Sum.inr e) ≠ 0)).card = 0 :=
  FlexibilityOfGraphG.deformedCheck_zero_path_edge_count G (checks j)

end ShortPaths

/-! ## Desideratum 2: Sufficient Expansion

The Cheeger constant should satisfy h(G) ≥ 1. This ensures the deformed code has
distance at least d (the original distance), as shown in Lemma 3. -/

section Expansion

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Desideratum 2: Sufficient expansion. The Cheeger constant of G is at least 1. -/
def SufficientExpansion : Prop :=
  1 ≤ QEC1.cheegerConstant G

/-- Sufficient expansion implies G is a 1-expander. -/
theorem sufficient_expansion_implies_expander
    (hexp : SufficientExpansion G) :
    QEC1.SimpleGraph.IsExpander G 1 :=
  ⟨by norm_num, hexp⟩

/-- With sufficient expansion, every valid subset S has |∂S| ≥ |S|. -/
theorem expansion_gives_boundary_bound
    (hexp : SufficientExpansion G)
    (S : Finset V) (hne : S.Nonempty) (hsize : 2 * S.card ≤ Fintype.card V) :
    (S.card : ℝ) ≤ (QEC1.SimpleGraph.edgeBoundary G S).card := by
  have h := QEC1.SimpleGraph.edgeBoundary_card_ge_of_cheeger G 1 hexp S hne hsize
  linarith

/-- Sufficient expansion implies the Cheeger constant is positive. -/
theorem sufficient_expansion_pos
    (hexp : SufficientExpansion G) :
    0 < QEC1.cheegerConstant G :=
  lt_of_lt_of_le one_pos hexp

end Expansion

/-! ## Desideratum 3: Low-Weight Cycle Basis

There should exist a generating set of cycles for G where each cycle has weight
at most some constant W. This ensures the flux operators B_p have bounded weight. -/

section CycleBasis

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]

/-- Desideratum 3: Low-weight cycle basis. Each cycle in the generating set
has at most W edges. -/
def LowWeightCycleBasis (W : ℕ) : Prop :=
  ∀ c : C, (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c)).card ≤ W

/-- Low-weight cycles imply bounded flux check weight: the weight of B_p equals
the number of edges in cycle p, so it is at most W. -/
theorem low_weight_cycles_bound_flux_weight
    (W : ℕ) (hlw : LowWeightCycleBasis G cycles W) (p : C) :
    (fluxChecks G cycles p).weight ≤ W := by
  rw [fluxChecks_weight]
  exact hlw p

/-- All flux checks are uniformly bounded when the cycle basis is low-weight. -/
theorem all_flux_checks_bounded
    (W : ℕ) (hlw : LowWeightCycleBasis G cycles W) :
    ∀ p : C, (fluxChecks G cycles p).weight ≤ W :=
  fun p => low_weight_cycles_bound_flux_weight G cycles W hlw p

end CycleBasis

/-! ## Constant Degree and Edge Overhead

A constant-degree graph has edge count linear in vertex count, giving
constant overhead per qubit in the support of L. -/

section ConstantOverhead

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- A constant-degree graph has maximum degree at most Δ. -/
def ConstantDegree (Δ : ℕ) : Prop :=
  ∀ v : V, G.degree v ≤ Δ

/-- Constant degree bounds edge count via the handshaking lemma:
2|E| = Σ_v deg(v) ≤ Δ · |V|. -/
theorem constant_degree_bounds_edges
    (Δ : ℕ) (hΔ : ConstantDegree G Δ) :
    2 * Fintype.card G.edgeSet ≤ Δ * Fintype.card V := by
  have hbd : ∑ v : V, G.degree v ≤ Δ * Fintype.card V := by
    calc ∑ v : V, G.degree v
        ≤ ∑ _v : V, Δ := Finset.sum_le_sum (fun v _ => hΔ v)
      _ = Δ * Fintype.card V := by
          simp [Finset.sum_const, Finset.card_univ, _root_.mul_comm]
  have hsum : ∑ v : V, G.degree v = 2 * Fintype.card G.edgeSet := by
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [SimpleGraph.edgeFinset, Set.toFinset_card] at h
    have : G.fintypeEdgeSet = ‹_› := Subsingleton.elim _ _
    rw [this] at h; exact h
  omega

/-- Constant overhead per vertex: the ratio |E|/|V| ≤ Δ/2. -/
theorem edge_overhead_per_vertex
    (Δ : ℕ) (hΔ : ConstantDegree G Δ) (hV : 0 < Fintype.card V) :
    (Fintype.card G.edgeSet : ℝ) / Fintype.card V ≤ Δ / 2 := by
  have h2 := constant_degree_bounds_edges G Δ hΔ
  rw [div_le_div_iff₀ (by exact_mod_cast hV) (by norm_num : (0 : ℝ) < 2)]
  have := @Nat.cast_le ℝ _ _ _ |>.mpr h2
  push_cast at this ⊢
  linarith

/-- The total qubit count of the deformed code is |V| + |E|, which is at most
|V| · (1 + Δ/2). We state a clean integer bound:
2·(|V| + |E|) ≤ (2 + Δ)·|V|. -/
theorem total_qubits_bounded
    (Δ : ℕ) (hΔ : ConstantDegree G Δ) :
    2 * (Fintype.card V + Fintype.card G.edgeSet) ≤ (2 + Δ) * Fintype.card V := by
  have := constant_degree_bounds_edges G Δ hΔ
  nlinarith

end ConstantOverhead

/-! ## Gauss Check Weight Characterization

The weight of the Gauss check A_v on V ⊕ E equals 1 + |incident edges|.
The support of A_v consists of vertex v (contributing 1) and all incident edges. -/

section GaussCheckWeight

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

lemma gaussLawOp_xVec_inl (v w : V) :
    (gaussLawOp G v).xVec (Sum.inl w) = if w = v then 1 else 0 := by
  simp [gaussLawOp]

lemma gaussLawOp_xVec_inr (v : V) (e : G.edgeSet) :
    (gaussLawOp G v).xVec (Sum.inr e) = if v ∈ (e : Sym2 V) then 1 else 0 := by
  simp [gaussLawOp]

/-- A_v acts nontrivially at vertex w iff w = v. -/
lemma gaussLaw_support_inl (v w : V) :
    (Sum.inl w : V ⊕ G.edgeSet) ∈ (gaussLawOp G v).support ↔ w = v := by
  simp only [PauliOp.mem_support, gaussLawOp_xVec_inl, gaussLawOp_zVec, Pi.zero_apply]
  constructor
  · intro h
    cases h with
    | inl h =>
      by_contra hne
      simp [hne] at h
    | inr h => exact absurd rfl h
  · intro h
    left
    simp [h]

/-- A_v acts nontrivially at edge e iff v ∈ e. -/
lemma gaussLaw_support_inr (v : V) (e : G.edgeSet) :
    (Sum.inr e : V ⊕ G.edgeSet) ∈ (gaussLawOp G v).support ↔ v ∈ (e : Sym2 V) := by
  simp only [PauliOp.mem_support, gaussLawOp_xVec_inr, gaussLawOp_zVec, Pi.zero_apply]
  constructor
  · intro h
    cases h with
    | inl h =>
      by_contra hne
      simp [hne] at h
    | inr h => exact absurd rfl h
  · intro h
    left
    simp [h]

/-- The support of A_v is {Sum.inl v} ∪ {Sum.inr e | v ∈ e}. -/
theorem gaussLaw_support_eq (v : V) :
    (gaussLawOp G v).support =
    {Sum.inl v} ∪ (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).map
      ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext q
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_map,
    Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  cases q with
  | inl w =>
    simp only [Sum.inl.injEq]
    constructor
    · intro h; left; exact (gaussLaw_support_inl G v w).mp h
    · intro h
      cases h with
      | inl h => exact (gaussLaw_support_inl G v w).mpr h
      | inr h => obtain ⟨_, _, h⟩ := h; exact absurd h (by simp)
  | inr e =>
    constructor
    · intro h
      right
      exact ⟨e, (gaussLaw_support_inr G v e).mp h, rfl⟩
    · intro h
      cases h with
      | inl h => exact absurd h (by simp)
      | inr h =>
        obtain ⟨e', he', heq⟩ := h
        have : e = e' := Sum.inr_injective heq.symm
        subst this
        exact (gaussLaw_support_inr G v e).mpr he'

/-- The weight of A_v equals 1 + |incident edges of v|. -/
theorem gaussLaw_weight_eq (v : V) :
    (gaussLawOp G v).weight =
    1 + (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).card := by
  unfold PauliOp.weight
  rw [gaussLaw_support_eq]
  rw [Finset.card_union_of_disjoint]
  · simp [Finset.card_map]
  · rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, not_exists]
    intro _ ⟨_, h⟩
    exact absurd h (by simp)

/-- The incident edges count equals the incidentEdges cardinality. -/
theorem incident_edges_eq (v : V) :
    (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).card =
    (incidentEdges G v).card := by
  congr 1

/-- The weight of A_v equals 1 + |incidentEdges|. -/
theorem gaussLaw_weight_eq_incident (v : V) :
    (gaussLawOp G v).weight = 1 + (incidentEdges G v).card := by
  rw [gaussLaw_weight_eq, incident_edges_eq]

/-- The incident edge count equals the graph degree. -/
theorem incidentEdges_card_eq_degree (v : V) :
    (incidentEdges G v).card = G.degree v := by
  rw [show G.degree v = (G.incidenceFinset v).card
    from (G.card_incidenceFinset_eq_degree v).symm]
  -- incidentEdges G v : Finset G.edgeSet, incidenceFinset : Finset (Sym2 V)
  -- Show their images under Subtype.val agree, then use injectivity
  have h_image : (incidentEdges G v).image Subtype.val = G.incidenceFinset v := by
    ext e
    simp only [Finset.mem_image, SimpleGraph.incidenceFinset, SimpleGraph.incidenceSet,
      Set.mem_toFinset, Set.mem_sep_iff]
    constructor
    · rintro ⟨⟨e', he'⟩, hm, rfl⟩
      simp only [mem_incidentEdges] at hm
      exact ⟨he', hm⟩
    · rintro ⟨he, hv⟩
      exact ⟨⟨e, he⟩, by simp [mem_incidentEdges, hv], rfl⟩
  rw [← h_image]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

/-- On a constant-degree graph, A_v has weight at most 1 + Δ. -/
theorem gaussLaw_weight_le
    (v : V) (Δ : ℕ) (hΔ : ConstantDegree G Δ) :
    (gaussLawOp G v).weight ≤ 1 + Δ := by
  rw [gaussLaw_weight_eq_incident, incidentEdges_card_eq_degree]
  linarith [hΔ v]

end GaussCheckWeight

/-! ## All Desiderata Satisfied

When all three conditions hold with constants independent of n, the deformed code
has bounded check weight and bounded qubit degree (LDPC property preserved),
with no distance reduction. -/

section AllDesiderata

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-- All three desiderata satisfied with given constants. -/
structure AllDesiderataSatisfied (D W : ℕ) : Prop where
  short_paths : ShortPathsForDeformation G checks D
  expansion : SufficientExpansion G
  low_weight_cycles : LowWeightCycleBasis G cycles W

/-- When all desiderata are satisfied, the flux checks have bounded weight. -/
theorem desiderata_imply_bounded_flux_weight
    (D W : ℕ) (hall : AllDesiderataSatisfied G cycles checks D W) (p : C) :
    (fluxChecks G cycles p).weight ≤ W :=
  low_weight_cycles_bound_flux_weight G cycles W hall.low_weight_cycles p

/-- When all desiderata are satisfied, the graph is an expander. -/
theorem desiderata_imply_expander
    (D W : ℕ) (hall : AllDesiderataSatisfied G cycles checks D W) :
    QEC1.SimpleGraph.IsExpander G 1 :=
  sufficient_expansion_implies_expander G hall.expansion

/-- When all desiderata are satisfied, every valid vertex subset has boundary
at least as large as itself — preventing distance loss. -/
theorem desiderata_imply_no_distance_loss
    (D W : ℕ) (hall : AllDesiderataSatisfied G cycles checks D W)
    (S : Finset V) (hne : S.Nonempty) (hsize : 2 * S.card ≤ Fintype.card V) :
    (S.card : ℝ) ≤ (QEC1.SimpleGraph.edgeBoundary G S).card :=
  expansion_gives_boundary_bound G hall.expansion S hne hsize

end AllDesiderata

/-! ## LDPC Preservation Characterization

The deformed code has three families of checks:
- Gauss checks A_v: weight = 1 + deg(v) (bounded by 1 + Δ on a degree-Δ graph)
- Flux checks B_p: weight = |cycle p| (bounded by W)
- Deformed checks s̃_j: vertex weight from original + edge weight from path γ_j
All are bounded when the desiderata hold with constant bounds. -/

section LDPCPreservation

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-- The LDPC property of the deformed code, using the existing IsQLDPC predicate. -/
def DeformedCodeIsLDPC
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (w_bound c_bound : ℕ) : Prop :=
  IsQLDPC (deformedStabilizerCode G cycles checks data hcyc hcomm) w_bound c_bound

/-- Gauss check weights are bounded on constant-degree graphs. -/
theorem gaussLaw_checks_weight_bounded
    (Δ : ℕ) (hΔ : ConstantDegree G Δ) (v : V) :
    (gaussLawChecks G v).weight ≤ 1 + Δ :=
  gaussLaw_weight_le G v Δ hΔ

/-- Flux check weights are bounded by the cycle basis weight bound. -/
theorem flux_checks_weight_bounded
    (W : ℕ) (hlw : LowWeightCycleBasis G cycles W) (p : C) :
    (fluxChecks G cycles p).weight ≤ W :=
  low_weight_cycles_bound_flux_weight G cycles W hlw p

end LDPCPreservation

/-! ## Summary: All Three Conditions Together

The three desiderata together ensure the deformed code is a good qLDPC code:
1. Flux checks have bounded weight (from low-weight cycle basis)
2. G is an expander with h(G) ≥ 1 (from sufficient expansion) — no distance loss
3. Edge overhead is linear in |V| (from constant degree) — constant overhead per qubit
4. Short paths ensure deformed checks have bounded weight -/

section Summary

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-- Summary theorem: when all three desiderata and constant degree are satisfied,
the key consequences hold simultaneously. -/
theorem desiderata_consequences
    (D W Δ : ℕ)
    (_hsp : ShortPathsForDeformation G checks D)
    (hexp : SufficientExpansion G)
    (hlw : LowWeightCycleBasis G cycles W)
    (hΔ : ConstantDegree G Δ) :
    -- (1) Flux checks bounded by W
    (∀ p : C, (fluxChecks G cycles p).weight ≤ W) ∧
    -- (2) G is a 1-expander
    QEC1.SimpleGraph.IsExpander G 1 ∧
    -- (3) Edge overhead is linear: 2|E| ≤ Δ|V|
    2 * Fintype.card G.edgeSet ≤ Δ * Fintype.card V ∧
    -- (4) Gauss checks bounded by 1 + Δ
    (∀ v : V, (gaussLawChecks G v).weight ≤ 1 + Δ) := by
  exact ⟨fun p => low_weight_cycles_bound_flux_weight G cycles W hlw p,
         sufficient_expansion_implies_expander G hexp,
         constant_degree_bounds_edges G Δ hΔ,
         fun v => gaussLaw_weight_le G v Δ hΔ⟩

/-- The additional qubit overhead (edge count) per vertex of L is bounded. -/
theorem overhead_per_vertex_bounded
    (D W Δ : ℕ)
    (_hsp : ShortPathsForDeformation G checks D)
    (_hexp : SufficientExpansion G)
    (_hlw : LowWeightCycleBasis G cycles W)
    (hΔ : ConstantDegree G Δ) (hV : 0 < Fintype.card V) :
    (Fintype.card G.edgeSet : ℝ) / Fintype.card V ≤ Δ / 2 :=
  edge_overhead_per_vertex G Δ hΔ hV

end Summary

end DesiderataForGraphG
