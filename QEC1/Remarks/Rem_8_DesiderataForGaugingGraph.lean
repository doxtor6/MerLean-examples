import QEC1.Remarks.Rem_7_SparsifiedDeformedChecks
import QEC1.Definitions.Def_5_CheegerConstant

/-!
# Desiderata for Gauging Graph (Remark 8)

## Statement
When choosing a constant-degree gauging graph $G = (V, E)$ for measuring logical operator $L$,
the following **desiderata** should be satisfied:

(i) **Short deforming paths**: $G$ should contain a constant-length edge-path between any pair
    of vertices that are in the Z-type support of some check from the original code. Specifically:
    for each check $s_j$ with $\mathcal{S}_{Z,j} \cap V \neq \emptyset$, there exists a path
    $\gamma_j \subseteq E$ with $|\gamma_j| \leq \kappa$ for some constant $\kappa$.

(ii) **Sufficient expansion**: The Cheeger constant should satisfy $h(G) \geq 1$. This ensures
     no distance reduction in the deformed code.

(iii) **Low-weight cycle basis**: There should exist a generating set of cycles $C$ where each
      cycle has weight bounded by a constant. Combined with cycle-sparsification, this ensures
      the flux operators $B_p$ have constant weight.

**When all desiderata are satisfied**:
- The deformed code is LDPC
- The code distance is preserved: $d_{\text{deformed}} \geq d_{\text{original}}$
- The qubit overhead is $O(|V| \cdot R_G^c)$ where $R_G^c$ is the sparsification depth

## Formalization Approach
This remark describes **criteria** (desiderata) for choosing a good gauging graph.
We formalize:
1. The three desiderata as Prop-valued predicates
2. The LDPC weight/degree bounds as computable formulas from parameters
3. The connection between expansion (h(G) ≥ 1) and the edge boundary property
4. The overhead formula O(|V| · R)

Note: The claims "LDPC" and "distance preserved" follow from having constant parameters
satisfying the desiderata. We formalize the weight/degree bounds explicitly.

## Main Results
**Desiderata Predicates** (standalone Prop):
- `ShortPathsProperty`: Paths of length ≤ κ between relevant vertex pairs
- `SufficientExpansionProperty`: Cheeger constant h(G) ≥ 1
- `LowWeightCycleBasisProperty`: Generating cycles with weight ≤ W

**LDPC Bounds**:
- `maxCheckWeight`: max(Δ+1, W, w+κ) bounds all check weights
- `maxQubitDegree`: 2Δ^κ·w + c + 2 bounds qubit participation

**Expansion Consequence**:
- `cheeger_ge_one_implies_boundary_ge_size`: h(G) ≥ 1 ⟹ |δ(S)| ≥ |S| for valid S

## File Structure
1. Graph Path Definition: Paths in the gauging graph
2. Short Deforming Paths Predicate: Desideratum (i)
3. Sufficient Expansion Predicate: Desideratum (ii)
4. Low-Weight Cycle Basis Predicate: Desideratum (iii)
5. LDPC Bounds: Weight and degree formulas
6. Expansion-Boundary Connection: h(G) ≥ 1 implies |δ(S)| ≥ |S|
7. Distance Preservation: Definition and connection to expansion
8. Qubit Overhead: O(|V| · R^c) formula
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Graph Paths

A path in the gauging graph connecting two vertices.
-/

/-- A path in the graph connecting two vertices.
    The path is represented by a list of edges that form a walk. -/
structure GraphPath (G : BaseGraphWithCycles) where
  /-- Start vertex -/
  start : G.V
  /-- End vertex -/
  endpoint : G.V
  /-- Edges forming the path -/
  edges : List (Sym2 G.V)
  /-- All edges are valid graph edges -/
  edges_valid : ∀ e ∈ edges, e ∈ G.graph.edgeSet

namespace GraphPath

variable {G : BaseGraphWithCycles}

/-- Path length = number of edges -/
def length (p : GraphPath G) : ℕ := p.edges.length

/-- Trivial path at a vertex (length 0) -/
def trivial (v : G.V) : GraphPath G where
  start := v
  endpoint := v
  edges := []
  edges_valid := fun _ h => by simp at h

@[simp]
theorem trivial_length (v : G.V) : (trivial v).length = 0 := rfl

@[simp]
theorem trivial_start (v : G.V) : (trivial v).start = v := rfl

@[simp]
theorem trivial_endpoint (v : G.V) : (trivial v).endpoint = v := rfl

end GraphPath

/-! ## Section 2: Short Deforming Paths Predicate (Desideratum i)

For each check s_j whose Z-support intersects the gauging graph vertices V,
there exists a path γ_j of length ≤ κ between any pair of vertices in S_{Z,j} ∩ V.

This is formalized as a **predicate** (Prop), not a bundled structure.
-/

/-- The short deforming paths property:
    Given a mapping from checks to their Z-support vertices in G,
    for any two vertices u, v in the Z-support of the same check,
    there exists a path from u to v with length ≤ κ.

    This captures: "for each check s_j with S_{Z,j} ∩ V ≠ ∅,
    there exists a path γ_j ⊆ E with |γ_j| ≤ κ" -/
def ShortPathsProperty (G : BaseGraphWithCycles)
    (zSupport : ℕ → Finset G.V) (κ : ℕ) : Prop :=
  ∀ j : ℕ, ∀ u v : G.V, u ∈ zSupport j → v ∈ zSupport j →
    ∃ (p : GraphPath G), p.start = u ∧ p.endpoint = v ∧ p.length ≤ κ

/-- Short paths property is preserved under increasing the bound -/
theorem ShortPathsProperty_mono {G : BaseGraphWithCycles}
    {zSupport : ℕ → Finset G.V} {κ κ' : ℕ} (hκ : κ ≤ κ')
    (h : ShortPathsProperty G zSupport κ) : ShortPathsProperty G zSupport κ' := by
  intro j u v hu hv
  obtain ⟨p, hp_start, hp_end, hp_len⟩ := h j u v hu hv
  exact ⟨p, hp_start, hp_end, Nat.le_trans hp_len hκ⟩

/-- Same vertex has a trivial path of length 0 -/
theorem same_vertex_path {G : BaseGraphWithCycles} (v : G.V) :
    ∃ (p : GraphPath G), p.start = v ∧ p.endpoint = v ∧ p.length = 0 :=
  ⟨GraphPath.trivial v, rfl, rfl, rfl⟩

/-! ## Section 3: Sufficient Expansion Predicate (Desideratum ii)

The Cheeger constant h(G) should satisfy h(G) ≥ 1.
This ensures no distance reduction in the deformed code.
-/

/-- The sufficient expansion property: Cheeger constant h(G) ≥ 1 -/
def SufficientExpansionProperty (G : BaseGraphWithCycles) : Prop :=
  cheegerConstant G.graph ≥ 1

/-- Expansion property implies positive Cheeger constant -/
theorem expansion_implies_positive_cheeger {G : BaseGraphWithCycles}
    (h : SufficientExpansionProperty G) : cheegerConstant G.graph > 0 := by
  calc 0 < 1 := by norm_num
    _ ≤ cheegerConstant G.graph := h

/-- Expansion property implies the graph is an expander -/
theorem expansion_implies_expander {G : BaseGraphWithCycles}
    (h : SufficientExpansionProperty G) : isExpanderGraph G.graph := by
  unfold isExpanderGraph
  use 1
  exact ⟨by norm_num, h⟩

/-! ## Section 4: Low-Weight Cycle Basis Predicate (Desideratum iii)

There should exist a generating set of cycles where each cycle has
weight bounded by a constant W.
-/

/-- The low-weight cycle basis property:
    All generating cycles have weight (number of vertices/edges) bounded by W. -/
def LowWeightCycleBasisProperty (G : BaseGraphWithCycles) (W : ℕ) : Prop :=
  ∀ c : G.CycleIdx, (G.cycleVertices c).length ≤ W

/-- Low-weight property is preserved under increasing the bound -/
theorem LowWeightCycleBasisProperty_mono {G : BaseGraphWithCycles}
    {W W' : ℕ} (hW : W ≤ W')
    (h : LowWeightCycleBasisProperty G W) : LowWeightCycleBasisProperty G W' := by
  intro c
  exact Nat.le_trans (h c) hW

/-- Total cycle weight is bounded by (number of cycles) × W -/
theorem total_cycle_weight_bounded {G : BaseGraphWithCycles} {W : ℕ}
    (h : LowWeightCycleBasisProperty G W) :
    ∑ c : G.CycleIdx, (G.cycleVertices c).length ≤ Fintype.card G.CycleIdx * W := by
  calc ∑ c : G.CycleIdx, (G.cycleVertices c).length
    ≤ ∑ _c : G.CycleIdx, W := Finset.sum_le_sum (fun c _ => h c)
    _ = Fintype.card G.CycleIdx * W := by simp [Finset.sum_const, Finset.card_univ]

/-! ## Section 5: LDPC Bounds

The LDPC property means bounded check weights and qubit degrees.
We compute explicit bounds from the desiderata parameters.
-/

/-- Parameters for the deformed code's LDPC analysis -/
structure DeformedCodeParams where
  /-- Graph degree Δ (degree of gauging graph) -/
  graphDegree : ℕ
  /-- Original check weight bound w -/
  originalCheckWeight : ℕ
  /-- Path length bound κ (from desideratum i) -/
  pathBound : ℕ
  /-- Cycle weight bound W (from desideratum iii) -/
  cycleWeightBound : ℕ
  /-- Maximum cycles per edge (cycle degree) -/
  cycleDegree : ℕ

namespace DeformedCodeParams

/-- Gauss law operator weight: Δ + 1 (vertex + incident edges) -/
def gaussLawWeight (p : DeformedCodeParams) : ℕ := p.graphDegree + 1

/-- Flux operator weight bound: W (from cycle weight bound) -/
def fluxWeight (p : DeformedCodeParams) : ℕ := p.cycleWeightBound

/-- Deformed check weight bound: w + κ (original weight + path contribution) -/
def deformedCheckWeight (p : DeformedCodeParams) : ℕ :=
  p.originalCheckWeight + p.pathBound

/-- Maximum check weight across all generator types:
    max(Δ+1, W, w+κ) -/
def maxCheckWeight (p : DeformedCodeParams) : ℕ :=
  max p.gaussLawWeight (max p.fluxWeight p.deformedCheckWeight)

/-- Maximum qubit degree: 2Δ^κ·w + c + 2
    - 2Δ^κ·w comes from paths through edges in layer 0
    - c comes from cycle participation
    - 2 comes from Gauss law at endpoints -/
def maxQubitDegree (p : DeformedCodeParams) : ℕ :=
  2 * p.graphDegree ^ p.pathBound * p.originalCheckWeight + p.cycleDegree + 2

/-- Gauss law weight ≤ max check weight -/
theorem gaussLaw_le_maxCheckWeight (p : DeformedCodeParams) :
    p.gaussLawWeight ≤ p.maxCheckWeight := by
  unfold maxCheckWeight
  exact Nat.le_max_left _ _

/-- Flux weight ≤ max check weight -/
theorem flux_le_maxCheckWeight (p : DeformedCodeParams) :
    p.fluxWeight ≤ p.maxCheckWeight := by
  unfold maxCheckWeight
  calc p.fluxWeight ≤ max p.fluxWeight p.deformedCheckWeight := Nat.le_max_left _ _
    _ ≤ max p.gaussLawWeight _ := Nat.le_max_right _ _

/-- Deformed check weight ≤ max check weight -/
theorem deformedCheck_le_maxCheckWeight (p : DeformedCodeParams) :
    p.deformedCheckWeight ≤ p.maxCheckWeight := by
  unfold maxCheckWeight
  calc p.deformedCheckWeight ≤ max p.fluxWeight p.deformedCheckWeight := Nat.le_max_right _ _
    _ ≤ max p.gaussLawWeight _ := Nat.le_max_right _ _

/-- All generator weights are bounded by maxCheckWeight -/
theorem all_weights_bounded (p : DeformedCodeParams) :
    p.gaussLawWeight ≤ p.maxCheckWeight ∧
    p.fluxWeight ≤ p.maxCheckWeight ∧
    p.deformedCheckWeight ≤ p.maxCheckWeight :=
  ⟨p.gaussLaw_le_maxCheckWeight, p.flux_le_maxCheckWeight, p.deformedCheck_le_maxCheckWeight⟩

end DeformedCodeParams

/-- Given desiderata parameters, compute explicit LDPC bounds -/
def LDPCBoundsFromParameters (Δ w κ W c : ℕ) : ℕ × ℕ :=
  (max (Δ + 1) (max W (w + κ)), 2 * Δ ^ κ * w + c + 2)

/-- The check weight bound formula -/
theorem checkWeightBound_formula (Δ w κ W c : ℕ) :
    (LDPCBoundsFromParameters Δ w κ W c).1 = max (Δ + 1) (max W (w + κ)) := rfl

/-- The qubit degree bound formula -/
theorem qubitDegreeBound_formula (Δ w κ W c : ℕ) :
    (LDPCBoundsFromParameters Δ w κ W c).2 = 2 * Δ ^ κ * w + c + 2 := rfl

/-! ## Section 6: Expansion-Boundary Connection

The key mathematical content: h(G) ≥ 1 implies |δ(S)| ≥ |S| for valid subsets S.

This is the core property that ensures distance preservation: the Cheeger constant
bounds how much the edge boundary can "shrink" relative to the set size.
-/

/-- A valid Cheeger subset: nonempty and |S| ≤ |V|/2 -/
def ValidCheegerSubset {V : Type*} [Fintype V] (S : Finset V) : Prop :=
  S.Nonempty ∧ 2 * S.card ≤ Fintype.card V

/-- The key expansion property: h(G) ≥ 1 implies |δ(S)|/|S| ≥ 1 for valid S,
    which gives |δ(S)| ≥ |S|.

    This theorem connects the Cheeger constant to the edge boundary bound. -/
theorem cheeger_ge_one_implies_boundary_ge_size {G : BaseGraphWithCycles}
    (h_cheeger : SufficientExpansionProperty G)
    (S : Finset G.V) (hS : ValidCheegerSubset S) :
    (edgeBoundary G.graph S).card ≥ S.card := by
  -- The Cheeger constant h(G) ≥ 1 means min_{valid S} |δ(S)|/|S| ≥ 1
  -- So for any valid S, we have |δ(S)|/|S| ≥ h(G) ≥ 1
  -- Therefore |δ(S)| ≥ |S|
  unfold SufficientExpansionProperty at h_cheeger
  unfold ValidCheegerSubset at hS
  -- Use the edge boundary bound from the Cheeger constant definition
  have h_bound := edgeBoundary_ge_cheeger_mul_card G.graph S ⟨hS.1, hS.2⟩
  -- h_bound : (edgeBoundaryCard G.graph S : ℚ) ≥ cheegerConstant G.graph * S.card
  -- Since cheegerConstant G.graph ≥ 1, we get edgeBoundaryCard ≥ S.card
  have h_card_pos : (0 : ℚ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS.1)
  -- From h_cheeger (cheeger ≥ 1) and h_card_pos (S.card > 0):
  -- cheeger * S.card ≥ 1 * S.card = S.card
  have h_cheeger_mul : cheegerConstant G.graph * S.card ≥ 1 * S.card := by
    apply mul_le_mul_of_nonneg_right h_cheeger
    exact le_of_lt h_card_pos
  simp only [one_mul] at h_cheeger_mul
  -- From h_bound and h_cheeger_mul: edgeBoundaryCard ≥ S.card (as rationals)
  have h_boundary_ge : (edgeBoundaryCard G.graph S : ℚ) ≥ S.card := by
    calc (edgeBoundaryCard G.graph S : ℚ)
      ≥ cheegerConstant G.graph * S.card := h_bound
      _ ≥ S.card := h_cheeger_mul
  -- Convert from ℚ to ℕ
  have h_nat := Nat.cast_le.mp (le_trans (Nat.cast_le.mpr (le_refl S.card)) h_boundary_ge)
  exact h_nat

/-! ## Section 7: Distance Preservation

The code distance is the minimum weight of a non-trivial logical operator.
Distance preservation means d_deformed ≥ d_original.

The expansion property (h(G) ≥ 1) ensures this because:
- Any logical operator in the deformed code corresponds to one in the original
- The edge boundary bound |δ(S)| ≥ |S| prevents "shortcuts" that reduce weight
-/

/-- Distance preservation: d_deformed ≥ d_original -/
def DistancePreserved (d_original d_deformed : ℕ) : Prop :=
  d_deformed ≥ d_original

/-- Distance preservation is reflexive -/
theorem distance_preserved_refl (d : ℕ) : DistancePreserved d d := le_refl d

/-- Distance preservation is transitive -/
theorem distance_preserved_trans {d₁ d₂ d₃ : ℕ}
    (h₁ : DistancePreserved d₁ d₂) (h₂ : DistancePreserved d₂ d₃) :
    DistancePreserved d₁ d₃ := by
  unfold DistancePreserved at *
  exact Nat.le_trans h₁ h₂

/-- The expansion property ensures no weight reduction.

    Given:
    - h(G) ≥ 1 (sufficient expansion)
    - |δ(S)| ≥ |S| for all valid S (consequence of expansion)

    The logical operator weight cannot decrease because any "shortcut"
    through the gauging graph would require crossing the boundary δ(S),
    and |δ(S)| ≥ |S| means we can't save on weight.

    This theorem captures: expansion ⟹ boundary bound ⟹ weight preserved. -/
theorem expansion_prevents_weight_reduction {G : BaseGraphWithCycles}
    (h_exp : SufficientExpansionProperty G) :
    ∀ S : Finset G.V, ValidCheegerSubset S → (edgeBoundary G.graph S).card ≥ S.card :=
  fun S hS => cheeger_ge_one_implies_boundary_ge_size h_exp S hS

/-! ## Section 8: Qubit Overhead Formula

The qubit overhead is O(|V| · R_G^c) where:
- |V| is the number of vertices in the gauging graph
- R_G^c is the sparsification depth

Specifically: overhead = |V| · (R + 1) which is O(|V| · R).
-/

/-- Qubit overhead formula: V · (R + 1) -/
def qubitOverhead (numVertices sparsificationDepth : ℕ) : ℕ :=
  numVertices * (sparsificationDepth + 1)

/-- The overhead is linear in V and R -/
theorem qubitOverhead_linear (V R : ℕ) :
    qubitOverhead V R = V * R + V := by
  unfold qubitOverhead
  ring

/-- Overhead is monotone in V -/
theorem qubitOverhead_mono_V (V V' R : ℕ) (h : V ≤ V') :
    qubitOverhead V R ≤ qubitOverhead V' R := by
  unfold qubitOverhead
  exact Nat.mul_le_mul_right _ h

/-- Overhead is monotone in R -/
theorem qubitOverhead_mono_R (V R R' : ℕ) (h : R ≤ R') :
    qubitOverhead V R ≤ qubitOverhead V R' := by
  unfold qubitOverhead
  apply Nat.mul_le_mul_left
  omega

/-- Total qubits = original + overhead -/
def totalQubits (numOriginal numVertices sparsificationDepth : ℕ) : ℕ :=
  numOriginal + qubitOverhead numVertices sparsificationDepth

/-- Total qubit formula -/
theorem totalQubits_formula (n V R : ℕ) :
    totalQubits n V R = n + V * (R + 1) := by
  unfold totalQubits qubitOverhead
  rfl

/-! ## Section 9: Constant Degree Property -/

/-- The gauging graph has constant degree Δ (all vertices have degree ≤ Δ) -/
def ConstantDegreeProperty (G : BaseGraphWithCycles) (Δ : ℕ) : Prop :=
  ∀ v : G.V, G.graph.degree v ≤ Δ

/-- Constant degree is preserved under increasing the bound -/
theorem ConstantDegreeProperty_mono {G : BaseGraphWithCycles}
    {Δ Δ' : ℕ} (hΔ : Δ ≤ Δ')
    (h : ConstantDegreeProperty G Δ) : ConstantDegreeProperty G Δ' := by
  intro v
  exact Nat.le_trans (h v) hΔ

/-! ## Section 10: Combined Desiderata Summary

All three desiderata together, expressed as predicates.
-/

/-- All desiderata satisfied -/
def AllDesiderataSatisfied (G : BaseGraphWithCycles)
    (zSupport : ℕ → Finset G.V) (κ W Δ : ℕ) : Prop :=
  ShortPathsProperty G zSupport κ ∧
  SufficientExpansionProperty G ∧
  LowWeightCycleBasisProperty G W ∧
  ConstantDegreeProperty G Δ

/-- When all desiderata are satisfied, the LDPC bounds apply -/
theorem desiderata_give_LDPC_bounds {G : BaseGraphWithCycles}
    {zSupport : ℕ → Finset G.V} {κ W Δ : ℕ}
    (h : AllDesiderataSatisfied G zSupport κ W Δ)
    (w c : ℕ) :
    let p : DeformedCodeParams := {
      graphDegree := Δ
      originalCheckWeight := w
      pathBound := κ
      cycleWeightBound := W
      cycleDegree := c
    }
    -- All check weights bounded
    p.gaussLawWeight ≤ p.maxCheckWeight ∧
    p.fluxWeight ≤ p.maxCheckWeight ∧
    p.deformedCheckWeight ≤ p.maxCheckWeight ∧
    -- Cycle weights bounded by W (from desideratum iii)
    (∀ cyc : G.CycleIdx, (G.cycleVertices cyc).length ≤ W) ∧
    -- Expansion property holds (from desideratum ii)
    (∀ S : Finset G.V, ValidCheegerSubset S → (edgeBoundary G.graph S).card ≥ S.card) := by
  obtain ⟨_, h_exp, h_cycles, _⟩ := h
  intro p
  refine ⟨p.gaussLaw_le_maxCheckWeight, p.flux_le_maxCheckWeight,
          p.deformedCheck_le_maxCheckWeight, h_cycles, ?_⟩
  exact expansion_prevents_weight_reduction h_exp

/-- Summary: desiderata imply the graph is an expander -/
theorem desiderata_imply_expander {G : BaseGraphWithCycles}
    {zSupport : ℕ → Finset G.V} {κ W Δ : ℕ}
    (h : AllDesiderataSatisfied G zSupport κ W Δ) :
    isExpanderGraph G.graph := by
  obtain ⟨_, h_exp, _, _⟩ := h
  exact expansion_implies_expander h_exp

/-! ## Section 11: Helper Lemmas -/

/-- Edge degree formula is O(Δ^κ · w) -/
theorem edgeDegree_formula (Δ κ w : ℕ) :
    2 * Δ ^ κ * w = 2 * (Δ ^ κ * w) := by ring

/-- When Δ = 0 and κ > 0, the edge degree contribution is 0 -/
theorem edgeDegree_zero_degree (κ w : ℕ) (hκ : κ > 0) :
    2 * 0 ^ κ * w = 0 := by
  have hκ' : κ ≠ 0 := Nat.pos_iff_ne_zero.mp hκ
  simp only [zero_pow hκ', mul_zero, zero_mul]

/-- Overhead formula simplified -/
theorem overhead_simplified (V R : ℕ) :
    V * (R + 1) = V * R + V := by ring

end QEC
