import QEC1.Theorems.Thm_1_GaugingMeasurement
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option linter.style.emptyLine false

/-!
# Algorithm Correctness (Remark 24)

## Statement
Algorithm 1 (Gauging measurement procedure) produces the correct post-measurement state up to
a byproduct operator $X_V(c')$.

**Byproduct determination**: The byproduct $c' \in C_0(G; \mathbb{Z}_2)$ is determined by the
$Z_e$ measurement outcomes $\{\omega_e\}$:
$$c' = \text{any 0-chain satisfying } \delta_0(c') = z$$
where $z_e = \frac{1 - \omega_e}{2} \in \{0, 1\}$ encodes the measurement outcome.

**Constructive determination**: Given a spanning tree $T$ of $G$ rooted at $v_0$:
- For each vertex $v \neq v_0$, let $\gamma_v$ be the unique path in $T$ from $v_0$ to $v$
- Set $c'_v = \bigoplus_{e \in \gamma_v} z_e$ (parity of outcomes along path)
- Set $c'_{v_0} = 0$

This gives $\delta_0(c') = z$ because tree paths have the required boundary property.

## Formalization Approach

This remark describes how the byproduct operator is determined from measurement outcomes.
The key insight is that:

1. The edge outcomes z determine a 1-chain
2. We need to find a 0-chain c' with δ₀(c') = z
3. A spanning tree provides a constructive way to compute c'
4. **Key constraint**: z must be in the image of δ₀ (i.e., z sums to 0 on every cycle)
5. Under this constraint, the path parity construction gives δ₀(c') = z for ALL edges

We formalize:
1. **Outcome encoding**: The mapping ω_e ↦ z_e = (1 - ω_e)/2
2. **Byproduct equation**: The constraint δ₀(c') = z
3. **Spanning tree structure**: Unique paths from root to each vertex
4. **Flux constraint**: z must sum to 0 on every cycle (z ∈ im(δ₀))
5. **Main correctness**: Under flux constraint, path parity gives δ₀(c') = z on ALL edges

## Main Results
- `outcomeEncoding`: Maps measurement outcomes to ZMod 2 values
- `satisfiesByproductEquation`: The equation δ₀(c') = z
- `pathParityChain`: The byproduct chain computed via path parities
- `algorithm_correctness`: Main theorem: path parity satisfies δ₀(c') = z globally

## File Structure
1. Outcome Encoding: Measurement outcomes to ZMod 2
2. Byproduct Equation: The constraint δ₀(c') = z
3. Spanning Tree Structure: Trees with parent pointers
4. Path Parity Construction: Computing c' from paths
5. Flux Constraint: z must be in the image of δ₀
6. Main Correctness: δ₀(c') = z for ALL edges (not just tree edges)
7. Uniqueness: c' is unique up to adding 1_V
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Outcome Encoding

The measurement outcome ω_e ∈ {±1} is encoded as z_e ∈ {0, 1} via:
z_e = (1 - ω_e)/2

In our ZMod 2 representation:
- ω_e = 0 (meaning +1) maps to z_e = 0
- ω_e = 1 (meaning -1) maps to z_e = 1

So the encoding is actually the identity in ZMod 2!
-/

/-- Outcome encoding: In our representation, the encoding ω_e ↦ z_e is the identity.
    This is because we use ZMod 2 where 0 represents +1 and 1 represents -1.
    The formula z_e = (1 - ω_e)/2 with ω_e ∈ {+1, -1} gives:
    - ω_e = +1 (encoded as 0) → z_e = (1-1)/2 = 0
    - ω_e = -1 (encoded as 1) → z_e = (1-(-1))/2 = 1 -/
def outcomeEncoding (ω : ZMod 2) : ZMod 2 := ω

/-- The encoding is the identity -/
@[simp]
theorem outcomeEncoding_id (ω : ZMod 2) : outcomeEncoding ω = ω := rfl

/-- Encoding preserves addition -/
@[simp]
theorem outcomeEncoding_add (ω₁ ω₂ : ZMod 2) :
    outcomeEncoding (ω₁ + ω₂) = outcomeEncoding ω₁ + outcomeEncoding ω₂ := rfl

/-- Encoding of 0 is 0 -/
@[simp]
theorem outcomeEncoding_zero : outcomeEncoding 0 = 0 := rfl

/-- Encoding of 1 is 1 -/
@[simp]
theorem outcomeEncoding_one : outcomeEncoding 1 = 1 := rfl

/-! ## Section 2: Byproduct Equation

The byproduct chain c' satisfies the equation δ₀(c') = z, where:
- δ₀ is the coboundary map from 0-chains to 1-chains
- z is the 1-chain of encoded edge outcomes

For edge e = {v, w}: δ₀(c')(e) = c'(v) + c'(w) = z(e)
-/

/-- The byproduct equation: δ₀(c') = z -/
def satisfiesByproductEquation {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (c' : VertexChain M) (z : EdgeChain M) : Prop :=
  delta0 M c' = z

/-- Alternative characterization: pointwise equality -/
theorem satisfiesByproductEquation_iff {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (c' : VertexChain M) (z : EdgeChain M) :
    satisfiesByproductEquation M c' z ↔ ∀ e, delta0 M c' e = z e := by
  constructor
  · intro h e
    exact congrFun h e
  · intro h
    funext e
    exact h e

/-- For any 0-chain c, there exists a z such that δ₀(c) = z -/
theorem byproductEquation_image {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (c : VertexChain M) :
    satisfiesByproductEquation M c (delta0 M c) := rfl

/-! ## Section 3: Spanning Tree Structure

A spanning tree T of G rooted at v₀ provides:
- A unique path from v₀ to each vertex v
- Parent pointers: each non-root vertex has a parent
- These paths can be used to compute the byproduct chain
-/

/-- A spanning tree with parent pointers and depth function for termination.
    Each vertex (except root) has a parent closer to the root. -/
structure SpanningTree {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) where
  /-- Parent function: gives the parent of each vertex (root is its own parent) -/
  parent : M.Vertex → M.Vertex
  /-- Depth from root: root has depth 0, others have depth = parent depth + 1 -/
  depth : M.Vertex → ℕ
  /-- Edge to parent: for non-root v, this is the edge {v, parent v} -/
  edgeToParent : M.Vertex → Sym2 M.Vertex
  /-- Root has depth 0 -/
  root_depth : depth M.root = 0
  /-- Root is its own parent -/
  root_is_own_parent : parent M.root = M.root
  /-- Non-root vertices have positive depth -/
  nonroot_pos_depth : ∀ v, v ≠ M.root → 0 < depth v
  /-- Parent has smaller depth -/
  parent_depth_lt : ∀ v, v ≠ M.root → depth (parent v) < depth v
  /-- Edge to parent connects v and parent(v) -/
  edge_connects : ∀ v, edgeToParent v = s(v, parent v)
  /-- All edges to parent are graph edges (except for root) -/
  edge_in_graph : ∀ v, v ≠ M.root → edgeToParent v ∈ M.graph.graph.edgeSet

/-! ## Section 4: Path Parity Construction

Given edge outcomes z and a spanning tree, compute c' via:
c'_v = ⊕_{e ∈ γ_v} z_e (XOR of outcomes along path from root to v)
-/

/-- The byproduct chain computed from edge outcomes via parent paths.
    c'(v) = sum of z(e) over edges from root to v -/
noncomputable def pathParityChain {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    {M : MeasurementConfig C L} (T : SpanningTree M) (z : EdgeChain M) : VertexChain M :=
  fun v =>
    if _hv : v = M.root then 0
    else pathParityChain T z (T.parent v) + z (T.edgeToParent v)
termination_by v => T.depth v
decreasing_by exact T.parent_depth_lt _ ‹_›

/-! ## Section 5: Flux Constraint and Image of δ₀

For z to have a solution c' with δ₀(c') = z, z must be in the image of δ₀.
This is equivalent to: z sums to 0 on every cycle.
-/

/-- z is in the image of δ₀: there exists c with δ₀(c) = z -/
def inImageDelta0 {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (z : EdgeChain M) : Prop :=
  ∃ c : VertexChain M, delta0 M c = z

/-- If z = δ₀(c) for some c, then z is in the image -/
theorem delta0_in_image {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (c : VertexChain M) :
    inImageDelta0 M (delta0 M c) := ⟨c, rfl⟩

/-! ## Section 6: Main Correctness Theorem

The key insight: For a connected graph with spanning tree T:
- Every vertex is reachable from the root via a unique tree path
- For the path parity chain c', we have c'(v) + c'(parent v) = z(edgeToParent v) for all non-root v
- This inductively determines c' uniquely given c'(root) = 0
- If z is in the image of δ₀, then δ₀(c') = z on ALL edges (not just tree edges)

The proof that δ₀(c') = z on ALL edges requires the flux constraint: z must be in im(δ₀).
-/

/-- Path parity at root is 0 -/
theorem pathParity_root {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    {M : MeasurementConfig C L} (T : SpanningTree M) (z : EdgeChain M) :
    pathParityChain T z M.root = 0 := by
  unfold pathParityChain
  simp

/-- **Key Lemma**: Path parity satisfies the edge property on tree edges.
    For non-root v: c'(v) + c'(parent v) = z(edgeToParent v) -/
theorem pathParity_tree_edge {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    {M : MeasurementConfig C L} (T : SpanningTree M) (z : EdgeChain M)
    (v : M.Vertex) (hv : v ≠ M.root) :
    pathParityChain T z v + pathParityChain T z (T.parent v) =
    z (T.edgeToParent v) := by
  conv_lhs =>
    lhs
    unfold pathParityChain
    simp only [hv, ↓reduceDIte]
  -- c'(v) = c'(parent v) + z(edge)
  -- So c'(v) + c'(parent v) = c'(parent v) + z(edge) + c'(parent v)
  --                        = z(edge) + (c'(parent v) + c'(parent v))
  --                        = z(edge) + 0 = z(edge)
  have h2x : pathParityChain T z (T.parent v) + pathParityChain T z (T.parent v) = 0 :=
    ZMod2_self_add_self _
  calc pathParityChain T z (T.parent v) + z (T.edgeToParent v) + pathParityChain T z (T.parent v)
    = z (T.edgeToParent v) +
        (pathParityChain T z (T.parent v) + pathParityChain T z (T.parent v)) := by ring
    _ = z (T.edgeToParent v) + 0 := by rw [h2x]
    _ = z (T.edgeToParent v) := by ring

/-- **Helper**: Path parity chain equals c₀ plus a constant (c₀ at root).
    This is proven by induction on tree depth. -/
theorem pathParity_eq_c0_plus_const {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    {M : MeasurementConfig C L} (T : SpanningTree M) (z : EdgeChain M)
    (c₀ : VertexChain M) (hc₀ : delta0 M c₀ = z)
    (u : M.Vertex) :
    pathParityChain T z u = c₀ u + c₀ M.root := by
  -- Proof by well-founded induction on depth
  induction hd : T.depth u using Nat.strong_induction_on generalizing u with
  | _ d ih =>
    by_cases hu : u = M.root
    · -- Base case: u = root
      subst hu
      rw [pathParity_root]
      rw [ZMod2_self_add_self]
    · -- Inductive case: u ≠ root
      conv_lhs => unfold pathParityChain; simp only [hu, ↓reduceDIte]
      -- c'(u) = c'(parent u) + z(edgeToParent u)
      -- By IH on parent: c'(parent u) = c₀(parent u) + c₀(root)
      have hdepth_parent : T.depth (T.parent u) < d := by
        rw [← hd]
        exact T.parent_depth_lt u hu
      have ih_parent : pathParityChain T z (T.parent u) = c₀ (T.parent u) + c₀ M.root :=
        ih (T.depth (T.parent u)) hdepth_parent (T.parent u) rfl
      -- z(edgeToParent u) = c₀(u) + c₀(parent u) since δ₀(c₀) = z
      have hedge : z (T.edgeToParent u) = c₀ u + c₀ (T.parent u) := by
        rw [T.edge_connects]
        have := congrFun hc₀ s(u, T.parent u)
        simp only [delta0, Sym2.lift_mk] at this
        exact this.symm
      rw [ih_parent, hedge]
      -- c₀(parent u) + c₀(root) + (c₀(u) + c₀(parent u))
      -- = c₀(u) + c₀(root) + (c₀(parent u) + c₀(parent u))
      -- = c₀(u) + c₀(root) + 0 = c₀(u) + c₀(root)
      have h2x : c₀ (T.parent u) + c₀ (T.parent u) = 0 := ZMod2_self_add_self _
      calc c₀ (T.parent u) + c₀ M.root + (c₀ u + c₀ (T.parent u))
        = c₀ u + c₀ M.root + (c₀ (T.parent u) + c₀ (T.parent u)) := by ring
        _ = c₀ u + c₀ M.root + 0 := by rw [h2x]
        _ = c₀ u + c₀ M.root := by ring

/-- **Main Correctness Theorem**: If z is in the image of δ₀, then the path parity chain
    satisfies δ₀(c') = z on ALL edges.

    This is the key result: the spanning tree construction recovers a solution to δ₀(c') = z.
    The flux constraint (z ∈ im(δ₀)) is essential - it ensures z sums to 0 on every cycle.

    **Proof**:
    1. Since z ∈ im(δ₀), there exists c₀ with δ₀(c₀) = z
    2. By pathParity_eq_c0_plus_const: c'(v) = c₀(v) + c₀(root) for all v
    3. So δ₀(c')(e) = c'(v) + c'(w) = (c₀(v) + c₀(root)) + (c₀(w) + c₀(root))
                    = c₀(v) + c₀(w) + 2*c₀(root) = c₀(v) + c₀(w) = z(e)
    The key is that the constant c₀(root) cancels: 2x = 0 in ZMod 2! -/
theorem algorithm_correctness {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (M : MeasurementConfig C L)
    (T : SpanningTree M) (z : EdgeChain M)
    (hz : inImageDelta0 M z) :
    satisfiesByproductEquation M (pathParityChain T z) z := by
  -- Since z is in the image, there exists some c₀ with δ₀(c₀) = z
  obtain ⟨c₀, hc₀⟩ := hz
  -- Direct proof: show δ₀(c') agrees with z on every edge
  unfold satisfiesByproductEquation
  funext e
  -- Use Sym2.ind to work with e = s(v, w)
  refine Sym2.ind (fun v w => ?_) e
  simp only [delta0, Sym2.lift_mk]
  -- Need: c'(v) + c'(w) = z(s(v,w))
  -- From hc₀: c₀(v) + c₀(w) = z(s(v,w))
  have hc₀_edge : c₀ v + c₀ w = z s(v, w) := by
    have := congrFun hc₀ s(v, w)
    simp only [delta0, Sym2.lift_mk] at this
    exact this
  -- By pathParity_eq_c0_plus_const: c'(v) = c₀(v) + c₀(root)
  have hv : pathParityChain T z v = c₀ v + c₀ M.root :=
    pathParity_eq_c0_plus_const T z c₀ hc₀ v
  have hw : pathParityChain T z w = c₀ w + c₀ M.root :=
    pathParity_eq_c0_plus_const T z c₀ hc₀ w
  -- Now we can conclude
  rw [hv, hw]
  -- (c₀ v + c₀ root) + (c₀ w + c₀ root)
  -- = c₀ v + c₀ w + (c₀ root + c₀ root)
  -- = c₀ v + c₀ w + 0 = c₀ v + c₀ w = z(s(v,w))
  have h2x : c₀ M.root + c₀ M.root = 0 := ZMod2_self_add_self _
  calc (c₀ v + c₀ M.root) + (c₀ w + c₀ M.root)
    = c₀ v + c₀ w + (c₀ M.root + c₀ M.root) := by ring
    _ = c₀ v + c₀ w + 0 := by rw [h2x]
    _ = c₀ v + c₀ w := by ring
    _ = z s(v, w) := hc₀_edge

/-! ## Section 7: Uniqueness - Up to Constant

Any two solutions c' and c'' of δ₀(c) = z differ by a constant (element of ker(δ₀)).
For connected graphs, ker(δ₀) = {0, 1_V}, so solutions are unique up to adding 1_V.
-/

/-- If c' and c'' both satisfy δ₀(c) = z, they differ by an element of ker(δ₀) -/
theorem byproductChain_diff_in_ker {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (c' c'' : VertexChain M) (z : EdgeChain M)
    (hc' : satisfiesByproductEquation M c' z)
    (hc'' : satisfiesByproductEquation M c'' z) :
    delta0 M (fun v => c' v + c'' v) = fun _ => 0 := by
  unfold satisfiesByproductEquation at hc' hc''
  funext e
  simp only [delta0]
  refine Sym2.ind (fun v w => ?_) e
  simp only [Sym2.lift_mk]
  have h1 := congrFun hc' s(v, w)
  have h2 := congrFun hc'' s(v, w)
  simp only [delta0, Sym2.lift_mk] at h1 h2
  have h2x : z s(v, w) + z s(v, w) = 0 := ZMod2_self_add_self _
  calc (c' v + c'' v) + (c' w + c'' w)
    = (c' v + c' w) + (c'' v + c'' w) := by ring
    _ = z s(v, w) + z s(v, w) := by rw [h1, h2]
    _ = 0 := h2x

/-- **Uniqueness Theorem**: For connected graphs, byproduct solutions are unique up to 1_V -/
theorem byproductChain_unique_up_to_constant {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (M : MeasurementConfig C L)
    (c' c'' : VertexChain M) (z : EdgeChain M)
    (hc' : satisfiesByproductEquation M c' z)
    (hc'' : satisfiesByproductEquation M c'' z) :
    (fun v => c' v + c'' v) = zeroVertexChain M ∨
    (fun v => c' v + c'' v) = allOnesVertexChain M := by
  have hdiff := byproductChain_diff_in_ker M c' c'' z hc' hc''
  exact ker_delta0_connected M _ hdiff

/-- Alternative: c'' equals c' or c' + 1_V -/
theorem byproductChain_unique_two_options {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (M : MeasurementConfig C L)
    (c' c'' : VertexChain M) (z : EdgeChain M)
    (hc' : satisfiesByproductEquation M c' z)
    (hc'' : satisfiesByproductEquation M c'' z) :
    c'' = c' ∨ c'' = addVertexChain c' (allOnesVertexChain M) := by
  have h := byproductChain_unique_up_to_constant M c' c'' z hc' hc''
  cases h with
  | inl h0 =>
    left
    funext v
    have hv := congrFun h0 v
    simp only [zeroVertexChain] at hv
    have h2x : c' v + c' v = 0 := ZMod2_self_add_self _
    calc c'' v = 0 + c'' v := by ring
      _ = (c' v + c' v) + c'' v := by rw [h2x]
      _ = c' v + (c' v + c'' v) := by ring
      _ = c' v + 0 := by rw [hv]
      _ = c' v := by ring
  | inr h1 =>
    right
    funext v
    have hv := congrFun h1 v
    simp only [allOnesVertexChain, addVertexChain] at *
    have h2x : c' v + c' v = 0 := ZMod2_self_add_self _
    calc c'' v = 0 + c'' v := by ring
      _ = (c' v + c' v) + c'' v := by rw [h2x]
      _ = c' v + (c' v + c'' v) := by ring
      _ = c' v + 1 := by rw [hv]

/-! ## Section 8: Existence of Spanning Trees

For any connected finite graph, a spanning tree exists. We prove this using
the BFS/DFS construction: starting from root, greedily add edges that connect
new vertices until all vertices are reached.
-/

/-- A vertex is reachable from root with a given depth bound -/
def reachableWithDepth {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (v : M.Vertex) (d : ℕ) : Prop :=
  ∃ p : M.graph.graph.Walk M.root v, p.length ≤ d

/-- For a connected graph, every vertex is reachable from root -/
theorem all_vertices_reachable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) (v : M.Vertex) :
    M.graph.graph.Reachable M.root v :=
  M.graph.connected.preconnected M.root v

/-- For a connected finite graph, a spanning tree can be constructed.

    **Construction**: We use graph distance from root as the depth function.
    For each non-root vertex v, we pick a neighbor w such that dist(root, w) < dist(root, v).
    Such a neighbor exists on any shortest path from root to v.

    This gives a valid spanning tree where depth = dist(root, _). -/
theorem spanningTree_exists {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (M : MeasurementConfig C L) :
    ∃ _T : SpanningTree M, True := by
  have hconn := M.graph.connected
  classical
  -- Use graph distance from root as depth
  let depth' : M.Vertex → ℕ := fun v => M.graph.graph.dist M.root v
  -- For each non-root v, find a neighbor closer to root
  -- This exists because any shortest path from root to v has a penultimate vertex
  have hparent_exists : ∀ v : M.Vertex, v ≠ M.root →
      ∃ w : M.Vertex, M.graph.graph.Adj w v ∧ depth' w < depth' v := by
    intro v hv
    have hreach : M.graph.graph.Reachable M.root v := hconn.preconnected M.root v
    -- dist(root, v) > 0 since v ≠ root
    have hdist_pos : 0 < depth' v := by
      simp only [depth']
      exact hreach.pos_dist_of_ne (fun h => hv h.symm)
    -- Get a path of length = dist
    obtain ⟨p, hp_path, hp_len⟩ := hreach.exists_path_of_dist
    -- Since dist > 0, path is nonempty, so we can decompose it
    -- p is a path from root to v with length = dist > 0
    -- Decompose: p = root --(adj)--> w --p'--> v
    obtain ⟨w, hadj, p', hp'⟩ := p.exists_eq_cons_of_ne (fun h => hv h.symm)
    -- w is adjacent to v via the cons structure, and p' : Walk w v
    -- hadj : Adj root w, p' : Walk w v
    -- We need a neighbor OF v (adjacent to v) closer to root
    -- The path is root --> w --> ... --> v
    -- We need to look at the end, not the beginning
    -- Use reverse: p.reverse is a path from v to root
    -- Then decompose p.reverse to get the neighbor of v
    let p_rev := p.reverse
    -- p_rev : Walk v root of same length
    obtain ⟨u, hadj_u, p'', hp''⟩ := p_rev.exists_eq_cons_of_ne (fun h => hv h)
    -- hadj_u : Adj v u, p'' : Walk u root
    refine ⟨u, hadj_u.symm, ?_⟩
    simp only [depth']
    -- dist(root, u) ≤ p''.reverse.length < p.length = dist(root, v)
    have hdist_u : M.graph.graph.dist M.root u ≤ p''.reverse.length := by
      apply SimpleGraph.dist_le
    -- p_rev = cons hadj_u p'' means p_rev.length = 1 + p''.length
    have hlen_p_rev : p_rev.length = p''.length + 1 := by
      rw [hp'']
      simp [SimpleGraph.Walk.length_cons]
    -- p_rev = p.reverse, so p_rev.length = p.length
    have hrev_len : p_rev.length = p.length := SimpleGraph.Walk.length_reverse p
    -- p''.reverse.length = p''.length
    have hrev_p'' : p''.reverse.length = p''.length := SimpleGraph.Walk.length_reverse p''
    calc M.graph.graph.dist M.root u
      ≤ p''.reverse.length := hdist_u
      _ = p''.length := hrev_p''
      _ < p''.length + 1 := Nat.lt_succ_self _
      _ = p_rev.length := hlen_p_rev.symm
      _ = p.length := hrev_len
      _ = M.graph.graph.dist M.root v := hp_len
  -- Choose parent for each non-root vertex
  choose parent hparent using hparent_exists
  -- Build parent' that handles all vertices
  let parent' : M.Vertex → M.Vertex := fun v =>
    if hv : v = M.root then M.root else parent v hv
  let edgeToParent' : M.Vertex → Sym2 M.Vertex := fun v => s(v, parent' v)
  -- Construct the spanning tree
  refine ⟨{
    parent := parent'
    depth := depth'
    edgeToParent := edgeToParent'
    root_depth := ?hroot
    root_is_own_parent := by simp [parent']
    nonroot_pos_depth := ?hnonroot
    parent_depth_lt := ?hlt
    edge_connects := by intro v; simp [edgeToParent']
    edge_in_graph := ?hedge
  }, trivial⟩
  case hroot =>
    simp only [depth']
    exact SimpleGraph.dist_self
  case hnonroot =>
    intro v hv
    simp only [depth']
    have hreach : M.graph.graph.Reachable M.root v := hconn.preconnected M.root v
    exact hreach.pos_dist_of_ne (fun h => hv h.symm)
  case hlt =>
    intro v hv
    simp only [parent', hv, ↓reduceDIte]
    exact (hparent v hv).2
  case hedge =>
    intro v hv
    simp only [edgeToParent', parent', hv, ↓reduceDIte]
    rw [SimpleGraph.mem_edgeSet]
    exact (hparent v hv).1.symm

/-! ## Section 9: Complete Algorithm Correctness Statement

Combining all the pieces: for a connected graph with flux constraint satisfied,
the path parity algorithm correctly computes the byproduct chain.
-/

/-- **Complete Algorithm Correctness**:
    Given a measurement configuration M and edge outcomes z satisfying the flux constraint
    (i.e., z ∈ im(δ₀)), there exists a spanning tree T such that the path parity chain c'
    computed from T satisfies:
    1. c'(root) = 0
    2. δ₀(c') = z (on ALL edges)
    3. c' is unique up to adding 1_V -/
theorem algorithm_correctness_complete {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (M : MeasurementConfig C L)
    (z : EdgeChain M) (hz : inImageDelta0 M z) :
    ∃ c' : VertexChain M,
      c' M.root = 0 ∧
      satisfiesByproductEquation M c' z ∧
      (∀ c'' : VertexChain M, satisfiesByproductEquation M c'' z →
        c'' = c' ∨ c'' = addVertexChain c' (allOnesVertexChain M)) := by
  -- Get a spanning tree
  obtain ⟨T, _⟩ := spanningTree_exists M
  -- Construct c' via path parity
  use pathParityChain T z
  constructor
  · exact pathParity_root T z
  constructor
  · exact algorithm_correctness M T z hz
  · intro c'' hc''
    exact byproductChain_unique_two_options M (pathParityChain T z) c'' z
      (algorithm_correctness M T z hz) hc''

/-! ## Section 10: Helper Lemmas -/

/-- Helper: foldl with zero function is zero -/
theorem foldl_const_zero {α : Type*} (path : List α) :
    List.foldl (fun (acc : ZMod 2) (_e : α) => acc + 0) 0 path = 0 := by
  induction path with
  | nil => rfl
  | cons _ tl ih =>
    unfold List.foldl
    rw [add_zero]
    exact ih

/-- Zero edge outcomes give zero byproduct (proven by induction on depth) -/
theorem pathParity_zero_z {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    {M : MeasurementConfig C L} (T : SpanningTree M) (v : M.Vertex) :
    pathParityChain T (fun _ => 0) v = 0 := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ d ih =>
    by_cases hv : v = M.root
    · subst hv; exact pathParity_root T _
    · conv_lhs => unfold pathParityChain; simp only [hv, ↓reduceDIte]
      have hdepth_parent : T.depth (T.parent v) < d := by
        rw [← hd]
        exact T.parent_depth_lt v hv
      have ih_parent : pathParityChain T (fun _ => 0) (T.parent v) = 0 :=
        ih (T.depth (T.parent v)) hdepth_parent (T.parent v) rfl
      rw [ih_parent]
      ring

end QEC
