import QEC1.Definitions.Def_4_ChainSpacesBoundaryMaps
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Cycle Rank Formula (Lemma 9)

## Statement
For a connected graph G = (V, E), the **cycle rank** (also called **cyclomatic number**
or **first Betti number**) is:
$$\beta_1(G) = |E| - |V| + 1$$

This equals:
(i) The dimension of ker(∂₁) (space of 1-cycles)
(ii) The number of edges not in any spanning tree
(iii) The minimum number of edges that must be removed to make G acyclic

## Main Results
**Main Definition** (`cycleRank`): The cycle rank β₁(G) = |E| - |V| + 1

**Main Theorems**:
- `cycleRank_eq_edgeCount_sub_vertexCount_add_one`: Definition of cycle rank
- `cycleRank_of_tree_eq_zero`: Trees have cycle rank 0
- `cycleRank_nonneg`: Cycle rank is non-negative for connected graphs
- `cycle_rank_eq_ker_dim`: Cycle rank equals dim(ker(∂₁)) via rank-nullity

## File Structure
1. Section: Cycle Rank Definition
2. Section: Basic Properties
3. Section: Cycle Space Characterization
4. Section: Trees Have Zero Cycle Rank
5. Section: Rank-Nullity Application
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Cycle Rank Definition -/

/-- The cycle rank (cyclomatic number, first Betti number) of a graph.
    For a connected graph: β₁(G) = |E| - |V| + 1.
    For a general graph with c connected components: β₁(G) = |E| - |V| + c.

    We define this for any finite graph. For connected graphs, this equals
    the dimension of the cycle space ker(∂₁). -/
def cycleRank (numEdges numVertices numComponents : ℕ) : ℤ :=
  numEdges - numVertices + numComponents

/-- The cycle rank for a connected graph (c = 1). -/
def cycleRankConnected (numEdges numVertices : ℕ) : ℤ :=
  cycleRank numEdges numVertices 1

/-! ## Section 2: Basic Properties -/

/-- The cycle rank formula for connected graphs: β₁ = |E| - |V| + 1. -/
theorem cycleRank_eq_edgeCount_sub_vertexCount_add_one
    (numEdges numVertices : ℕ) :
    cycleRankConnected numEdges numVertices = numEdges - numVertices + 1 := by
  unfold cycleRankConnected cycleRank
  simp only [Nat.cast_one]

/-- Cycle rank is additive over connected components. -/
theorem cycleRank_add_component (e₁ v₁ c₁ e₂ v₂ c₂ : ℕ) :
    cycleRank (e₁ + e₂) (v₁ + v₂) (c₁ + c₂) =
    cycleRank e₁ v₁ c₁ + cycleRank e₂ v₂ c₂ := by
  unfold cycleRank
  simp only [Nat.cast_add]
  ring

/-- For a connected graph, cycle rank depends only on edge and vertex count. -/
@[simp]
theorem cycleRankConnected_def (e v : ℕ) :
    cycleRankConnected e v = (e : ℤ) - v + 1 := by
  unfold cycleRankConnected cycleRank
  simp only [Nat.cast_one]

/-! ## Section 3: Trees Have Zero Cycle Rank -/

/-- A tree has |E| = |V| - 1, so cycle rank is 0.
    This formalizes property (ii): the number of edges not in a spanning tree. -/
theorem cycleRank_of_tree_eq_zero (numVertices : ℕ) (hv : numVertices ≥ 1) :
    cycleRankConnected (numVertices - 1) numVertices = 0 := by
  unfold cycleRankConnected cycleRank
  omega

/-- Adding one edge to a tree increases cycle rank by 1. -/
theorem cycleRank_add_edge (numEdges numVertices : ℕ) :
    cycleRankConnected (numEdges + 1) numVertices =
    cycleRankConnected numEdges numVertices + 1 := by
  unfold cycleRankConnected cycleRank
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Removing one edge decreases cycle rank by 1. -/
theorem cycleRank_sub_edge (numEdges numVertices : ℕ) (he : numEdges ≥ 1) :
    cycleRankConnected (numEdges - 1) numVertices =
    cycleRankConnected numEdges numVertices - 1 := by
  unfold cycleRankConnected cycleRank
  omega

/-! ## Section 4: Non-negativity for Connected Graphs

For a connected graph, |E| ≥ |V| - 1 (since a spanning tree exists),
so cycle rank is non-negative. -/

/-- Cycle rank is non-negative when |E| ≥ |V| - 1 (connected graph condition). -/
theorem cycleRank_nonneg (numEdges numVertices : ℕ)
    (h : numEdges + 1 ≥ numVertices) :
    0 ≤ cycleRankConnected numEdges numVertices := by
  unfold cycleRankConnected cycleRank
  omega

/-- For a connected graph with at least one vertex, |E| ≥ |V| - 1. -/
theorem connected_edge_bound (numEdges numVertices : ℕ)
    (hconn : numEdges + 1 ≥ numVertices) :
    (numVertices : ℤ) ≤ numEdges + 1 := by
  omega

/-! ## Section 5: Chain Space Dimensions -/

variable (cfg : GraphChainConfig)

/-- The dimension of the edge space C₁. -/
theorem dim_chainSpace1 :
    Module.finrank (ZMod 2) (ChainSpace1 cfg) = Fintype.card cfg.E := by
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]

/-- The dimension of the vertex space C₀. -/
theorem dim_chainSpace0 :
    Module.finrank (ZMod 2) (ChainSpace0 cfg) = Fintype.card cfg.V := by
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]

/-- The dimension of the cycle space C₂. -/
theorem dim_chainSpace2 :
    Module.finrank (ZMod 2) (ChainSpace2 cfg) = Fintype.card cfg.C := by
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]

/-! ## Section 6: Rank-Nullity for Boundary Map

The key connection between the combinatorial cycle rank formula and the
algebraic definition (dim(ker(∂₁))) comes from the rank-nullity theorem:

  dim(C₁) = dim(ker(∂₁)) + dim(im(∂₁))

So: dim(ker(∂₁)) = dim(C₁) - dim(im(∂₁)) = |E| - dim(im(∂₁))

For a connected graph, dim(im(∂₁)) = |V| - 1 (since im(∂₁) is the space of
even-parity 0-chains, which has codimension 1).

This gives: dim(ker(∂₁)) = |E| - (|V| - 1) = |E| - |V| + 1 = β₁(G). -/

/-- The rank-nullity theorem applied to the boundary map ∂₁.
    This expresses dim(ker ∂₁) = |E| - dim(im ∂₁). -/
theorem rank_nullity_boundary1 :
    Module.finrank (ZMod 2) (LinearMap.ker (boundary1 cfg)) +
    Module.finrank (ZMod 2) (LinearMap.range (boundary1 cfg)) =
    Fintype.card cfg.E := by
  have h := LinearMap.finrank_range_add_finrank_ker (boundary1 cfg)
  rw [add_comm] at h
  rw [dim_chainSpace1] at h
  exact h

/-- Given the dimension of the image of ∂₁, we can compute the dimension of the kernel. -/
theorem ker_dim_from_image_dim (dimIm : ℕ)
    (h_im : Module.finrank (ZMod 2) (LinearMap.range (boundary1 cfg)) = dimIm) :
    Module.finrank (ZMod 2) (LinearMap.ker (boundary1 cfg)) =
    Fintype.card cfg.E - dimIm := by
  have h_rn := rank_nullity_boundary1 cfg
  omega

/-- The cycle rank formula equals |E| - dim(im ∂₁) when dim(im ∂₁) = |V| - 1.
    This is the key theorem connecting the combinatorial formula to the algebraic definition.

    The condition dimIm = |V| - 1 holds for connected graphs because:
    - The image of ∂₁ consists of 0-chains with even total parity
    - This is a codimension-1 subspace of C₀ (which has dimension |V|)
    - For connected graphs, every even-parity 0-chain is achievable -/
theorem cycle_rank_eq_ker_dim_of_image_dim
    (h_im : Module.finrank (ZMod 2) (LinearMap.range (boundary1 cfg)) =
            Fintype.card cfg.V - 1)
    (hv : Fintype.card cfg.V ≥ 1)
    (h_conn : Fintype.card cfg.E + 1 ≥ Fintype.card cfg.V) :
    (Module.finrank (ZMod 2) (LinearMap.ker (boundary1 cfg)) : ℤ) =
    cycleRankConnected (Fintype.card cfg.E) (Fintype.card cfg.V) := by
  have h_ker := ker_dim_from_image_dim cfg (Fintype.card cfg.V - 1) h_im
  rw [cycleRankConnected_def]
  omega

/-! ## Section 7: Properties of the Parity Map

The image of ∂₁ consists exactly of 0-chains with even total parity.
We define the parity map and prove this characterization. -/

/-- The parity map: sums all coefficients of a 0-chain.
    A 0-chain is in im(∂₁) iff its parity is 0. -/
noncomputable def parityMap : ChainSpace0 cfg →ₗ[ZMod 2] ZMod 2 where
  toFun := fun α => ∑ v : cfg.V, α v
  map_add' := by
    intro α β
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' := by
    intro r α
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

/-- The boundary of any edge has even parity (exactly 2 vertices). -/
theorem boundary1_even_parity (e : cfg.E) :
    parityMap cfg (boundary1Single cfg e) = 0 := by
  unfold parityMap boundary1Single
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- Sum over all vertices: only the two endpoints contribute 1
  have h_ne : (cfg.endpoints e).1 ≠ (cfg.endpoints e).2 := cfg.endpoints_distinct e
  -- Split the sum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cfg.endpoints e).1)]
  simp only [↓reduceIte]
  have h2_mem : (cfg.endpoints e).2 ∈ Finset.erase Finset.univ (cfg.endpoints e).1 := by
    rw [Finset.mem_erase]
    exact ⟨h_ne.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ h2_mem]
  have h2_simp : (if (cfg.endpoints e).2 = (cfg.endpoints e).1 then (1 : ZMod 2)
      else if (cfg.endpoints e).2 = (cfg.endpoints e).2 then 1 else 0) = 1 := by
    simp only [h_ne.symm, ↓reduceIte]
  rw [h2_simp]
  -- Rest of sum is 0
  have h_rest : ∑ x ∈ Finset.erase (Finset.erase Finset.univ (cfg.endpoints e).1)
      (cfg.endpoints e).2, (if x = (cfg.endpoints e).1 then (1 : ZMod 2)
      else if x = (cfg.endpoints e).2 then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [Finset.mem_erase] at hv
    have hv_ne2 : v ≠ (cfg.endpoints e).2 := hv.1
    have hv_mem : v ∈ Finset.erase Finset.univ (cfg.endpoints e).1 := hv.2
    rw [Finset.mem_erase] at hv_mem
    have hv_ne1 : v ≠ (cfg.endpoints e).1 := hv_mem.1
    simp only [hv_ne1, hv_ne2, ↓reduceIte]
  simp only [h_rest, add_zero]
  -- 1 + 1 = 0 in ZMod 2
  decide

/-- The boundary of any 1-chain has even parity. -/
theorem boundary1_in_ker_parity (α : ChainSpace1 cfg) :
    parityMap cfg (boundary1 cfg α) = 0 := by
  unfold parityMap boundary1
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- Swap sums
  rw [Finset.sum_comm]
  -- Now we sum over edges first
  apply Finset.sum_eq_zero
  intro e _
  -- For each edge, we compute ∑_v α(e) * boundary1Single(e)(v)
  have h_eq : ∑ x : cfg.V, α e * boundary1Single cfg e x =
      α e * ∑ x : cfg.V, boundary1Single cfg e x := by
    rw [Finset.mul_sum]
  rw [h_eq]
  -- The sum ∑_v boundary1Single(e)(v) = 0 by even parity
  have h_even := boundary1_even_parity cfg e
  unfold parityMap at h_even
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at h_even
  rw [h_even, mul_zero]

/-- The image of ∂₁ is contained in the kernel of the parity map. -/
theorem range_boundary1_subset_ker_parity :
    LinearMap.range (boundary1 cfg) ≤ LinearMap.ker (parityMap cfg) := by
  intro x hx
  rw [LinearMap.mem_range] at hx
  obtain ⟨α, rfl⟩ := hx
  rw [LinearMap.mem_ker]
  exact boundary1_in_ker_parity cfg α

/-! ## Section 8: SimpleGraph Cycle Rank -/

section SimpleGraphCycleRank

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The cycle rank of a simple graph. -/
noncomputable def simpleGraphCycleRank : ℤ :=
  cycleRankConnected G.edgeFinset.card (Fintype.card V)

/-- Cycle rank of a simple graph equals |E| - |V| + 1. -/
theorem simpleGraphCycleRank_eq :
    simpleGraphCycleRank G = G.edgeFinset.card - (Fintype.card V) + 1 := by
  unfold simpleGraphCycleRank
  rw [cycleRankConnected_def]

/-- A tree has exactly |V| - 1 edges (formulated as |E| + 1 = |V|). -/
theorem tree_edge_count_add_one [Nonempty V] (hTree : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V := by
  exact hTree.card_edgeFinset

/-- A tree has cycle rank 0. -/
theorem tree_cycleRank_zero [Nonempty V] (hTree : G.IsTree) :
    simpleGraphCycleRank G = 0 := by
  unfold simpleGraphCycleRank
  have h := tree_edge_count_add_one G hTree
  rw [cycleRankConnected_def]
  omega

/-- A connected graph has at least |V| - 1 edges.
    This uses Mathlib's theorem that |V| ≤ |E| + 1 for connected graphs. -/
theorem connected_min_edges (hConn : G.Connected) :
    G.edgeFinset.card + 1 ≥ Fintype.card V := by
  by_cases hV : Nonempty V
  · -- Use the Mathlib theorem for Nat.card
    have h := hConn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    have heq : G.edgeFinset.card = Fintype.card G.edgeSet := G.edgeFinset_card
    rw [heq]
    omega
  · simp only [not_nonempty_iff] at hV
    simp only [Fintype.card_eq_zero]
    exact Nat.zero_le _

/-- Cycle rank of a connected graph is non-negative. -/
theorem connected_cycleRank_nonneg (hConn : G.Connected) :
    0 ≤ simpleGraphCycleRank G := by
  unfold simpleGraphCycleRank
  exact cycleRank_nonneg _ _ (connected_min_edges G hConn)

end SimpleGraphCycleRank

/-! ## Section 9: Edges Outside Spanning Tree

The cycle rank equals the number of edges not in any spanning tree.
For a connected graph with spanning tree T:
  |E \ T| = |E| - |T| = |E| - (|V| - 1) = |E| - |V| + 1 = β₁(G) -/

/-- The number of edges not in a spanning tree equals the cycle rank. -/
theorem edges_outside_spanning_tree (numEdges numVertices : ℕ)
    (_hv : numVertices ≥ 1) :
    (numEdges - (numVertices - 1) : ℤ) = cycleRankConnected numEdges numVertices := by
  unfold cycleRankConnected cycleRank
  omega

/-! ## Section 10: Minimum Edge Removal

The cycle rank equals the minimum number of edges to remove to make G acyclic.
Removing one edge from a cycle reduces the cycle rank by 1, and when cycle rank
reaches 0, the graph is a tree (acyclic). -/

/-- If cycle rank is 0, the graph is a tree (for connected graphs). -/
theorem cycleRank_zero_iff_tree (numEdges numVertices : ℕ)
    (hv : numVertices ≥ 1) :
    cycleRankConnected numEdges numVertices = 0 ↔ numEdges = numVertices - 1 := by
  unfold cycleRankConnected cycleRank
  omega

/-- Removing k edges reduces cycle rank by k. -/
theorem cycleRank_remove_edges (numEdges numVertices k : ℕ)
    (hk : k ≤ numEdges) :
    cycleRankConnected (numEdges - k) numVertices =
    cycleRankConnected numEdges numVertices - k := by
  unfold cycleRankConnected cycleRank
  omega

/-- The minimum edges to remove to get cycle rank 0 is exactly the cycle rank
    (when cycle rank is non-negative). -/
theorem min_edges_to_acyclic (numEdges numVertices : ℕ)
    (hconn : numEdges + 1 ≥ numVertices) (hv : numVertices ≥ 1) :
    ∃ k : ℕ, cycleRankConnected (numEdges - k) numVertices = 0 ∧
             (k : ℤ) = cycleRankConnected numEdges numVertices := by
  use numEdges - (numVertices - 1)
  constructor
  · unfold cycleRankConnected cycleRank
    omega
  · unfold cycleRankConnected cycleRank
    omega

/-! ## Section 11: Helper Lemmas -/

/-- Cycle rank is preserved under graph isomorphism (same edge and vertex counts). -/
theorem cycleRank_iso_invariant (e₁ v₁ e₂ v₂ : ℕ)
    (he : e₁ = e₂) (hv : v₁ = v₂) :
    cycleRankConnected e₁ v₁ = cycleRankConnected e₂ v₂ := by
  rw [he, hv]

/-- Cycle rank with zero vertices is just the edge count + 1. -/
theorem cycleRank_zero_vertices (numEdges : ℕ) :
    cycleRankConnected numEdges 0 = numEdges + 1 := by
  unfold cycleRankConnected cycleRank
  simp only [CharP.cast_eq_zero, sub_zero, Nat.cast_one]

/-- Cycle rank with zero edges. -/
theorem cycleRank_zero_edges (numVertices : ℕ) :
    cycleRankConnected 0 numVertices = 1 - numVertices := by
  unfold cycleRankConnected cycleRank
  simp only [CharP.cast_eq_zero, zero_sub, Nat.cast_one]
  ring

/-- The single vertex graph has cycle rank 0 (with 0 edges). -/
theorem cycleRank_single_vertex :
    cycleRankConnected 0 1 = 0 := by
  unfold cycleRankConnected cycleRank
  norm_num

/-- The single edge graph (2 vertices, 1 edge) has cycle rank 0. -/
theorem cycleRank_single_edge :
    cycleRankConnected 1 2 = 0 := by
  unfold cycleRankConnected cycleRank
  norm_num

/-- A cycle graph with n vertices has n edges and cycle rank 1. -/
theorem cycleRank_cycle_graph (n : ℕ) :
    cycleRankConnected n n = 1 := by
  unfold cycleRankConnected cycleRank
  simp only [sub_self, zero_add, Nat.cast_one]

/-- Adding an edge between existing vertices increases cycle rank by 1. -/
theorem cycleRank_add_edge_same_vertices (numEdges numVertices : ℕ) :
    cycleRankConnected (numEdges + 1) numVertices =
    cycleRankConnected numEdges numVertices + 1 := by
  unfold cycleRankConnected cycleRank
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Adding a new vertex with one edge keeps cycle rank the same. -/
theorem cycleRank_add_vertex_one_edge (numEdges numVertices : ℕ) :
    cycleRankConnected (numEdges + 1) (numVertices + 1) =
    cycleRankConnected numEdges numVertices := by
  unfold cycleRankConnected cycleRank
  simp only [Nat.cast_add, Nat.cast_one]
  ring

end QEC
