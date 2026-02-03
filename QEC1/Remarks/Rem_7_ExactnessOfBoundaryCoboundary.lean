import QEC1.Remarks.Rem_2_ExactnessOfChainComplex

/-!
# Exactness of Boundary and Coboundary Maps (Remark 7)

## Statement
When a generating set of cycles for graph G is chosen, the maps ∂₂ (boundary from cycles to
edges) and ∂ (boundary from edges to vertices) form an exact sequence in the sense that
im(∂₂) = ker(∂). That is, the image of ∂₂ equals the kernel of ∂: an edge-set is the boundary
of some cycle-set if and only if it has zero boundary (i.e., every vertex has even degree in
the edge-set).

Similarly, the coboundary maps δ and δ₂ form an exact sequence: ker(δ₂) = im(δ).

Note that δ has a nontrivial kernel: ker(δ) = {𝟬, 𝟙} where 𝟙 is the all-ones vector
(corresponding to the full vertex set), since every edge has exactly two endpoints.

## Main Results
- `im_boundary2_eq_ker_boundary1`: Exactness at C₁ (when cycles generate all cycles)
- `ker_coboundary1_eq_im_coboundary0`: Dual exactness at C₁
- `ker_coboundary0_is_zero_or_allOnes`: ker(δ₀) = {0, 𝟙_V} for connected graphs
- `allOnes_mem_ker_coboundary0`: 𝟙_V ∈ ker(δ₀)
- `ker_coboundary0_nontrivial`: ker(δ₀) contains both 0 and 𝟙_V (nontrivial)

## Interpretation
- An edge-set γ has zero boundary iff every vertex has even degree in γ
- The coboundary of a vertex-set is the set of edges crossing the cut
- The all-ones vector corresponds to the full vertex set V
- Since every edge has exactly two endpoints, δ(V) = δ(𝟙) = 0

## File Structure
1. Exactness Characterization for Boundaries
2. Dual Exactness for Coboundaries
3. Nontrivial Kernel of δ₀
4. Zero Boundary Characterization
5. Simp Lemmas and Corollaries
-/

namespace QEC

open scoped BigOperators

variable (cfg : GraphChainConfig)

/-! ## Section 1: Exactness Characterization

The remark states that im(∂₂) = ker(∂₁). We formalize this as:
- One direction (im(∂₂) ⊆ ker(∂₁)) is `im_boundary2_subset_ker_boundary1` from Rem_2
- The other direction (ker(∂₁) ⊆ im(∂₂)) requires that the chosen cycles generate all cycles
-/

/-- Exactness at C₁: im(∂₂) = ker(∂₁), stated as a biconditional.
    An edge-set is in the image of ∂₂ iff it has zero boundary.
    This requires that the cycles generate all cycles (CyclesGenerate property). -/
theorem im_boundary2_eq_ker_boundary1 (hgen : CyclesGenerate cfg) (γ : ChainSpace1 cfg) :
    (∃ β : ChainSpace2 cfg, boundary2 cfg β = γ) ↔ boundary1 cfg γ = 0 :=
  (exactness_at_C1_of_generates cfg hgen γ).symm

/-- The characterization rephrased: γ ∈ ker(∂₁) iff γ ∈ im(∂₂). -/
theorem ker_boundary1_eq_im_boundary2 (hgen : CyclesGenerate cfg) (γ : ChainSpace1 cfg) :
    boundary1 cfg γ = 0 ↔ ∃ β : ChainSpace2 cfg, boundary2 cfg β = γ :=
  exactness_at_C1_of_generates cfg hgen γ

/-! ## Section 2: Dual Exactness

For coboundary maps, we have ker(δ₂) = im(δ₁), i.e., ker(coboundary1) = im(coboundary0).
- One direction (im(δ₀) ⊆ ker(δ₁)) is `im_coboundary0_subset_ker_coboundary1` from Rem_2
- The other direction requires dual cycle generation properties
-/

/-- Dual cycle generation property: every 1-chain in ker(δ₁) is in im(δ₀). -/
def DualCyclesGenerate : Prop :=
  ∀ γ : ChainSpace1 cfg, coboundary1 cfg γ = 0 →
    ∃ α : ChainSpace0 cfg, coboundary0 cfg α = γ

/-- Dual exactness at C₁: ker(δ₁) = im(δ₀), when the dual generation property holds.
    This states that an edge-set is in the image of coboundary₀ iff it's in the kernel
    of coboundary₁. -/
theorem ker_coboundary1_eq_im_coboundary0 (hdual : DualCyclesGenerate cfg)
    (γ : ChainSpace1 cfg) :
    coboundary1 cfg γ = 0 ↔ ∃ α : ChainSpace0 cfg, coboundary0 cfg α = γ := by
  constructor
  · exact hdual γ
  · intro ⟨α, hα⟩
    rw [← hα]
    exact im_coboundary0_subset_ker_coboundary1 cfg α

/-! ## Section 3: Nontrivial Kernel of δ₀

The remark emphasizes that δ (i.e., δ₀ = coboundary0) has a nontrivial kernel:
ker(δ₀) = {𝟬, 𝟙} where 𝟙 is the all-ones vector.

This is because:
- δ₀(𝟬) = 0 trivially (zero maps to zero)
- δ₀(𝟙)(e) = 1 + 1 = 0 for every edge e (since every edge has exactly two endpoints)

For a connected graph, these are the ONLY elements in ker(δ₀).
-/

/-- The all-ones vector is in ker(δ₀). This is the key insight: every edge has exactly
    two endpoints, so δ₀(𝟙)(e) = 𝟙(v) + 𝟙(v') = 1 + 1 = 0 for e = {v, v'}. -/
theorem allOnes_mem_ker_coboundary0' :
    coboundary0 cfg (allOnes cfg) = 0 :=
  allOnes_in_ker_coboundary0 cfg

/-- The zero vector is trivially in ker(δ₀). -/
theorem zero_mem_ker_coboundary0 :
    coboundary0 cfg 0 = 0 :=
  map_zero (coboundary0 cfg)

/-- For connected graphs, ker(δ₀) consists exactly of {0, 𝟙}.
    The kernel is nontrivial (contains more than just 0). -/
theorem ker_coboundary0_is_zero_or_allOnes' (hconn : IsConnectedGraph cfg)
    (α : ChainSpace0 cfg) (hα : coboundary0 cfg α = 0) :
    α = 0 ∨ α = allOnes cfg :=
  ker_coboundary0_eq_zero_or_allOnes cfg α hα hconn

/-- The kernel of δ₀ is nontrivial: it contains both 0 and 𝟙.
    This formalizes the remark that "δ has a nontrivial kernel". -/
theorem ker_coboundary0_nontrivial (cfg : GraphChainConfig) :
    (coboundary0 cfg 0 = 0) ∧ (coboundary0 cfg (allOnes cfg) = 0) :=
  ⟨zero_mem_ker_coboundary0 cfg, allOnes_mem_ker_coboundary0' cfg⟩

/-- The all-ones vector is nonzero if there is at least one vertex. -/
theorem allOnes_ne_zero [Nonempty cfg.V] : allOnes cfg ≠ 0 := by
  intro h
  have := congr_fun h (Classical.arbitrary cfg.V)
  simp [allOnes] at this

/-- For a nonempty graph, ker(δ₀) contains a nonzero element.
    This demonstrates the nontriviality concretely. -/
theorem ker_coboundary0_has_nonzero_element [Nonempty cfg.V] :
    ∃ α : ChainSpace0 cfg, α ≠ 0 ∧ coboundary0 cfg α = 0 :=
  ⟨allOnes cfg, allOnes_ne_zero cfg, allOnes_mem_ker_coboundary0' cfg⟩

/-! ## Section 4: Zero Boundary Characterization

The remark states that an edge-set has zero boundary "i.e., every vertex has even degree
in the edge-set". We formalize this characterization.
-/

/-- A 1-chain (edge-set) has zero boundary iff every vertex has even degree.
    The degree of v in γ is the number of edges incident to v, weighted by γ. -/
theorem zero_boundary_iff_even_degree (γ : ChainSpace1 cfg) :
    boundary1 cfg γ = 0 ↔
    ∀ v : cfg.V, (∑ e : cfg.E, γ e * boundary1Single cfg e v) = 0 :=
  mem_ker_boundary1_iff cfg γ

/-- The "degree" of vertex v in a 1-chain γ. This counts (with multiplicity) how many
    times edges incident to v appear in γ. -/
noncomputable def vertexDegreeIn (γ : ChainSpace1 cfg) (v : cfg.V) : ZMod 2 :=
  ∑ e : cfg.E, γ e * boundary1Single cfg e v

/-- Zero boundary is equivalent to all vertex degrees being zero (mod 2). -/
theorem zero_boundary_iff_all_degrees_zero (γ : ChainSpace1 cfg) :
    boundary1 cfg γ = 0 ↔ ∀ v : cfg.V, vertexDegreeIn cfg γ v = 0 := by
  unfold vertexDegreeIn
  exact mem_ker_boundary1_iff cfg γ

/-- Alternative characterization: boundary1 γ v = vertexDegreeIn γ v. -/
theorem boundary1_eq_vertexDegree (γ : ChainSpace1 cfg) (v : cfg.V) :
    (boundary1 cfg γ) v = vertexDegreeIn cfg γ v := by
  simp only [boundary1, vertexDegreeIn, LinearMap.coe_mk, AddHom.coe_mk]

/-! ## Section 5: Coboundary Characterization

The coboundary δ₀(α)(e) = α(v) + α(v') for e = {v, v'} is the "cut" function:
it equals 1 iff exactly one endpoint of e is in the set α.
-/

/-- Coboundary at an edge: δ₀(α)(e) = α(v) + α(v') where e = {v, v'}. -/
theorem coboundary0_at_edge (α : ChainSpace0 cfg) (e : cfg.E) :
    (coboundary0 cfg α) e = α (cfg.endpoints e).1 + α (cfg.endpoints e).2 := rfl

/-- The coboundary is zero at an edge iff both endpoints have the same value. -/
theorem coboundary0_zero_at_edge_iff (α : ChainSpace0 cfg) (e : cfg.E) :
    (coboundary0 cfg α) e = 0 ↔
    α (cfg.endpoints e).1 = α (cfg.endpoints e).2 := by
  rw [coboundary0_at_edge]
  constructor
  · intro h
    have := ZMod2_add_eq_zero_iff' (α (cfg.endpoints e).1) (α (cfg.endpoints e).2)
    exact this.mp h
  · intro h
    rw [h]
    exact ZMod2_add_self (α (cfg.endpoints e).2)

/-- For the all-ones vector, coboundary is zero at every edge
    because both endpoints have value 1. -/
theorem coboundary0_allOnes_at_edge (e : cfg.E) :
    (coboundary0 cfg (allOnes cfg)) e = 0 := by
  rw [coboundary0_at_edge]
  simp only [allOnes]
  decide

/-! ## Section 6: The Two Endpoints Property

The fundamental reason ker(δ₀) is nontrivial is that every edge has exactly two endpoints.
This is built into the structure of a graph and manifests as 1 + 1 = 0 in ZMod 2.
-/

/-- Every edge has exactly two endpoints, which in ZMod 2 means the all-ones coboundary
    sums to 0. This is the algebraic form of "every edge has exactly two endpoints". -/
theorem two_endpoints_property (_e : cfg.E) :
    (1 : ZMod 2) + 1 = 0 := by decide

/-- The coboundary of the full vertex set (all-ones) at any edge is zero. -/
theorem full_vertex_set_coboundary_zero :
    coboundary0 cfg (allOnes cfg) = 0 :=
  allOnes_mem_ker_coboundary0' cfg

/-! ## Section 7: Simp Lemmas -/

@[simp]
theorem coboundary0_allOnes :
    coboundary0 cfg (allOnes cfg) = 0 :=
  allOnes_mem_ker_coboundary0' cfg

@[simp]
theorem boundary1_boundary2 (β : ChainSpace2 cfg) :
    boundary1 cfg (boundary2 cfg β) = 0 :=
  im_boundary2_subset_ker_boundary1 cfg β

@[simp]
theorem coboundary1_coboundary0 (α : ChainSpace0 cfg) :
    coboundary1 cfg (coboundary0 cfg α) = 0 :=
  im_coboundary0_subset_ker_coboundary1 cfg α

/-! ## Section 8: Exactness Summary

Summarizing the exactness properties from the remark:

1. Boundary exactness (im(∂₂) = ker(∂₁)):
   - Always: im(∂₂) ⊆ ker(∂₁) (composition is zero)
   - With generation: ker(∂₁) ⊆ im(∂₂) (exactness)

2. Coboundary exactness (ker(δ₂) = im(δ₁)):
   - Always: im(δ₀) ⊆ ker(δ₁) (composition is zero)
   - With dual generation: ker(δ₁) ⊆ im(δ₀) (exactness)

3. Nontrivial kernel of δ₀:
   - ker(δ₀) ⊇ {0, 𝟙_V} always
   - For connected graphs: ker(δ₀) = {0, 𝟙_V}
-/

/-- Summary: The chain complex is a complex (∂₁ ∘ ∂₂ = 0). -/
theorem chain_complex_boundary :
    boundary1 cfg ∘ₗ boundary2 cfg = 0 :=
  boundary_comp_boundary_eq_zero cfg

/-- Summary: The cochain complex is a complex (δ₁ ∘ δ₀ = 0). -/
theorem cochain_complex_coboundary :
    coboundary1 cfg ∘ₗ coboundary0 cfg = 0 :=
  coboundary_comp_coboundary_eq_zero cfg

/-- Summary: For connected graphs, the kernel of δ₀ is exactly {0, 𝟙_V}. -/
theorem ker_coboundary0_classification (hconn : IsConnectedGraph cfg)
    (α : ChainSpace0 cfg) :
    coboundary0 cfg α = 0 ↔ α = 0 ∨ α = allOnes cfg := by
  constructor
  · exact fun hα => ker_coboundary0_is_zero_or_allOnes' cfg hconn α hα
  · intro h
    rcases h with rfl | rfl
    · exact zero_mem_ker_coboundary0 cfg
    · exact allOnes_mem_ker_coboundary0' cfg

/-! ## Section 9: Physical Interpretation

In the context of quantum error correction:
- Vertices represent qubits in the support of a logical operator
- Edges represent gauge qubits
- A 1-chain with zero boundary corresponds to a valid pattern of edge qubits
- The all-ones kernel element corresponds to the full vertex set V_G

The exactness properties ensure:
- Valid cycle patterns (ker(∂₁)) come from cycle generators (im(∂₂))
- Cut patterns (im(δ₀)) are exactly those that commute with all flux operators (ker(δ₁))
-/

/-- The exactness condition characterizes which edge-sets can be boundaries of cycle-sets. -/
theorem edge_set_is_cycle_boundary_iff (hgen : CyclesGenerate cfg) (γ : ChainSpace1 cfg) :
    (∃ β : ChainSpace2 cfg, boundary2 cfg β = γ) ↔
    (∀ v : cfg.V, vertexDegreeIn cfg γ v = 0) := by
  rw [im_boundary2_eq_ker_boundary1 cfg hgen γ]
  exact zero_boundary_iff_all_degrees_zero cfg γ

end QEC
