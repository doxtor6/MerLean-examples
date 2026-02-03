import QEC1.Definitions.Def_4_ChainSpacesBoundaryMaps
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Exactness of Chain Complex (Remark 2)

## Statement
Let G = (V, E) be a connected graph with a chosen generating set of cycles C.

The chain complex C₂ → C₁ → C₀ satisfies:

(i) Exactness at C₁: ker(∂₁) = im(∂₂) when C generates all cycles.
(ii) Exactness at C₀ (almost): im(∂₁) = {c ∈ C₀ : |c| ≡ 0 (mod 2)}.
(iii) Dual exactness: δ₁ ∘ δ₀ = 0, and ker(δ₀) = ℤ₂·𝟙_V for connected G.

## Main Results
- `coboundary_comp_coboundary_eq_zero`: δ₁ ∘ δ₀ = 0
- `boundary1_parity`: im(∂₁) has even parity
- `allOnes_in_ker_coboundary0`: 𝟙_V ∈ ker(δ₀)
- `im_boundary2_subset_ker_boundary1`: im(∂₂) ⊆ ker(∂₁)
- `im_coboundary0_subset_ker_coboundary1`: im(δ₀) ⊆ ker(δ₁)
- `ker_coboundary0_eq_zero_or_allOnes`: ker(δ₀) ⊆ {0, 𝟙_V} for connected graphs

## File Structure
1. Chain Complex Identity (Dual)
2. Kernel/Image Characterizations
3. Even Cardinality Condition
4. All-Ones Vector
5. Exactness Properties (One Direction)
6. Connected Graph Kernel Characterization
7. Helper Lemmas

## Note on Faithfulness
The full exactness results (ker = im) require:
- For ker(∂₁) = im(∂₂): The cycle set C must generate ALL cycles
- For ker(δ₀) = span{0, 𝟙_V}: Graph connectedness

This formalization proves:
- One direction always holds: im ⊆ ker (composition is zero)
- For connected graphs: ker(δ₀) consists only of 0 or 𝟙_V
- Parity constraint: im(∂₁) has even parity

The reverse directions require additional assumptions about cycle generation
that are not part of GraphChainConfig.
-/

namespace QEC

open scoped BigOperators

variable (cfg : GraphChainConfig)

/-! ## Section 1: Chain Complex Identity (Dual) -/

/-- Helper: sum over cycles of sums equals sum over edges of sums. -/
theorem coboundary_sum_swap (α : ChainSpace0 cfg) (c : cfg.C) :
    ∑ e ∈ cfg.cycleEdges c, (α (cfg.endpoints e).1 + α (cfg.endpoints e).2) = 0 := by
  have h_valid := cfg.cycles_valid c
  unfold isValidCycle' at h_valid
  have h_expand :
      ∑ e ∈ cfg.cycleEdges c, (α (cfg.endpoints e).1 + α (cfg.endpoints e).2) =
      ∑ e ∈ cfg.cycleEdges c, α (cfg.endpoints e).1 +
      ∑ e ∈ cfg.cycleEdges c, α (cfg.endpoints e).2 := by
    rw [← Finset.sum_add_distrib]
  rw [h_expand]
  suffices h : ∀ v : cfg.V,
      ((Finset.filter (fun e => (cfg.endpoints e).1 = v) (cfg.cycleEdges c)).card +
       (Finset.filter (fun e => (cfg.endpoints e).2 = v) (cfg.cycleEdges c)).card : ZMod 2) = 0 by
    have h1 : ∑ e ∈ cfg.cycleEdges c, α (cfg.endpoints e).1 =
        ∑ v : cfg.V, (Finset.filter
          (fun e => (cfg.endpoints e).1 = v) (cfg.cycleEdges c)).card • α v := by
      trans (∑ v : cfg.V, ∑ e ∈ cfg.cycleEdges c,
          if (cfg.endpoints e).1 = v then α v else 0)
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_eq_single (cfg.endpoints e).1]
        · simp
        · intro v _ hne
          simp [hne.symm]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have h2 : ∑ e ∈ cfg.cycleEdges c, α (cfg.endpoints e).2 =
        ∑ v : cfg.V, (Finset.filter
          (fun e => (cfg.endpoints e).2 = v) (cfg.cycleEdges c)).card • α v := by
      trans (∑ v : cfg.V, ∑ e ∈ cfg.cycleEdges c,
          if (cfg.endpoints e).2 = v then α v else 0)
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_eq_single (cfg.endpoints e).2]
        · simp
        · intro v _ hne
          simp [hne.symm]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [h1, h2, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro v _
    rw [← add_nsmul, nsmul_eq_mul]
    simp only [Nat.cast_add]
    rw [h v, zero_mul]
  intro v
  have h_disjoint : Disjoint
      (Finset.filter (fun e => (cfg.endpoints e).1 = v) (cfg.cycleEdges c))
      (Finset.filter (fun e => (cfg.endpoints e).2 = v) (cfg.cycleEdges c)) := by
    rw [Finset.disjoint_filter]
    intro e _ h1 h2
    have := cfg.endpoints_distinct e
    rw [h1, h2] at this
    exact this rfl
  have h_union_card :
      (Finset.filter (fun e => (cfg.endpoints e).1 = v) (cfg.cycleEdges c)).card +
      (Finset.filter (fun e => (cfg.endpoints e).2 = v) (cfg.cycleEdges c)).card =
      (Finset.filter (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
        (cfg.cycleEdges c)).card := by
    rw [← Finset.card_union_of_disjoint h_disjoint]
    congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have h_even := h_valid v
  have h_even' : Even (Finset.filter
      (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
      (cfg.cycleEdges c)).card := Nat.even_iff.mpr h_even
  have h1 : ((Finset.filter (fun e => (cfg.endpoints e).1 = v) (cfg.cycleEdges c)).card : ZMod 2) +
      (Finset.filter (fun e => (cfg.endpoints e).2 = v) (cfg.cycleEdges c)).card =
      ((Finset.filter (fun e => (cfg.endpoints e).1 = v) (cfg.cycleEdges c)).card +
        (Finset.filter (fun e => (cfg.endpoints e).2 = v) (cfg.cycleEdges c)).card : ℕ) := by
    simp only [Nat.cast_add]
  rw [h1, h_union_card]
  exact h_even'.natCast_zmod_two

/-- The dual chain complex identity: δ₁ ∘ δ₀ = 0. -/
theorem coboundary_comp_coboundary_eq_zero :
    coboundary1 cfg ∘ₗ coboundary0 cfg = 0 := by
  apply LinearMap.ext
  intro α
  apply funext
  intro c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [coboundary1, coboundary0, LinearMap.coe_mk, AddHom.coe_mk]
  exact coboundary_sum_swap cfg α c

/-! ## Section 2: Kernel/Image Characterizations -/

/-- An element is in ker(∂₁) iff every vertex has even degree. -/
theorem mem_ker_boundary1_iff (γ : ChainSpace1 cfg) :
    boundary1 cfg γ = 0 ↔
    ∀ v : cfg.V, (∑ e : cfg.E, γ e * boundary1Single cfg e v) = 0 := by
  constructor
  · intro h v
    have hv := congr_fun h v
    simp only [boundary1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hv
    exact hv
  · intro h
    apply funext
    intro v
    simp only [boundary1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    exact h v

/-- An element is in ker(δ₀) iff α(v) + α(v') = 0 for all edges. -/
theorem mem_ker_coboundary0_iff (α : ChainSpace0 cfg) :
    coboundary0 cfg α = 0 ↔
    ∀ e : cfg.E, α (cfg.endpoints e).1 + α (cfg.endpoints e).2 = 0 := by
  constructor
  · intro h e
    have he := congr_fun h e
    simp only [coboundary0, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at he
    exact he
  · intro h
    apply funext
    intro e
    simp only [coboundary0, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    exact h e

/-- In ZMod 2, α + β = 0 iff α = β -/
theorem ZMod2_add_eq_zero_iff' (α β : ZMod 2) : α + β = 0 ↔ α = β := by
  constructor
  · intro h
    have h1 : α + β + β = 0 + β := by rw [h]
    rw [zero_add, add_assoc] at h1
    have hbb : β + β = 0 := by fin_cases β <;> decide
    rw [hbb, add_zero] at h1
    exact h1
  · intro h
    rw [h]
    fin_cases β <;> decide

/-- ker(δ₀) consists of functions constant on edges. -/
theorem ker_coboundary0_constant_on_edges (α : ChainSpace0 cfg)
    (hα : coboundary0 cfg α = 0) :
    ∀ e : cfg.E, α (cfg.endpoints e).1 = α (cfg.endpoints e).2 := by
  intro e
  have := (mem_ker_coboundary0_iff cfg α).mp hα e
  rw [ZMod2_add_eq_zero_iff'] at this
  exact this

/-! ## Section 3: Even Cardinality Condition -/

/-- The "parity" of a 0-chain: sum of all vertex values. -/
noncomputable def chain0Parity (α : ChainSpace0 cfg) : ZMod 2 :=
  ∑ v : cfg.V, α v

/-- Helper: the boundary of a single edge sums to 0 (1 + 1 = 0). -/
theorem boundary1Single_sum_eq_zero (e : cfg.E) :
    ∑ v : cfg.V, boundary1Single cfg e v = 0 := by
  unfold boundary1Single
  have h_distinct := cfg.endpoints_distinct e
  have h1_mem : (cfg.endpoints e).1 ∈ (Finset.univ : Finset cfg.V) := Finset.mem_univ _
  rw [← Finset.insert_erase h1_mem]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  simp only [↓reduceIte]
  have h2_in_erase : (cfg.endpoints e).2 ∈ Finset.erase Finset.univ (cfg.endpoints e).1 := by
    rw [Finset.mem_erase]
    exact ⟨h_distinct.symm, Finset.mem_univ _⟩
  rw [← Finset.insert_erase h2_in_erase]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  have h2_val : (if (cfg.endpoints e).2 = (cfg.endpoints e).1 then (1 : ZMod 2)
      else if (cfg.endpoints e).2 = (cfg.endpoints e).2 then 1 else 0) = 1 := by
    simp [h_distinct.symm]
  rw [h2_val]
  have h_rest : ∑ x ∈ Finset.erase (Finset.erase Finset.univ (cfg.endpoints e).1)
      (cfg.endpoints e).2, (if x = (cfg.endpoints e).1 then (1 : ZMod 2)
      else if x = (cfg.endpoints e).2 then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [Finset.mem_erase] at hv
    have hv2 : v ≠ (cfg.endpoints e).2 := hv.1
    have hv' := hv.2
    rw [Finset.mem_erase] at hv'
    have hv1 : v ≠ (cfg.endpoints e).1 := hv'.1
    simp [hv1, hv2]
  rw [h_rest, add_zero]
  decide

/-- The boundary of a single edge has parity 0. -/
theorem boundary1Single_parity (e : cfg.E) :
    chain0Parity cfg (boundary1Single cfg e) = 0 := by
  unfold chain0Parity
  exact boundary1Single_sum_eq_zero cfg e

/-- The boundary of any 1-chain has parity 0.
    This is part (ii) of the exactness statement: im(∂₁) ⊆ {even parity chains}. -/
theorem boundary1_parity (γ : ChainSpace1 cfg) :
    chain0Parity cfg (boundary1 cfg γ) = 0 := by
  unfold chain0Parity boundary1
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  have h_factor : ∑ v : cfg.V, γ e * boundary1Single cfg e v =
      γ e * ∑ v : cfg.V, boundary1Single cfg e v := by
    rw [Finset.mul_sum]
  rw [h_factor]
  have h_parity := boundary1Single_sum_eq_zero cfg e
  rw [h_parity, mul_zero]

/-- The image of ∂₁ has even parity. -/
theorem boundary1_image_even_parity :
    ∀ γ : ChainSpace1 cfg, chain0Parity cfg (boundary1 cfg γ) = 0 :=
  boundary1_parity cfg

/-! ## Section 4: All-Ones Vector and Kernel of δ₀ -/

/-- The all-ones 0-chain: value 1 at every vertex. -/
def allOnes : ChainSpace0 cfg := fun _ => 1

/-- The zero 0-chain. -/
def zeroChain : ChainSpace0 cfg := fun _ => 0

/-- The all-ones vector is in ker(δ₀). -/
theorem allOnes_in_ker_coboundary0 :
    coboundary0 cfg (allOnes cfg) = 0 := by
  apply funext
  intro e
  simp only [coboundary0, allOnes, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  decide

/-- The zero vector is in ker(δ₀). -/
theorem zero_in_ker_coboundary0 :
    coboundary0 cfg (zeroChain cfg) = 0 := by
  apply funext
  intro e
  simp only [coboundary0, zeroChain, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, add_zero]

/-- In ZMod 2, every element is 0 or 1. -/
theorem ZMod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-! ## Section 5: Exactness Properties (One Direction Always Holds) -/

/-- im(∂₂) ⊆ ker(∂₁) always holds (from ∂₁ ∘ ∂₂ = 0).
    This is one direction of exactness at C₁. -/
theorem im_boundary2_subset_ker_boundary1 (β : ChainSpace2 cfg) :
    boundary1 cfg (boundary2 cfg β) = 0 := by
  have h := boundary_comp_boundary_eq_zero cfg
  have := LinearMap.ext_iff.mp h β
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
  exact this

/-- im(δ₀) ⊆ ker(δ₁) always holds (from δ₁ ∘ δ₀ = 0).
    This is one direction of dual exactness at C₁. -/
theorem im_coboundary0_subset_ker_coboundary1 (α : ChainSpace0 cfg) :
    coboundary1 cfg (coboundary0 cfg α) = 0 := by
  have h := coboundary_comp_coboundary_eq_zero cfg
  have := LinearMap.ext_iff.mp h α
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
  exact this

/-! ## Section 6: Connected Graph Kernel Characterization

For a connected graph, any element of ker(δ₀) must be constant on all vertices.
This is because α ∈ ker(δ₀) means α(v) = α(w) for any edge {v,w}, and
connectedness allows us to extend this to all pairs of vertices.

We model connectedness via a symmetric relation that is connected (any two vertices
are related by a sequence of edges).
-/

/-- Two vertices are adjacent if they share an edge. -/
def vertexAdjacent (v w : cfg.V) : Prop :=
  ∃ e : cfg.E, ((cfg.endpoints e).1 = v ∧ (cfg.endpoints e).2 = w) ∨
               ((cfg.endpoints e).1 = w ∧ (cfg.endpoints e).2 = v)

/-- The graph is vertex-connected if any two vertices can be connected
    by a sequence of adjacent vertices. This is the reflexive-transitive
    closure of the adjacency relation. -/
def IsConnectedGraph : Prop :=
  ∀ v w : cfg.V, Relation.ReflTransGen (vertexAdjacent cfg) v w

/-- If two vertices are adjacent and α ∈ ker(δ₀), then α(v) = α(w). -/
theorem ker_coboundary0_constant_on_adjacent (α : ChainSpace0 cfg)
    (hα : coboundary0 cfg α = 0) (v w : cfg.V) (hadj : vertexAdjacent cfg v w) :
    α v = α w := by
  obtain ⟨e, h⟩ := hadj
  have hconst := ker_coboundary0_constant_on_edges cfg α hα e
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact hconst
  · rw [← h1, ← h2]; exact hconst.symm

/-- For a connected graph, if α ∈ ker(δ₀), then α is constant on all vertices. -/
theorem ker_coboundary0_constant_of_connected (α : ChainSpace0 cfg)
    (hα : coboundary0 cfg α = 0) (hconn : IsConnectedGraph cfg) :
    ∀ v w : cfg.V, α v = α w := by
  intro v w
  have h := hconn v w
  induction h with
  | refl => rfl
  | tail _ hadj ih =>
    have hstep := ker_coboundary0_constant_on_adjacent cfg α hα _ _ hadj
    exact ih.trans hstep

/-- For a connected graph, ker(δ₀) = {0, 𝟙_V}.
    This is part (iii) of the exactness statement. -/
theorem ker_coboundary0_eq_zero_or_allOnes (α : ChainSpace0 cfg)
    (hα : coboundary0 cfg α = 0) (hconn : IsConnectedGraph cfg) :
    α = 0 ∨ α = allOnes cfg := by
  by_cases hV : Nonempty cfg.V
  · obtain ⟨v₀⟩ := hV
    have hconst := ker_coboundary0_constant_of_connected cfg α hα hconn
    have hall : ∀ v, α v = α v₀ := fun v => hconst v v₀
    rcases ZMod2_cases (α v₀) with h0 | h1
    · left
      funext v
      simp [hall v, h0]
    · right
      funext v
      simp [allOnes, hall v, h1]
  · left
    funext v
    exact absurd ⟨v⟩ hV

/-! ## Section 7: Cycle Generation Property

For exactness at C₁ (ker(∂₁) = im(∂₂)), we need the cycles to generate all cycles.
This means every element of ker(∂₁) can be written as a linear combination of
the boundary2Single images. This property is defined but not proven here as it
requires additional structure beyond GraphChainConfig.
-/

/-- The cycles C generate all cycles if every 1-chain in ker(∂₁) is in im(∂₂). -/
def CyclesGenerate : Prop :=
  ∀ γ : ChainSpace1 cfg, boundary1 cfg γ = 0 →
    ∃ β : ChainSpace2 cfg, boundary2 cfg β = γ

/-- If cycles generate all cycles, then exactness at C₁ holds:
    ker(∂₁) = im(∂₂). -/
theorem exactness_at_C1_of_generates
    (hgen : CyclesGenerate cfg) (γ : ChainSpace1 cfg) :
    boundary1 cfg γ = 0 ↔ ∃ β : ChainSpace2 cfg, boundary2 cfg β = γ := by
  constructor
  · exact hgen γ
  · intro ⟨β, hβ⟩
    rw [← hβ]
    exact im_boundary2_subset_ker_boundary1 cfg β

/-! ## Section 8: Helper Lemmas -/

/-- The chain complex identity in functional form. -/
theorem boundary_comp_boundary_apply (β : ChainSpace2 cfg) :
    boundary1 cfg (boundary2 cfg β) = 0 :=
  im_boundary2_subset_ker_boundary1 cfg β

/-- The dual chain complex identity in functional form. -/
theorem coboundary_comp_coboundary_apply (α : ChainSpace0 cfg) :
    coboundary1 cfg (coboundary0 cfg α) = 0 :=
  im_coboundary0_subset_ker_coboundary1 cfg α

/-- Parity is additive. -/
theorem chain0Parity_add (α β : ChainSpace0 cfg) :
    chain0Parity cfg (α + β) = chain0Parity cfg α + chain0Parity cfg β := by
  unfold chain0Parity
  rw [← Finset.sum_add_distrib]
  rfl

/-- Parity of zero chain is zero. -/
@[simp]
theorem chain0Parity_zero :
    chain0Parity cfg 0 = 0 := by
  unfold chain0Parity
  simp only [Pi.zero_apply, Finset.sum_const_zero]

/-- Parity of allOnes depends on vertex count parity. -/
theorem chain0Parity_allOnes :
    chain0Parity cfg (allOnes cfg) = (Fintype.card cfg.V : ZMod 2) := by
  unfold chain0Parity allOnes
  simp only [Finset.sum_const, Finset.card_univ, Nat.smul_one_eq_cast]

/-- The zero chain is in ker(∂₁). -/
@[simp]
theorem zero_in_ker_boundary1 :
    boundary1 cfg 0 = 0 := by
  simp only [map_zero]

/-- The zero chain is in ker(δ₁). -/
@[simp]
theorem zero_in_ker_coboundary1 :
    coboundary1 cfg 0 = 0 := by
  simp only [map_zero]

/-- Single cycle is in ker(∂₁). -/
theorem singleCycle_in_ker_boundary1 (c : cfg.C) :
    boundary1 cfg (boundary2Single cfg c) = 0 := by
  apply funext
  intro v
  simp only [boundary1, boundary2Single, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  have h_valid := cfg.cycles_valid c
  unfold isValidCycle' at h_valid
  specialize h_valid v
  have h_sum : ∑ e : cfg.E, (if e ∈ cfg.cycleEdges c then (1 : ZMod 2) else 0) *
      boundary1Single cfg e v =
      (Finset.filter (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
        (cfg.cycleEdges c)).card := by
    have h_term : ∀ e, (if e ∈ cfg.cycleEdges c then (1 : ZMod 2) else 0) *
        boundary1Single cfg e v =
        if e ∈ cfg.cycleEdges c ∧ ((cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
          then 1 else 0 := by
      intro e
      simp only [boundary1Single]
      by_cases he : e ∈ cfg.cycleEdges c
      · simp only [he, ↓reduceIte, one_mul, true_and]
        by_cases h1 : v = (cfg.endpoints e).1
        · simp [h1]
        · by_cases h2 : v = (cfg.endpoints e).2
          · have _hne : (cfg.endpoints e).1 ≠ (cfg.endpoints e).2 := cfg.endpoints_distinct e
            have this' : (cfg.endpoints e).2 = v := h2.symm
            simp only [h1, ↓reduceIte, this', or_true]
          · have hne1 : (cfg.endpoints e).1 ≠ v := fun h => h1 h.symm
            have hne2 : (cfg.endpoints e).2 ≠ v := fun h => h2 h.symm
            simp [h1, h2, hne1, hne2]
      · simp [he]
    simp_rw [h_term]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, Nat.smul_one_eq_cast]
    congr 2
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h_sum]
  exact (Nat.even_iff.mpr h_valid).natCast_zmod_two

/-- Linearity: boundary1 preserves addition. -/
theorem boundary1_add (γ₁ γ₂ : ChainSpace1 cfg) :
    boundary1 cfg (γ₁ + γ₂) = boundary1 cfg γ₁ + boundary1 cfg γ₂ := by
  exact map_add (boundary1 cfg) γ₁ γ₂

/-- Linearity: coboundary0 preserves addition. -/
theorem coboundary0_add (α₁ α₂ : ChainSpace0 cfg) :
    coboundary0 cfg (α₁ + α₂) = coboundary0 cfg α₁ + coboundary0 cfg α₂ := by
  exact map_add (coboundary0 cfg) α₁ α₂

end QEC
