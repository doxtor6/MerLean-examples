import QEC1.Definitions.Def_3_GaugingGraph
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Chain Spaces and Boundary Maps (Definition 4)

## Statement
Let $G = (V, E)$ be a finite connected graph and let $C$ be a chosen collection of generating
cycles for $G$.

We define the following $\mathbb{Z}_2$-vector spaces and linear maps:

(i) **Chain spaces**:
- $C_0(G; \mathbb{Z}_2) = \mathbb{Z}_2^V$ is the space of **0-chains** (formal sums of vertices)
- $C_1(G; \mathbb{Z}_2) = \mathbb{Z}_2^E$ is the space of **1-chains** (formal sums of edges)
- $C_2(G; \mathbb{Z}_2) = \mathbb{Z}_2^C$ is the space of **2-chains** (formal sums of cycles)

We identify a subset $S \subseteq V$ with the 0-chain $\sum_{v \in S} v \in C_0$.

(ii) **Boundary map** $\partial_1: C_1(G; \mathbb{Z}_2) \to C_0(G; \mathbb{Z}_2)$ is the
$\mathbb{Z}_2$-linear map defined on basis elements by:
$$\partial_1(e) = v + v'$$
where $e = \{v, v'\}$ is an edge with endpoints $v, v'$.

(iii) **Second boundary map** $\partial_2: C_2(G; \mathbb{Z}_2) \to C_1(G; \mathbb{Z}_2)$
is defined by:
$$\partial_2(c) = \sum_{e \in c} e$$
for a cycle $c$ viewed as a set of edges.

(iv) **Coboundary maps** are the transposes:
- $\delta_0 = \partial_1^T: C_0(G; \mathbb{Z}_2) \to C_1(G; \mathbb{Z}_2)$
- $\delta_1 = \partial_2^T: C_1(G; \mathbb{Z}_2) \to C_2(G; \mathbb{Z}_2)$

(v) **Key identity**: $\partial_1 \circ \partial_2 = 0$, i.e., the boundary of a cycle is zero.

## Main Results
**Main Definitions**:
- `ChainSpace0`, `ChainSpace1`, `ChainSpace2`: The chain spaces as ZMod 2 vector spaces
- `boundary1`, `boundary2`: The boundary maps
- `coboundary0`, `coboundary1`: The coboundary maps (transposes)

**Main Theorem** (`boundary_comp_boundary_eq_zero`): ∂₁ ∘ ∂₂ = 0

## File Structure
1. Chain Space Definitions: Vector spaces over ZMod 2
2. Boundary Map ∂₁: Edges to vertices
3. Boundary Map ∂₂: Cycles to edges
4. Coboundary Maps: Transposes δ₀, δ₁
5. Chain Complex Identity: ∂₁ ∘ ∂₂ = 0
6. Helper Lemmas: Basic properties
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Chain Space Definitions -/

/-- A valid cycle: every vertex has even degree (even number of incident edges).
    This is the defining property that makes ∂₁(cycle) = 0. -/
def isValidCycle' {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E]
    (endpoints : E → V × V) (edgeSet : Finset E) : Prop :=
  ∀ v : V, (Finset.filter (fun e =>
    (endpoints e).1 = v ∨ (endpoints e).2 = v) edgeSet).card % 2 = 0

/-- Configuration for a graph with a cycle basis.
    This bundles a finite vertex set V, finite edge set E, and a cycle index set C.
    IMPORTANTLY: The cycleEdges function must produce valid cycles (closed walks),
    which is enforced by the cycles_valid field. -/
structure GraphChainConfig where
  /-- The vertex type -/
  V : Type
  /-- The edge type -/
  E : Type
  /-- The cycle index type -/
  C : Type
  /-- Vertices are finite -/
  vFintype : Fintype V
  /-- Edges are finite -/
  eFintype : Fintype E
  /-- Cycles are finite -/
  cFintype : Fintype C
  /-- Vertices have decidable equality -/
  vDecEq : DecidableEq V
  /-- Edges have decidable equality -/
  eDecEq : DecidableEq E
  /-- Cycles have decidable equality -/
  cDecEq : DecidableEq C
  /-- Each edge has two distinct endpoints -/
  endpoints : E → V × V
  /-- Endpoints are distinct (simple graph condition) -/
  endpoints_distinct : ∀ e, (endpoints e).1 ≠ (endpoints e).2
  /-- Each cycle is a set of edges -/
  cycleEdges : C → Finset E
  /-- All cycles are valid: every vertex has even degree in the cycle.
      This is the key property ensuring ∂₁ ∘ ∂₂ = 0.
      This corresponds to the mathematical requirement that C is a collection
      of generating cycles for G (closed walks). -/
  cycles_valid : ∀ c, isValidCycle' endpoints (cycleEdges c)

attribute [instance] GraphChainConfig.vFintype GraphChainConfig.eFintype
  GraphChainConfig.cFintype GraphChainConfig.vDecEq GraphChainConfig.eDecEq
  GraphChainConfig.cDecEq

variable (cfg : GraphChainConfig)

/-- The 0-chain space C₀(G; ℤ₂) = ℤ₂^V -/
abbrev ChainSpace0 := cfg.V → ZMod 2

/-- The 1-chain space C₁(G; ℤ₂) = ℤ₂^E -/
abbrev ChainSpace1 := cfg.E → ZMod 2

/-- The 2-chain space C₂(G; ℤ₂) = ℤ₂^C -/
abbrev ChainSpace2 := cfg.C → ZMod 2

/-- C₀ is a ZMod 2 module (vector space) -/
instance : Module (ZMod 2) (ChainSpace0 cfg) := Pi.module _ _ _

/-- C₁ is a ZMod 2 module (vector space) -/
instance : Module (ZMod 2) (ChainSpace1 cfg) := Pi.module _ _ _

/-- C₂ is a ZMod 2 module (vector space) -/
instance : Module (ZMod 2) (ChainSpace2 cfg) := Pi.module _ _ _

/-! ## Section 2: Subset to Chain Identification -/

/-- Convert a subset S ⊆ V to a 0-chain: the characteristic function as ZMod 2 values.
    This identifies a subset with the formal sum ∑_{v ∈ S} v. -/
def subsetToChain0 (S : Finset cfg.V) : ChainSpace0 cfg :=
  fun v => if v ∈ S then 1 else 0

/-- Convert a subset S ⊆ E to a 1-chain -/
def subsetToChain1 (S : Finset cfg.E) : ChainSpace1 cfg :=
  fun e => if e ∈ S then 1 else 0

/-- The indicator function for a single vertex -/
def singleVertex (v : cfg.V) : ChainSpace0 cfg :=
  fun w => if w = v then 1 else 0

/-- The indicator function for a single edge -/
def singleEdge (e : cfg.E) : ChainSpace1 cfg :=
  fun f => if f = e then 1 else 0

/-- The indicator function for a single cycle -/
def singleCycle (c : cfg.C) : ChainSpace2 cfg :=
  fun d => if d = c then 1 else 0

/-! ## Section 3: Boundary Map ∂₁ : C₁ → C₀ -/

/-- The boundary of a single edge: ∂₁(e) = v + v' where e = {v, v'}.
    This returns the 0-chain with value 1 at both endpoints of e. -/
def boundary1Single (e : cfg.E) : ChainSpace0 cfg :=
  let (v, v') := cfg.endpoints e
  fun w => if w = v then 1 else (if w = v' then 1 else 0)

/-- The first boundary map ∂₁: C₁(G; ℤ₂) → C₀(G; ℤ₂).
    For a 1-chain α, ∂₁(α) = ∑_e α(e) · ∂₁(e). -/
noncomputable def boundary1 : ChainSpace1 cfg →ₗ[ZMod 2] ChainSpace0 cfg where
  toFun := fun α =>
    fun v => ∑ e : cfg.E, α e * (boundary1Single cfg e v)
  map_add' := by
    intro α β
    funext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr 1
    ext e
    ring
  map_smul' := by
    intro r α
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    congr 1
    ext e
    ring

/-! ## Section 4: Boundary Map ∂₂ : C₂ → C₁ -/

/-- The boundary of a single cycle: ∂₂(c) = ∑_{e ∈ c} e.
    This returns the 1-chain that is 1 on edges in the cycle. -/
def boundary2Single (c : cfg.C) : ChainSpace1 cfg :=
  fun e => if e ∈ cfg.cycleEdges c then 1 else 0

/-- The second boundary map ∂₂: C₂(G; ℤ₂) → C₁(G; ℤ₂).
    For a 2-chain β, ∂₂(β) = ∑_c β(c) · ∂₂(c). -/
noncomputable def boundary2 : ChainSpace2 cfg →ₗ[ZMod 2] ChainSpace1 cfg where
  toFun := fun β =>
    fun e => ∑ c : cfg.C, β c * (boundary2Single cfg c e)
  map_add' := by
    intro α β
    funext e
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr 1
    ext c
    ring
  map_smul' := by
    intro r α
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    congr 1
    ext c
    ring

/-! ## Section 5: Chain Complex Identity ∂₁ ∘ ∂₂ = 0 -/

/-- A cycle is a valid cycle: the boundary (sum of vertices with odd degree) is zero.
    A valid cycle has the property that every vertex is incident to an even number of edges. -/
def isValidCycle (edgeSet : Finset cfg.E) : Prop :=
  ∀ v : cfg.V, (Finset.filter (fun e =>
    (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v) edgeSet).card % 2 = 0

/-- The key chain complex identity: ∂₁ ∘ ∂₂ = 0.
    This holds unconditionally because GraphChainConfig requires all cycles to be valid
    (every vertex has even degree in any cycle). The original mathematical statement
    asserts this as a property of cycles in a graph. -/
theorem boundary_comp_boundary_eq_zero :
    boundary1 cfg ∘ₗ boundary2 cfg = 0 := by
  apply LinearMap.ext
  intro γ
  apply funext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [boundary1, boundary2, LinearMap.coe_mk, AddHom.coe_mk]
  -- We want to show: ∑_e (∑_c γ(c) · 1[e ∈ c]) · ∂₁(e)(v) = 0
  -- Swap the sums
  have h_swap : ∑ e : cfg.E,
      (∑ c : cfg.C, γ c * boundary2Single cfg c e) * boundary1Single cfg e v =
      ∑ c : cfg.C, ∑ e : cfg.E,
        γ c * boundary2Single cfg c e * boundary1Single cfg e v := by
    rw [Finset.sum_comm]
    congr 1
    ext e
    rw [Finset.sum_mul]
  rw [h_swap]
  -- Now: ∑_c (∑_e γ(c) · 1[e ∈ c] · ∂₁(e)(v))
  apply Finset.sum_eq_zero
  intro c _
  simp only [boundary2Single, boundary1Single]
  by_cases hγ : γ c = 0
  · simp only [hγ, zero_mul]
    apply Finset.sum_eq_zero
    intro _ _
    ring
  · -- When γ c ≠ 0, we need the inner sum to be 0
    have h_valid := cfg.cycles_valid c
    unfold isValidCycle' at h_valid
    specialize h_valid v
    -- The inner sum counts edges in c incident to v
    -- First, show the sum equals γ c * (cardinality of filtered set)
    -- The inner sum counts edges in c incident to v
    -- We show the sum equals γ c * (cardinality of filtered set)
    have h_simplify : ∑ e : cfg.E, γ c * (if e ∈ cfg.cycleEdges c then 1 else 0) *
        (if v = (cfg.endpoints e).1 then 1 else if v = (cfg.endpoints e).2 then 1 else 0) =
        γ c * (Finset.filter (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
          (cfg.cycleEdges c)).card := by
      -- Extract γ c from the sum
      have h_eq : ∑ e : cfg.E, γ c * (if e ∈ cfg.cycleEdges c then 1 else 0) *
          (if v = (cfg.endpoints e).1 then 1 else if v = (cfg.endpoints e).2 then 1 else 0) =
          γ c * ∑ e : cfg.E, (if e ∈ cfg.cycleEdges c then 1 else 0) *
            (if v = (cfg.endpoints e).1 then 1 else if v = (cfg.endpoints e).2 then 1 else 0) := by
        rw [Finset.mul_sum]
        congr 1
        ext e
        ring
      rw [h_eq]
      congr 1
      -- The inner sum equals the cardinality
      have h_card : (∑ e : cfg.E, (if e ∈ cfg.cycleEdges c then (1 : ZMod 2) else 0) *
          (if v = (cfg.endpoints e).1 then 1 else if v = (cfg.endpoints e).2 then 1 else 0)) =
          (Finset.filter (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
            (cfg.cycleEdges c)).card := by
        -- Transform the product form to indicator form
        have h_eq3 : ∀ e, (if e ∈ cfg.cycleEdges c then (1 : ZMod 2) else 0) *
            (if v = (cfg.endpoints e).1 then 1
              else if v = (cfg.endpoints e).2 then 1 else 0) =
            if e ∈ cfg.cycleEdges c ∧
              ((cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v) then 1 else 0 := by
          intro e
          by_cases he : e ∈ cfg.cycleEdges c
          · simp only [he, ↓reduceIte, one_mul, true_and]
            by_cases h1 : v = (cfg.endpoints e).1
            · simp only [h1, eq_comm, true_or, ↓reduceIte]
            · by_cases h2 : v = (cfg.endpoints e).2
              · -- Goal: 1 = if _ then 1 else 1  which is trivially true
                have heq : (cfg.endpoints e).2 = v := h2.symm
                simp only [h1, heq, or_true, ↓reduceIte]
              · have hne1 : (cfg.endpoints e).1 ≠ v := fun h => h1 h.symm
                have hne2 : (cfg.endpoints e).2 ≠ v := fun h => h2 h.symm
                simp only [h1, h2, hne1, hne2, or_self, ↓reduceIte]
          · simp only [he, ↓reduceIte, zero_mul, false_and]
        simp_rw [h_eq3]
        -- The sum of indicator is the card of filter
        have h_sum_eq : ∑ e : cfg.E, (if e ∈ cfg.cycleEdges c ∧
            ((cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v) then (1 : ZMod 2) else 0) =
            (Finset.filter (fun e => e ∈ cfg.cycleEdges c ∧
              ((cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)) Finset.univ).card := by
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const, Nat.smul_one_eq_cast]
        rw [h_sum_eq]
        -- Simplify the filter to match
        have h_filter_eq : Finset.filter (fun e => e ∈ cfg.cycleEdges c ∧
            ((cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)) Finset.univ =
            Finset.filter (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
              (cfg.cycleEdges c) := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
        rw [h_filter_eq]
      exact h_card
    rw [h_simplify]
    -- Now use validity: the cardinality mod 2 = 0
    have h_even : Even (Finset.filter (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
        (cfg.cycleEdges c)).card := by
      rw [Nat.even_iff]
      exact h_valid
    have h_zmod : ((Finset.filter (fun e => (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v)
        (cfg.cycleEdges c)).card : ZMod 2) = 0 := by
      exact h_even.natCast_zmod_two
    rw [h_zmod, mul_zero]

/-! ## Section 6: Coboundary Maps (Transposes) -/

/-- The inner product (pairing) for chains: ⟨α, β⟩ = ∑_i α_i β_i in ZMod 2.
    This is the standard inner product on Z₂^n. -/
noncomputable def chainPairing {X : Type} [Fintype X] [DecidableEq X]
    (α β : X → ZMod 2) : ZMod 2 :=
  ∑ x : X, α x * β x

/-- Coboundary map δ₀ = ∂₁ᵀ : C₀ → C₁.
    For a 0-chain α (vertex function), δ₀(α) is the 1-chain where
    δ₀(α)(e) = α(v) + α(v') for edge e = {v, v'}.

    Equivalently, δ₀(v) = sum of edges incident to v. -/
noncomputable def coboundary0 : ChainSpace0 cfg →ₗ[ZMod 2] ChainSpace1 cfg where
  toFun := fun α =>
    fun e =>
      let (v, v') := cfg.endpoints e
      α v + α v'
  map_add' := by
    intro α β
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro r α
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Coboundary map δ₁ = ∂₂ᵀ : C₁ → C₂.
    For a 1-chain α (edge function), δ₁(α) is the 2-chain where
    δ₁(α)(c) = ∑_{e ∈ c} α(e).

    Equivalently, δ₁(e) = sum of cycles containing e. -/
noncomputable def coboundary1 : ChainSpace1 cfg →ₗ[ZMod 2] ChainSpace2 cfg where
  toFun := fun α =>
    fun c => ∑ e ∈ cfg.cycleEdges c, α e
  map_add' := by
    intro α β
    funext c
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' := by
    intro r α
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

/-! ## Section 7: Transpose Property -/

/-- δ₀ is indeed the transpose of ∂₁: ⟨∂₁(β), α⟩ = ⟨β, δ₀(α)⟩ for all 0-chains α and 1-chains β -/
theorem coboundary0_transpose (α : ChainSpace0 cfg) (β : ChainSpace1 cfg) :
    chainPairing (boundary1 cfg β) α = chainPairing β (coboundary0 cfg α) := by
  unfold chainPairing boundary1 coboundary0
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS: ∑_v (∑_e β(e) · ∂₁(e)(v)) · α(v)
  -- RHS: ∑_e β(e) · (α(v) + α(v')) where e = {v, v'}
  have h_swap : ∑ x : cfg.V, (∑ e : cfg.E, β e * boundary1Single cfg e x) * α x =
      ∑ e : cfg.E, ∑ x : cfg.V, β e * boundary1Single cfg e x * α x := by
    rw [Finset.sum_comm]
    congr 1
    ext x
    rw [Finset.sum_mul]
  rw [h_swap]
  congr 1
  ext e
  simp only [boundary1Single]
  -- Need to show: ∑_v β(e) * (if v = v₁ then 1 else if v = v₂ then 1 else 0) * α(v)
  --             = β(e) * (α(v₁) + α(v₂))
  have h_sum : ∑ v : cfg.V, β e * (if v = (cfg.endpoints e).1 then 1
      else if v = (cfg.endpoints e).2 then 1 else 0) * α v =
      β e * α (cfg.endpoints e).1 + β e * α (cfg.endpoints e).2 := by
    have h_ne : (cfg.endpoints e).1 ≠ (cfg.endpoints e).2 := cfg.endpoints_distinct e
    -- Extract the first vertex term
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cfg.endpoints e).1)]
    simp only [↓reduceIte, mul_one]
    -- Extract the second vertex term from remaining sum
    have h2_mem : (cfg.endpoints e).2 ∈ Finset.erase Finset.univ (cfg.endpoints e).1 := by
      rw [Finset.mem_erase]
      exact ⟨h_ne.symm, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ h2_mem]
    have h_v2_simp : β e * (if (cfg.endpoints e).2 = (cfg.endpoints e).1 then (1 : ZMod 2)
        else if (cfg.endpoints e).2 = (cfg.endpoints e).2 then 1 else 0) *
        α (cfg.endpoints e).2 = β e * α (cfg.endpoints e).2 := by
      simp only [h_ne.symm, ↓reduceIte, mul_one]
    rw [h_v2_simp]
    -- The rest of the sum is zero
    have h_rest : ∑ x ∈ Finset.erase (Finset.erase Finset.univ (cfg.endpoints e).1)
        (cfg.endpoints e).2, β e * (if x = (cfg.endpoints e).1 then 1
        else if x = (cfg.endpoints e).2 then 1 else 0) * α x = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [Finset.mem_erase] at hv
      have hv_ne2 : v ≠ (cfg.endpoints e).2 := hv.1
      have hv_mem : v ∈ Finset.erase Finset.univ (cfg.endpoints e).1 := hv.2
      rw [Finset.mem_erase] at hv_mem
      have hv_ne1 : v ≠ (cfg.endpoints e).1 := hv_mem.1
      simp only [hv_ne1, hv_ne2, ↓reduceIte, mul_zero, zero_mul]
    rw [h_rest, add_zero]
  rw [h_sum]
  ring

/-- δ₁ is indeed the transpose of ∂₂: ⟨∂₂(γ), β⟩ = ⟨γ, δ₁(β)⟩ for all 1-chains β and 2-chains γ -/
theorem coboundary1_transpose (β : ChainSpace1 cfg) (γ : ChainSpace2 cfg) :
    chainPairing (boundary2 cfg γ) β = chainPairing γ (coboundary1 cfg β) := by
  unfold chainPairing boundary2 coboundary1
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS: ∑_e (∑_c γ(c) · 1[e ∈ c]) · β(e)
  -- RHS: ∑_c γ(c) · (∑_{e ∈ c} β(e))
  have h_swap : ∑ x : cfg.E, (∑ c : cfg.C, γ c * boundary2Single cfg c x) * β x =
      ∑ c : cfg.C, ∑ x : cfg.E, γ c * boundary2Single cfg c x * β x := by
    rw [Finset.sum_comm]
    congr 1
    ext x
    rw [Finset.sum_mul]
  rw [h_swap]
  congr 1
  ext c
  simp only [boundary2Single]
  -- Need: ∑_e γ(c) · (if e ∈ c then 1 else 0) · β(e) = γ(c) · ∑_{e ∈ c} β(e)
  have h_eq : ∑ e : cfg.E, γ c * (if e ∈ cfg.cycleEdges c then 1 else 0) * β e =
      γ c * ∑ e ∈ cfg.cycleEdges c, β e := by
    -- Transform to filter sum
    have h_transform : ∀ e, γ c * (if e ∈ cfg.cycleEdges c then (1 : ZMod 2) else 0) * β e =
        if e ∈ cfg.cycleEdges c then γ c * β e else 0 := by
      intro e
      by_cases he : e ∈ cfg.cycleEdges c
      · simp only [he, ↓reduceIte, mul_one]
      · simp only [he, ↓reduceIte, mul_zero, zero_mul]
    simp_rw [h_transform]
    -- Now sum over univ with filter = sum over subset
    have h_sum_filter : ∑ e : cfg.E, (if e ∈ cfg.cycleEdges c then γ c * β e else 0) =
        ∑ e ∈ cfg.cycleEdges c, γ c * β e := by
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h_sum_filter, Finset.mul_sum]
  rw [h_eq]

/-! ## Section 8: Coboundary on Basis Elements -/

/-- δ₀ applied to a single vertex gives the sum of incident edges -/
theorem coboundary0_single_vertex (v : cfg.V) :
    coboundary0 cfg (singleVertex cfg v) =
    fun e => if (cfg.endpoints e).1 = v ∨ (cfg.endpoints e).2 = v then 1 else 0 := by
  funext e
  simp only [coboundary0, singleVertex, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h1 : (cfg.endpoints e).1 = v
  · simp only [h1, ↓reduceIte, true_or]
    by_cases h2 : (cfg.endpoints e).2 = v
    · -- Both endpoints equal v, but they must be distinct
      exfalso
      have := cfg.endpoints_distinct e
      rw [h1, h2] at this
      exact this rfl
    · simp only [h2, ↓reduceIte, add_zero]
  · simp only [h1, ↓reduceIte, false_or, zero_add]

/-- δ₁ applied to a single edge gives the sum of cycles containing that edge -/
theorem coboundary1_single_edge (e : cfg.E) :
    coboundary1 cfg (singleEdge cfg e) =
    fun c => if e ∈ cfg.cycleEdges c then 1 else 0 := by
  funext c
  simp only [coboundary1, singleEdge, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases he : e ∈ cfg.cycleEdges c
  · simp only [he, ↓reduceIte]
    rw [Finset.sum_eq_single e]
    · simp only [↓reduceIte]
    · intro f hf hne
      simp only [hne, ↓reduceIte]
    · intro hne
      exact absurd he hne
  · simp only [he, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro f hf
    by_cases hfe : f = e
    · exact absurd (hfe ▸ hf) he
    · simp only [hfe, ↓reduceIte]

/-! ## Section 9: Helper Lemmas -/

/-- The zero chain in C₀ -/
@[simp]
theorem zero_chain0 : (0 : ChainSpace0 cfg) = fun _ => 0 := rfl

/-- The zero chain in C₁ -/
@[simp]
theorem zero_chain1 : (0 : ChainSpace1 cfg) = fun _ => 0 := rfl

/-- The zero chain in C₂ -/
@[simp]
theorem zero_chain2 : (0 : ChainSpace2 cfg) = fun _ => 0 := rfl

/-- Boundary of zero is zero -/
@[simp]
theorem boundary1_zero : boundary1 cfg 0 = 0 := by
  simp only [map_zero]

/-- Boundary of zero is zero -/
@[simp]
theorem boundary2_zero : boundary2 cfg 0 = 0 := by
  simp only [map_zero]

/-- Coboundary of zero is zero -/
@[simp]
theorem coboundary0_zero : coboundary0 cfg 0 = 0 := by
  simp only [map_zero]

/-- Coboundary of zero is zero -/
@[simp]
theorem coboundary1_zero : coboundary1 cfg 0 = 0 := by
  simp only [map_zero]

/-- In ZMod 2, x + x = 0 -/
theorem ZMod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- The empty subset corresponds to the zero 0-chain -/
@[simp]
theorem subsetToChain0_empty : subsetToChain0 cfg ∅ = 0 := by
  funext v
  simp only [subsetToChain0, Finset.notMem_empty, ↓reduceIte, Pi.zero_apply]

/-- The empty subset corresponds to the zero 1-chain -/
@[simp]
theorem subsetToChain1_empty : subsetToChain1 cfg ∅ = 0 := by
  funext e
  simp only [subsetToChain1, Finset.notMem_empty, ↓reduceIte, Pi.zero_apply]

/-- Symmetric difference of subsets corresponds to addition of chains -/
theorem subsetToChain0_symmDiff (S T : Finset cfg.V) :
    subsetToChain0 cfg (symmDiff S T) = subsetToChain0 cfg S + subsetToChain0 cfg T := by
  funext v
  simp only [subsetToChain0, Pi.add_apply, Finset.mem_symmDiff]
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T
  · simp only [hS, hT, not_true_eq_false, and_false, false_or, ↓reduceIte]
    decide
  · simp only [hS, hT, not_true_eq_false, and_false, or_false, not_false_eq_true,
      and_true, ↓reduceIte, add_zero]
  · simp only [hS, hT, not_false_eq_true, and_true, false_and, or_true, ↓reduceIte, zero_add]
  · simp only [hS, hT, false_and, or_self, ↓reduceIte, add_zero]

/-- Symmetric difference of edge subsets corresponds to addition of chains -/
theorem subsetToChain1_symmDiff (S T : Finset cfg.E) :
    subsetToChain1 cfg (symmDiff S T) = subsetToChain1 cfg S + subsetToChain1 cfg T := by
  funext e
  simp only [subsetToChain1, Pi.add_apply, Finset.mem_symmDiff]
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T
  · simp only [hS, hT, not_true_eq_false, and_false, false_or, ↓reduceIte]
    decide
  · simp only [hS, hT, not_true_eq_false, and_false, or_false, not_false_eq_true,
      and_true, ↓reduceIte, add_zero]
  · simp only [hS, hT, not_false_eq_true, and_true, false_and, or_true, ↓reduceIte, zero_add]
  · simp only [hS, hT, false_and, or_self, ↓reduceIte, add_zero]

end QEC
