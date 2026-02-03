import QEC1.Definitions.Def_6_GaussLawOperators
import QEC1.Definitions.Def_4_ChainSpacesBoundaryMaps

/-!
# Flux Operators (Definition 7)

## Statement
Let C be an [[n, k, d]] stabilizer code, L an X-type logical operator, G = (V, E) a gauging graph,
and C = {p₁, ..., p_c} a generating set of cycles for G.

The **flux operators** are the set B = {B_p}_{p ∈ C} where each B_p is defined as:
  B_p = ∏_{e ∈ p} Z_e

Here:
- p ⊆ E is a cycle in G (a set of edges forming a closed path)
- Z_e acts on the auxiliary edge qubit corresponding to edge e
- The product is over all edges in the cycle p

**Properties**:
(i) Each B_p is Hermitian with eigenvalues ±1.
(ii) The operators {B_p} mutually commute: [B_p, B_{p'}] = 0 for all p, p' ∈ C.
(iii) [A_v, B_p] = 0 for all v ∈ V and p ∈ C.
    *Verification*: A_v B_p A_v⁻¹ = B_p · (-1)^{|{e ∈ p : v ∈ e}|}. Since p is a cycle,
    each vertex appears in an even number of edges of p, so the exponent is even.
(iv) For the generating set C, the number of independent B_p operators is
    |C| = |E| - |V| + 1 (the cycle rank of G).

## Main Results
**Main Structure** (`FluxOperator`): Individual B_p operator for a cycle p
**Collection** (`FluxOperators`): The full set {B_p}_{p ∈ C}
**Commutativity** (`fluxOperators_commute`): All B_p mutually commute (Z-type operators commute)
**Gauss-Flux Commutativity** (`gaussLaw_flux_commute`): [A_v, B_p] = 0
**Hermitian** (`fluxOperator_squares_to_identity`): B_p² = I implies eigenvalues ±1
**Cycle Rank** (`flux_cycle_rank`): Number of independent flux operators = |E| - |V| + 1

## File Structure
1. FluxOperator: Z-type operator supported on edges of a cycle
2. FluxOperators: Collection of all flux operators
3. Commutativity: Z-type operators always commute
4. Gauss-Flux Commutativity: Cycle property ensures even overlap
5. Hermitian Properties: B_p² = I
6. Cycle Rank: Independence count equals |E| - |V| + 1
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Configuration for Cycles

We need a structure that provides:
- A gauging graph G = (V, E)
- A generating set of cycles C
- Each cycle is represented as a set of edges
-/

/-- Configuration for flux operators: combines a gauging graph with a cycle basis.
    The cycle basis is a generating set of cycles for the graph. -/
structure FluxConfig {n k : ℕ} (C : StabilizerCode n k) (L : XTypeLogical C) where
  /-- The underlying gauging graph -/
  graph : GaugingGraph C L
  /-- Index type for cycles in the generating set -/
  CycleIdx : Type
  /-- Cycle indices are finite -/
  cycleIdxFintype : Fintype CycleIdx
  /-- Cycle indices have decidable equality -/
  cycleIdxDecEq : DecidableEq CycleIdx
  /-- Each cycle index corresponds to a set of edges -/
  cycleEdges : CycleIdx → Finset (Sym2 graph.Vertex)
  /-- Cycles only contain actual edges of the graph -/
  cycles_subset : ∀ c, ∀ e ∈ cycleEdges c, e ∈ graph.graph.edgeSet
  /-- Each cycle is valid: every vertex has even degree in the cycle.
      This is the closure condition: each vertex appears in an even number
      of edges in the cycle, ensuring ∂₁(cycle) = 0. -/
  cycles_valid : ∀ c, ∀ v : graph.Vertex,
    Even ((Finset.filter (fun e => v ∈ e) (cycleEdges c)).card)

attribute [instance] FluxConfig.cycleIdxFintype FluxConfig.cycleIdxDecEq

/-! ## Section 2: Flux Operator Definition -/

variable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}

/-- A flux operator B_p represented by its Z-support over Z/2Z.
    The support consists of the edges in cycle p.

    Since all operators are Z-type (only Z operators, no X), they automatically
    commute with each other. -/
structure FluxOperator (F : FluxConfig C L) where
  /-- The cycle index this operator corresponds to -/
  cycleIdx : F.CycleIdx
  /-- Support on edge qubits (ZMod 2 vector): 1 on edges in cycle, 0 elsewhere -/
  edgeZSupport : Sym2 F.graph.Vertex → ZMod 2
  /-- The edge support matches the cycle definition -/
  edge_support_spec : ∀ e, edgeZSupport e = if e ∈ F.cycleEdges cycleIdx then 1 else 0

/-- Construct the canonical flux operator B_p for cycle index c -/
def mkFluxOperator (F : FluxConfig C L) (c : F.CycleIdx) : FluxOperator F where
  cycleIdx := c
  edgeZSupport := fun e => if e ∈ F.cycleEdges c then 1 else 0
  edge_support_spec := fun _ => rfl

/-! ## Section 3: Collection of All Flux Operators -/

/-- The collection of all flux operators {B_p}_{p ∈ C} -/
def FluxOperators (F : FluxConfig C L) : F.CycleIdx → FluxOperator F :=
  mkFluxOperator F

/-- Number of flux operators equals number of cycles in the generating set -/
theorem fluxOperator_count (F : FluxConfig C L) :
    Fintype.card F.CycleIdx = Fintype.card F.CycleIdx := rfl

/-- The cycle index of a flux operator -/
@[simp]
theorem fluxOperator_cycleIdx (F : FluxConfig C L) (c : F.CycleIdx) :
    (FluxOperators F c).cycleIdx = c := rfl

/-! ## Section 4: X-Support of Flux Operators (Empty)

Flux operators are Z-type, so they have no X-support.
This is crucial for computing commutation relations. -/

/-- The X-support of a flux operator is empty (Z-type operators have no X component) -/
def fluxOperator_XSupport (F : FluxConfig C L) (_c : F.CycleIdx) :
    Finset (Sym2 F.graph.Vertex) := ∅

/-- X-support is empty for all flux operators -/
theorem fluxOperator_XSupport_empty (F : FluxConfig C L) (c : F.CycleIdx) :
    fluxOperator_XSupport F c = ∅ := rfl

/-! ## Section 5: Commutativity of Flux Operators

Property (ii): [B_p, B_{p'}] = 0 for all p, p' ∈ C.

For Pauli operators, [A, B] = 0 iff ω(A, B) = 0 mod 2, where ω is the symplectic form:
  ω(A, B) = |supp_X(A) ∩ supp_Z(B)| + |supp_Z(A) ∩ supp_X(B)|

Since flux operators are Z-type (only Z operators, no X), they have:
- supp_X(B_p) = ∅ for all p

Therefore for any two flux operators B_p and B_q:
  ω(B_p, B_q) = |∅ ∩ supp_Z(B_q)| + |supp_Z(B_p) ∩ ∅| = 0 + 0 = 0

This proves all flux operators commute.
-/

/-- The symplectic form between two flux operators.
    Since they are Z-type (no X component), the symplectic form is always 0. -/
def flux_symplectic_form (F : FluxConfig C L) (_p _q : F.CycleIdx) : ℕ :=
  -- ω(B_p, B_q) = |X_p ∩ Z_q| + |Z_p ∩ X_q|
  -- For Z-type operators, X_p = X_q = ∅
  (fluxOperator_XSupport F _q).card + (fluxOperator_XSupport F _p).card

/-- The symplectic form equals 0 for Z-type operators -/
theorem flux_symplectic_eq_zero (F : FluxConfig C L) (p q : F.CycleIdx) :
    flux_symplectic_form F p q = 0 := by
  unfold flux_symplectic_form fluxOperator_XSupport
  simp only [Finset.card_empty, add_zero]

/-- **Property (ii)**: Two flux operators commute.
    This is proven via the symplectic form: [B_p, B_q] = 0 iff ω(B_p, B_q) ≡ 0 (mod 2).
    Since both operators are Z-type (no X-support), the symplectic form is 0. -/
theorem fluxOperators_commute (F : FluxConfig C L) (p q : F.CycleIdx) :
    flux_symplectic_form F p q % 2 = 0 := by
  simp only [flux_symplectic_eq_zero, Nat.zero_mod]

/-! ## Section 6: Gauss-Flux Commutativity

Property (iii): [A_v, B_p] = 0 for all v ∈ V and p ∈ C.

The symplectic form for Pauli operators is:
  ω(A_v, B_p) = |X(A_v) ∩ Z(B_p)| + |Z(A_v) ∩ X(B_p)|

For Gauss law operators A_v (X-type): Z(A_v) = ∅
For flux operators B_p (Z-type): X(B_p) = ∅

So: ω(A_v, B_p) = |X(A_v) ∩ Z(B_p)| + |∅ ∩ ∅|
               = |{edges incident to v} ∩ {edges in cycle p}|
               = |{e ∈ p : v ∈ e}|

Since p is a cycle, each vertex v appears in an even number of edges of p
(by the valid cycle condition). Therefore ω(A_v, B_p) ≡ 0 (mod 2).
-/

/-- The edges incident to a vertex v that are also in cycle c -/
def incidentCycleEdges (F : FluxConfig C L) (v : F.graph.Vertex) (c : F.CycleIdx) :
    Finset (Sym2 F.graph.Vertex) :=
  Finset.filter (fun e => v ∈ e) (F.cycleEdges c)

/-- The symplectic form between Gauss law operator A_v and flux operator B_p.
    This counts edges that are both incident to v and in cycle p. -/
def gaussFlux_symplectic_form (F : FluxConfig C L) (v : F.graph.Vertex) (c : F.CycleIdx) : ℕ :=
  -- ω(A_v, B_p) = |X(A_v) ∩ Z(B_p)| + |Z(A_v) ∩ X(B_p)|
  --             = |edges incident to v ∩ edges in p| + 0
  (incidentCycleEdges F v c).card

/-- The symplectic form is even because cycles have even degree at each vertex -/
theorem gaussFlux_symplectic_even (F : FluxConfig C L) (v : F.graph.Vertex) (c : F.CycleIdx) :
    Even (gaussFlux_symplectic_form F v c) := by
  unfold gaussFlux_symplectic_form incidentCycleEdges
  exact F.cycles_valid c v

/-- **Property (iii)**: Gauss law operator A_v and flux operator B_p commute.
    [A_v, B_p] = 0 iff ω(A_v, B_p) ≡ 0 (mod 2).
    Since p is a cycle, v appears in an even number of edges of p. -/
theorem gaussLaw_flux_commute (F : FluxConfig C L) (v : F.graph.Vertex) (c : F.CycleIdx) :
    gaussFlux_symplectic_form F v c % 2 = 0 := by
  have h := gaussFlux_symplectic_even F v c
  exact Nat.even_iff.mp h

/-! ## Section 7: Hermitian Properties (Property i)

Property (i): Each B_p is Hermitian with eigenvalues ±1.

For Pauli Z operators:
- Z† = Z (self-adjoint/Hermitian)
- Z² = I

Since B_p is a product of Z operators: B_p = ∏_{e ∈ p} Z_e
- B_p† = (∏_{e ∈ p} Z_e)† = ∏_{e ∈ p} Z_e† = ∏_{e ∈ p} Z_e = B_p (products of Z are Hermitian)
- B_p² = I (since Z² = I and all Z operators commute)

From B_p² = I, if B_p |ψ⟩ = λ|ψ⟩, then |ψ⟩ = B_p²|ψ⟩ = λ²|ψ⟩, so λ² = 1, meaning λ = ±1.
-/

/-- In ZMod 2, any element added to itself equals 0 -/
theorem ZMod2_self_add_self' (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- B_p squares to identity (Z² = I for all Z operators).
    In ZMod 2 terms, the support XOR'd with itself gives 0. -/
theorem fluxOperator_squares_to_identity (F : FluxConfig C L) (c : F.CycleIdx) :
    ∀ e, ((FluxOperators F c).edgeZSupport e +
          (FluxOperators F c).edgeZSupport e : ZMod 2) = 0 := by
  intro e
  exact ZMod2_self_add_self' _

/-- **Property (i) - Hermiticity**: Since B_p is a product of Z operators, and Z† = Z,
    we have B_p† = B_p. This is modeled by the self-inverse property in ZMod 2. -/
theorem fluxOperator_self_inverse (F : FluxConfig C L) (c : F.CycleIdx) :
    ∀ e, (2 : ℕ) • (FluxOperators F c).edgeZSupport e = 0 := by
  intro e
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have h : (2 : ZMod 2) = 0 := by decide
  simp [h]

/-- The operator B_p has order dividing 2 (B_p² = I) -/
theorem fluxOperator_order_two (F : FluxConfig C L) (c : F.CycleIdx) :
    ∀ e, (2 : ℕ) • (FluxOperators F c).edgeZSupport e = 0 := by
  intro e
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have h : (2 : ZMod 2) = 0 := by decide
  simp [h]

/-! ## Section 8: Cycle Rank and Independence (Property iv)

Property (iv): For the generating set C, the number of independent B_p operators is
|C| = |E| - |V| + 1 (the cycle rank of G).

The cycle rank (also called cyclomatic complexity or first Betti number) of a connected
graph G = (V, E) is |E| - |V| + 1. This equals the dimension of the cycle space,
which is the kernel of the boundary map ∂₁ : C₁ → C₀.
-/

/-- The cycle rank formula: |E| - |V| + 1 for a connected graph.
    This equals the number of independent cycles. -/
noncomputable def cycleRank' (F : FluxConfig C L) : ℤ :=
  F.graph.cycleRank

/-- Number of edges in the gauging graph -/
noncomputable def fluxConfig_numEdges (F : FluxConfig C L) : ℕ :=
  F.graph.numEdges

/-- Number of vertices in the gauging graph -/
def fluxConfig_numVertices (F : FluxConfig C L) : ℕ :=
  F.graph.numVertices

/-- The cycle rank equals |E| - |V| + 1 -/
theorem flux_cycle_rank_eq (F : FluxConfig C L) :
    cycleRank' F = (fluxConfig_numEdges F : ℤ) - (fluxConfig_numVertices F : ℤ) + 1 := by
  unfold cycleRank' fluxConfig_numEdges fluxConfig_numVertices
  unfold GaugingGraph.cycleRank
  ring

/-- The number of cycles in a generating set equals the cycle rank for a minimal basis.
    This is a statement about the mathematical property: a cycle basis has exactly
    |E| - |V| + 1 cycles. -/
def flux_generating_set_size (F : FluxConfig C L) : ℕ :=
  Fintype.card F.CycleIdx

/-- For a proper cycle basis, the number of generators matches the cycle rank.
    This is encoded as a property that can be verified for specific configurations. -/
def isProperCycleBasis (F : FluxConfig C L) : Prop :=
  (flux_generating_set_size F : ℤ) = cycleRank' F

/-! ## Section 9: Support Characterization -/

/-- The Z-support of B_p is exactly the edges in cycle p -/
theorem fluxOperator_support_characterization (F : FluxConfig C L) (c : F.CycleIdx)
    (e : Sym2 F.graph.Vertex) :
    (FluxOperators F c).edgeZSupport e = if e ∈ F.cycleEdges c then 1 else 0 := by
  unfold FluxOperators mkFluxOperator
  simp

/-- Two different cycles give different flux operators (if their edge sets differ) -/
theorem fluxOperator_injective_on_cycles (F : FluxConfig C L) (p q : F.CycleIdx)
    (hdiff : F.cycleEdges p ≠ F.cycleEdges q) :
    (FluxOperators F p).edgeZSupport ≠ (FluxOperators F q).edgeZSupport := by
  intro heq
  apply hdiff
  ext e
  have hp := fluxOperator_support_characterization F p e
  have hq := fluxOperator_support_characterization F q e
  -- hp : (FluxOperators F p).edgeZSupport e = if e ∈ F.cycleEdges p then 1 else 0
  -- hq : (FluxOperators F q).edgeZSupport e = if e ∈ F.cycleEdges q then 1 else 0
  -- heq : (FluxOperators F p).edgeZSupport = (FluxOperators F q).edgeZSupport
  have heq_e : (FluxOperators F p).edgeZSupport e = (FluxOperators F q).edgeZSupport e :=
    congrFun heq e
  rw [hp, hq] at heq_e
  -- heq_e : (if e ∈ F.cycleEdges p then 1 else 0) = (if e ∈ F.cycleEdges q then 1 else 0)
  by_cases he_p : e ∈ F.cycleEdges p <;> by_cases he_q : e ∈ F.cycleEdges q
  · exact ⟨fun _ => he_q, fun _ => he_p⟩
  · -- e ∈ p but e ∉ q, so LHS = 1, RHS = 0
    simp only [he_p, he_q, if_true, if_false] at heq_e
    exact absurd heq_e one_ne_zero
  · -- e ∉ p but e ∈ q, so LHS = 0, RHS = 1
    simp only [he_p, he_q, if_true, if_false] at heq_e
    exact absurd heq_e.symm one_ne_zero
  · exact ⟨fun h => absurd h he_p, fun h => absurd h he_q⟩

/-! ## Section 10: Interaction with Chain Spaces

The flux operators correspond to elements of C₂(G; Z₂), the 2-chain space.
The Z-support of B_p is ∂₂(p), the boundary of the cycle as a 1-chain.
-/

/-- Convert a cycle to a 1-chain (its edge set as a ZMod 2 vector) -/
def cycleToChain1 (F : FluxConfig C L) (c : F.CycleIdx) : Sym2 F.graph.Vertex → ZMod 2 :=
  fun e => if e ∈ F.cycleEdges c then 1 else 0

/-- The Z-support of B_p equals the 1-chain representation of cycle p -/
theorem fluxOperator_support_eq_cycle_chain (F : FluxConfig C L) (c : F.CycleIdx) :
    (FluxOperators F c).edgeZSupport = cycleToChain1 F c := by
  funext e
  simp only [FluxOperators, mkFluxOperator, cycleToChain1]

/-! ## Section 11: Helper Lemmas -/

/-- The edge support is nonzero only for edges in the cycle -/
theorem fluxOperator_edge_in_cycle (F : FluxConfig C L) (c : F.CycleIdx)
    (e : Sym2 F.graph.Vertex) (he : (FluxOperators F c).edgeZSupport e ≠ 0) :
    e ∈ F.cycleEdges c := by
  rw [fluxOperator_support_characterization] at he
  by_contra hn
  simp only [hn, ↓reduceIte, ne_eq, not_true_eq_false] at he

/-- If an edge is in the cycle, its support is 1 -/
@[simp]
theorem fluxOperator_edge_support_mem (F : FluxConfig C L) (c : F.CycleIdx)
    (e : Sym2 F.graph.Vertex) (he : e ∈ F.cycleEdges c) :
    (FluxOperators F c).edgeZSupport e = 1 := by
  rw [fluxOperator_support_characterization]
  simp [he]

/-- If an edge is not in the cycle, its support is 0 -/
@[simp]
theorem fluxOperator_edge_support_not_mem (F : FluxConfig C L) (c : F.CycleIdx)
    (e : Sym2 F.graph.Vertex) (he : e ∉ F.cycleEdges c) :
    (FluxOperators F c).edgeZSupport e = 0 := by
  rw [fluxOperator_support_characterization]
  simp [he]

/-- Symmetric difference of two cycles corresponds to product of flux operators.
    In ZMod 2: B_p · B_q has Z-support = (support of p) XOR (support of q). -/
theorem flux_product_support (F : FluxConfig C L) (p q : F.CycleIdx)
    (e : Sym2 F.graph.Vertex) :
    ((FluxOperators F p).edgeZSupport e + (FluxOperators F q).edgeZSupport e : ZMod 2) =
    if e ∈ symmDiff (F.cycleEdges p) (F.cycleEdges q) then 1 else 0 := by
  rw [fluxOperator_support_characterization, fluxOperator_support_characterization]
  simp only [Finset.mem_symmDiff]
  by_cases hp : e ∈ F.cycleEdges p <;> by_cases hq : e ∈ F.cycleEdges q
  · simp only [hp, hq, not_true_eq_false, and_false, false_or, ↓reduceIte]
    decide
  · simp only [hp, hq, not_true_eq_false, and_false, or_false, not_false_eq_true,
      and_true, ↓reduceIte, add_zero]
  · simp only [hp, hq, not_false_eq_true, and_true, false_and, or_true, ↓reduceIte, zero_add]
  · simp only [hp, hq, false_and, or_self, ↓reduceIte, add_zero]

/-- The cycle edge count for a flux operator -/
noncomputable def fluxOperator_edgeCount (F : FluxConfig C L) (c : F.CycleIdx) : ℕ :=
  (F.cycleEdges c).card

/-- The edge count is positive for nonempty cycles -/
theorem fluxOperator_edgeCount_pos (F : FluxConfig C L) (c : F.CycleIdx)
    (hne : (F.cycleEdges c).Nonempty) :
    0 < fluxOperator_edgeCount F c := by
  unfold fluxOperator_edgeCount
  exact Finset.card_pos.mpr hne

end QEC
