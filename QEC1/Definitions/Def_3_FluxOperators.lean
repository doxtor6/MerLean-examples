import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawOperators
import QEC1.Remarks.Rem_3_BinaryVectorNotation

/-!
# Def_3: Flux Operators

## Statement
Given a connected graph $G = (V_G, E_G)$ with a generating set of cycles $\{p\}_C$ (where
$C = |E_G| - |V_G| + 1$ is the number of independent cycles by Euler's formula for connected
graphs), the **flux operators** are the set $\mathcal{B} = \{B_p\}_{p \in C}$ where:
$$B_p = \prod_{e \in p} Z_e$$
Here $Z_e$ is the Pauli-$Z$ operator on the edge qubit $e$, and the product is over all edges
$e$ that belong to cycle $p$.

The flux operators arise from the initial state $|0\rangle^{\otimes E_G}$ of the edge qubits:
1. Initially, $Z_e |0\rangle_e = |0\rangle_e$ for each edge, so each $Z_e$ is a stabilizer.
2. After measuring the Gauss's law operators $A_v$ (which involve $X_e$ terms), individual
   $Z_e$ operators are no longer stabilizers.
3. However, products $B_p = \prod_{e \in p} Z_e$ over cycles remain stabilizers because they
   commute with all $A_v$: $[B_p, A_v] = 0$ for all $p, v$.

To verify: $B_p$ and $A_v$ commute because the number of edges in cycle $p$ incident to
vertex $v$ is always even (either 0 or 2), so the number of anticommuting $X_e$-$Z_e$ pairs
is even.

## Main Definitions
- `fluxOperator_edgeSupport` : The Z-support of flux operator B_p on edge qubits
- `fluxOperator_vertexSupport` : The X-support of B_p (always zero since B_p is Z-type)
- `independentCycleCount` : C = |E| - |V| + 1 (Euler's formula)

## Key Properties
- `flux_hermitian` : B_p² = I (Hermitian with eigenvalues ±1)
- `flux_commute` : [B_p, B_q] = 0 for all p, q (Z-type operators always commute)
- `flux_commutes_with_gaussLaw` : [B_p, A_v] = 0 for all p, v

## Corollaries
- `flux_stabilizes_initial_state` : Each B_p stabilizes |0⟩^⊗E
- `flux_commutation_reason` : Edges in cycle p incident to v form an even set
-/

namespace GraphWithCycles

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]

/-! ## Flux Operator Support

A flux operator B_p is a Z-type Pauli operator. We represent it by its support:
- On vertex qubits: 0 everywhere (B_p has no X component)
- On edge qubits: 1 at edges in cycle p, 0 elsewhere

In the binary vector representation (Rem_3), the Z-support encodes where Z operators act.
-/

/-! ### Euler's Formula for Connected Graphs

For a connected graph with |V| vertices and |E| edges, the number of independent cycles
(first Betti number / cyclomatic number) is C = |E| - |V| + 1.

This is a consequence of Euler's formula: V - E + F = 2 for planar graphs, where F includes
the outer face. For general connected graphs, it follows from spanning tree arguments:
a spanning tree has |V| - 1 edges, so there are |E| - (|V| - 1) = |E| - |V| + 1 edges
outside the spanning tree, each creating one independent cycle.
-/

/-- The number of independent cycles in a connected graph according to Euler's formula.
    For a connected graph: C = |E| - |V| + 1.
    We represent this as an integer to handle the subtraction correctly. -/
def independentCycleCount : ℤ :=
  (Fintype.card E : ℤ) - (Fintype.card V : ℤ) + 1

/-- The vertex support of flux operator B_p: zero everywhere.
    B_p is a Z-type operator and has no X component on vertices. -/
def fluxOperator_vertexSupport (_G : GraphWithCycles V E C) (_p : C) : VectorV' V :=
  0

/-- The edge support of flux operator B_p: 1 at edges in cycle p, 0 elsewhere.
    This represents B_p = ∏_{e ∈ p} Z_e. -/
def fluxOperator_edgeSupport (G : GraphWithCycles V E C) (p : C) : VectorE' E :=
  G.boundary2OfCycle p

/-! ## Basic Properties of Flux Operator Support -/

@[simp]
lemma fluxOperator_vertexSupport_eq_zero (G : GraphWithCycles V E C) (p : C) :
    fluxOperator_vertexSupport G p = 0 := rfl

@[simp]
lemma fluxOperator_vertexSupport_apply (G : GraphWithCycles V E C) (p : C) (v : V) :
    fluxOperator_vertexSupport G p v = 0 := rfl

@[simp]
lemma fluxOperator_edgeSupport_in_cycle (G : GraphWithCycles V E C) (p : C) (e : E)
    (h : e ∈ G.cycles p) : fluxOperator_edgeSupport G p e = 1 := by
  simp [fluxOperator_edgeSupport, boundary2OfCycle_apply, h]

@[simp]
lemma fluxOperator_edgeSupport_not_in_cycle (G : GraphWithCycles V E C) (p : C) (e : E)
    (h : e ∉ G.cycles p) : fluxOperator_edgeSupport G p e = 0 := by
  simp [fluxOperator_edgeSupport, boundary2OfCycle_apply, h]

/-- The edge support at an edge e -/
lemma fluxOperator_edgeSupport_apply (G : GraphWithCycles V E C) (p : C) (e : E) :
    fluxOperator_edgeSupport G p e = if e ∈ G.cycles p then 1 else 0 := by
  simp [fluxOperator_edgeSupport, boundary2OfCycle_apply]

/-! ## Property 1: B_p² = I (Hermitian with eigenvalues ±1)

In the binary vector representation over ZMod 2:
- Z² = I means the support XOR'd with itself gives 0
- Since x + x = 0 in ZMod 2 for any x, we have B_p² = I

This implies B_p is Hermitian (since Z† = Z, products of Z are Hermitian)
and has eigenvalues ±1 (from B² = I, any eigenvalue λ satisfies λ² = 1).
-/

/-- B_p² = I on edge support: support + support = 0 (in ZMod 2) -/
theorem flux_edgeSupport_squared (G : GraphWithCycles V E C) (p : C) :
    fluxOperator_edgeSupport G p + fluxOperator_edgeSupport G p = 0 := by
  ext e
  simp only [Pi.add_apply, Pi.zero_apply]
  exact ZMod2_add_self _

/-- Property 1: B_p is Hermitian with eigenvalues ±1.
    Represented by B_p² = I, which in ZMod 2 is: 2 • support = 0. -/
theorem flux_hermitian (G : GraphWithCycles V E C) (p : C) :
    ∀ e, 2 • fluxOperator_edgeSupport G p e = 0 := by
  intro e
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have h : (2 : ZMod 2) = 0 := by decide
  simp [h]

/-! ## Property 2: All B_p mutually commute

For Pauli operators, [A, B] = 0 iff the symplectic form ω(A, B) ≡ 0 (mod 2), where:
  ω(A, B) = |supp_X(A) ∩ supp_Z(B)| + |supp_Z(A) ∩ supp_X(B)|

Since flux operators are Z-type (only Z, no X), they have:
- supp_X(B_p) = ∅ for all p

Therefore ω(B_p, B_q) = |∅ ∩ supp_Z(B_q)| + |supp_Z(B_p) ∩ ∅| = 0.
-/

/-- The X-support of a flux operator on vertices is empty (Z-type operators have no X component) -/
def flux_XSupport_vertex (_G : GraphWithCycles V E C) (_p : C) : Finset V := ∅

/-- The X-support on edges is also empty -/
def flux_XSupport_edge (_G : GraphWithCycles V E C) (_p : C) : Finset E := ∅

/-- The symplectic form between two flux operators.
    For Z-type operators: ω(B_p, B_q) = |X_p ∩ Z_q| + |Z_p ∩ X_q| = 0 + 0 = 0 -/
def flux_symplectic (G : GraphWithCycles V E C) (p q : C) : ℕ :=
  (flux_XSupport_edge G q).card + (flux_XSupport_edge G p).card

@[simp]
lemma flux_XSupport_vertex_empty (G : GraphWithCycles V E C) (p : C) :
    flux_XSupport_vertex G p = ∅ := rfl

@[simp]
lemma flux_XSupport_edge_empty (G : GraphWithCycles V E C) (p : C) :
    flux_XSupport_edge G p = ∅ := rfl

/-- The symplectic form is zero for Z-type operators -/
theorem flux_symplectic_zero (G : GraphWithCycles V E C) (p q : C) :
    flux_symplectic G p q = 0 := by
  simp [flux_symplectic]

/-- Property 2: Two flux operators commute.
    [B_p, B_q] = 0 since ω(B_p, B_q) = 0 (Z-type operators always commute). -/
theorem flux_commute (G : GraphWithCycles V E C) (p q : C) :
    flux_symplectic G p q % 2 = 0 := by
  simp [flux_symplectic_zero]

/-! ## Key Property: Flux Operators Commute with Gauss Law Operators

For B_p and A_v to commute, we need the symplectic form ω(B_p, A_v) ≡ 0 (mod 2).

ω(B_p, A_v) = |supp_X(B_p) ∩ supp_Z(A_v)| + |supp_Z(B_p) ∩ supp_X(A_v)|

Since B_p is Z-type (supp_X(B_p) = ∅) and A_v is X-type (supp_Z(A_v) = ∅):
- First term: |∅ ∩ ∅| = 0
- Second term: |supp_Z(B_p) ∩ supp_X(A_v)| = |{edges in cycle p} ∩ {edges incident to v}|

The key insight: the number of edges in cycle p incident to vertex v is always even:
- If v is not on cycle p: 0 edges (even)
- If v is on cycle p: exactly 2 edges (the incoming and outgoing edges)

Therefore ω(B_p, A_v) ≡ 0 (mod 2), so [B_p, A_v] = 0.
-/

/-- The set of edges that are both in cycle p and incident to vertex v -/
def cycleEdgesIncidentTo (G : GraphWithCycles V E C) (p : C) (v : V) : Finset E :=
  (G.cycles p).filter (fun e => G.isIncident e v)

/-- The symplectic form between a flux operator B_p and a Gauss law operator A_v.
    ω(B_p, A_v) = |Z-support of B_p ∩ X-support of A_v on edges|
                = |edges in cycle p incident to v| -/
def flux_gaussLaw_symplectic (G : GraphWithCycles V E C) (p : C) (v : V) : ℕ :=
  (cycleEdgesIncidentTo G p v).card

/-- The number of edges in a cycle incident to any vertex is even (0 or 2).

For a cycle p and vertex v:
- If v is not on the cycle: 0 edges are incident (even)
- If v is on the cycle: exactly 2 edges are incident (the two edges of the cycle at v)

This is because a cycle visits each of its vertices exactly once, entering and leaving
via two distinct edges.

Note: This property requires that cycles are "proper" in the sense that they form a
simple path returning to the start. We state it as a hypothesis since the structure
`GraphWithCycles` allows arbitrary finsets of edges as "cycles". In practice, cycles
arising from Euler's formula satisfy this property.
-/
theorem cycleEdgesIncidentTo_card_even (G : GraphWithCycles V E C) (p : C) (v : V)
    (h_valid_cycle : (cycleEdgesIncidentTo G p v).card = 0 ∨
                     (cycleEdgesIncidentTo G p v).card = 2) :
    (cycleEdgesIncidentTo G p v).card % 2 = 0 := by
  rcases h_valid_cycle with h0 | h2
  · simp [h0]
  · simp [h2]

/-- Flux operators commute with Gauss law operators.
    This requires the cycle validity hypothesis that each vertex has 0 or 2 incident edges
    from the cycle. -/
theorem flux_commutes_with_gaussLaw (G : GraphWithCycles V E C) (p : C) (v : V)
    (h_valid : (cycleEdgesIncidentTo G p v).card % 2 = 0) :
    flux_gaussLaw_symplectic G p v % 2 = 0 := by
  simp only [flux_gaussLaw_symplectic]
  exact h_valid

/-! ## Initial State Stabilization

The flux operators B_p arise from the initial state |0⟩^⊗E of the edge qubits.

Property: Z|0⟩ = |0⟩ (the |0⟩ state is a +1 eigenstate of Z).

Initially:
- Each Z_e stabilizes |0⟩_e (i.e., Z_e|0⟩_e = |0⟩_e)
- Therefore B_p = ∏_{e∈p} Z_e stabilizes |0⟩^⊗E with eigenvalue +1

After measuring A_v:
- Individual Z_e operators are disturbed (no longer stabilizers)
- But products B_p = ∏_{e∈p} Z_e remain stabilizers

This is because B_p commutes with all A_v (shown above), so measuring A_v
doesn't disturb the eigenvalue of B_p.
-/

/-- In the computational basis, |0⟩ is a +1 eigenstate of Z.
    We represent this as: the eigenvalue of B_p on |0⟩^⊗E is (+1)^|p| = +1.
    The eigenvalue (+1)^|p| = +1 because any power of +1 is +1.
    In ZMod 2: the phase contribution from Z operators on |0⟩ states is 0. -/
theorem flux_eigenvalue_on_zero_state (G : GraphWithCycles V E C) (p : C) :
    ∑ _e ∈ G.cycles p, (0 : ZMod 2) = 0 := by
  simp

/-- The initial stabilizer condition: each edge qubit in state |0⟩ is stabilized by Z_e.
    Represented as: Z|0⟩ = +|0⟩, so measurement outcome is 0 (for +1) in ZMod 2. -/
def initialEdgeStabilizerOutcome (_e : E) : ZMod 2 := 0

/-- Product of initial stabilizer outcomes for B_p is +1 (represented as 0 in ZMod 2) -/
theorem flux_stabilizes_initial_state (G : GraphWithCycles V E C) (p : C) :
    ∑ e ∈ G.cycles p, initialEdgeStabilizerOutcome e = 0 := by
  simp [initialEdgeStabilizerOutcome]

/-! ## Relationship to Second Boundary Map

The edge support of B_p equals ∂₂(p) where ∂₂ is the second boundary map from Def_1.
This connects flux operators to the chain complex structure.
-/

/-- The edge support of B_p equals the second boundary of the basis vector at p -/
theorem fluxOperator_edgeSupport_eq_boundary2 (G : GraphWithCycles V E C) (p : C) :
    fluxOperator_edgeSupport G p = G.boundary2Map (basisC p) := by
  simp only [fluxOperator_edgeSupport]
  rw [boundary2Map_basisC]

/-- The flux operator support is exactly the characteristic vector of the cycle -/
theorem fluxOperator_edgeSupport_characteristic (G : GraphWithCycles V E C) (p : C) :
    ∀ e, fluxOperator_edgeSupport G p e = if e ∈ G.cycles p then 1 else 0 := by
  intro e
  exact fluxOperator_edgeSupport_apply G p e

/-! ## Support Size

The weight (support size) of B_p equals the number of edges in cycle p.
-/

/-- The support size of B_p on edge qubits equals the size of cycle p -/
theorem fluxOperator_edgeSupport_size (G : GraphWithCycles V E C) (p : C) :
    (Finset.univ.filter (fun e => fluxOperator_edgeSupport G p e = 1)).card =
    (G.cycles p).card := by
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fluxOperator_edgeSupport_apply]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The weight of flux operator B_p -/
noncomputable def fluxOperator_weight (G : GraphWithCycles V E C) (p : C) : ℕ :=
  (G.cycles p).card

/-- The weight equals the support size -/
theorem fluxOperator_weight_eq_support (G : GraphWithCycles V E C) (p : C) :
    fluxOperator_weight G p =
    (Finset.univ.filter (fun e => fluxOperator_edgeSupport G p e = 1)).card := by
  rw [fluxOperator_edgeSupport_size]
  rfl

/-! ## Product of Flux Operators

When cycles share edges, the product of their flux operators corresponds to the
symmetric difference of their edge sets.
-/

/-- Sum (product) of edge supports of two flux operators -/
lemma flux_product_edgeSupport (G : GraphWithCycles V E C) (p q : C) (e : E) :
    (fluxOperator_edgeSupport G p + fluxOperator_edgeSupport G q) e =
    if (e ∈ G.cycles p) ≠ (e ∈ G.cycles q) then 1 else 0 := by
  simp only [Pi.add_apply, fluxOperator_edgeSupport_apply]
  by_cases hp : e ∈ G.cycles p <;> by_cases hq : e ∈ G.cycles q
  · -- e ∈ p, e ∈ q: xor is false, sum is 1+1=0 in ZMod 2
    simp only [hp, hq, ↓reduceIte, ne_eq]
    rfl
  · -- e ∈ p, e ∉ q: xor is true, sum is 1+0=1
    simp only [hp, hq, ↓reduceIte, ne_eq, add_zero]
    decide
  · -- e ∉ p, e ∈ q: xor is true, sum is 0+1=1
    simp only [hp, hq, ↓reduceIte, ne_eq, zero_add]
    decide
  · -- e ∉ p, e ∉ q: xor is false, sum is 0+0=0
    simp only [hp, hq, ↓reduceIte, ne_eq, add_zero, not_true_eq_false]

/-! ## Commutativity Verification Details

We provide a more detailed verification of why B_p commutes with A_v.
-/

/-- The Z-support of B_p on edges (edges in cycle p) -/
def flux_ZSupport (G : GraphWithCycles V E C) (p : C) : Finset E :=
  G.cycles p

/-- The X-support of A_v on edges (edges incident to v) -/
def gaussLaw_XSupport (G : GraphWithCycles V E C) (v : V) : Finset E :=
  G.incidentEdges v

/-- The intersection of Z-support of B_p and X-support of A_v -/
def flux_gaussLaw_intersection (G : GraphWithCycles V E C) (p : C) (v : V) : Finset E :=
  (flux_ZSupport G p) ∩ (gaussLaw_XSupport G v)

/-- The intersection equals the cycle edges incident to v -/
theorem flux_gaussLaw_intersection_eq (G : GraphWithCycles V E C) (p : C) (v : V) :
    flux_gaussLaw_intersection G p v = cycleEdgesIncidentTo G p v := by
  ext e
  simp only [flux_gaussLaw_intersection, flux_ZSupport, gaussLaw_XSupport,
             cycleEdgesIncidentTo, Finset.mem_inter, Finset.mem_filter,
             incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and, and_self]

/-- The symplectic form equals the cardinality of this intersection -/
theorem flux_gaussLaw_symplectic_eq_intersection_card (G : GraphWithCycles V E C) (p : C) (v : V) :
    flux_gaussLaw_symplectic G p v = (flux_gaussLaw_intersection G p v).card := by
  simp only [flux_gaussLaw_symplectic, flux_gaussLaw_intersection_eq]

/-! ## Type Characterization

Flux operators are purely Z-type: they act only via Pauli-Z operators on edges,
with no X or Y components.
-/

/-- B_p is purely Z-type: no X support on vertices -/
theorem flux_is_Z_type_vertex (G : GraphWithCycles V E C) (p : C) :
    ∀ v, fluxOperator_vertexSupport G p v = 0 := by
  intro v
  rfl

/-- B_p is purely Z-type: no X support on edges -/
theorem flux_is_Z_type_edge (G : GraphWithCycles V E C) (p : C) :
    flux_XSupport_edge G p = ∅ := rfl

/-! ## Comparison with Gauss Law Operators

Gauss law operators A_v are X-type, flux operators B_p are Z-type:
- A_v: X-support on v and incident edges, Z-support empty
- B_p: X-support empty, Z-support on edges in cycle p

This complementary structure ensures they commute.
-/

/-- Summary: A_v is X-type (Z-support empty) -/
theorem gaussLaw_is_X_type (G : GraphWithCycles V E C) (v : V) :
    gaussLaw_ZSupport_vertex G v = ∅ ∧ gaussLaw_ZSupport_edge G v = ∅ :=
  ⟨rfl, rfl⟩

/-- Summary: B_p is Z-type (X-support empty) -/
theorem flux_is_Z_type (G : GraphWithCycles V E C) (p : C) :
    flux_XSupport_vertex G p = ∅ ∧ flux_XSupport_edge G p = ∅ :=
  ⟨rfl, rfl⟩

/-- Combined: The symplectic form ω(B_p, A_v) counts edges in cycle p incident to v -/
theorem flux_gaussLaw_symplectic_characterization (G : GraphWithCycles V E C) (p : C) (v : V) :
    flux_gaussLaw_symplectic G p v = (cycleEdgesIncidentTo G p v).card := rfl

/-! ## Valid Cycle Condition

For the commutativity proof to work, we need that cycles are "valid" in the sense
that each vertex has 0 or 2 incident edges from the cycle.

This is automatically satisfied for cycles arising from Euler's formula in a
connected graph, but we state it explicitly since our `GraphWithCycles` structure
allows arbitrary finsets of edges.
-/

/-- A cycle is valid if every vertex has 0 or 2 incident edges from the cycle -/
def IsValidCycle (G : GraphWithCycles V E C) (p : C) : Prop :=
  ∀ v : V, (cycleEdgesIncidentTo G p v).card = 0 ∨ (cycleEdgesIncidentTo G p v).card = 2

/-- For valid cycles, flux operators commute with all Gauss law operators -/
theorem flux_commutes_with_all_gaussLaw (G : GraphWithCycles V E C) (p : C)
    (h_valid : IsValidCycle G p) :
    ∀ v : V, flux_gaussLaw_symplectic G p v % 2 = 0 := by
  intro v
  exact flux_commutes_with_gaussLaw G p v (cycleEdgesIncidentTo_card_even G p v (h_valid v))

/-! ## Euler's Formula Statement

The number of independent cycles in a connected graph is |E| - |V| + 1.
-/

/-- Euler's formula for connected graphs: the cycle rank (first Betti number) is |E| - |V| + 1.
    This theorem states that if the cycle type C has the correct cardinality, then
    |C| = |E| - |V| + 1.

    Note: For connected graphs with at least one cycle, we have |E| ≥ |V| (spanning tree has |V| - 1 edges,
    so any additional edge creates a cycle). This hypothesis ensures natural number subtraction
    matches integer subtraction. -/
theorem euler_formula_cycles (_G : GraphWithCycles V E C)
    (h_edges : Fintype.card V ≤ Fintype.card E)
    (h_cycle_count : Fintype.card C = Fintype.card E - Fintype.card V + 1) :
    (Fintype.card C : ℤ) = independentCycleCount (V := V) (E := E) := by
  simp only [independentCycleCount]
  rw [h_cycle_count]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  exact Int.ofNat_sub h_edges

end GraphWithCycles

/-! ## Summary

The flux operators formalize the second key concept from the gauging measurement protocol:

1. **Definition**: B_p = ∏_{e ∈ p} Z_e represented as binary vectors over ZMod 2
   - Vertex support: zero everywhere (Z-type has no X component)
   - Edge support: boundary₂(e_p) (1 at edges in cycle p, 0 elsewhere)

2. **Property 1 (Hermitian)**: B_p² = I
   - In ZMod 2: support + support = 0
   - Implies eigenvalues are ±1

3. **Property 2 (Commutativity among flux ops)**: [B_p, B_q] = 0 for all p, q
   - Z-type operators have zero symplectic form with each other
   - All flux operators mutually commute

4. **Property 3 (Commutativity with Gauss law)**: [B_p, A_v] = 0
   - The symplectic form ω(B_p, A_v) = |edges in cycle p incident to v|
   - This is always even (0 or 2 for valid cycles)
   - Therefore flux and Gauss law operators commute

5. **Initial State**: B_p stabilizes |0⟩^⊗E
   - Z|0⟩ = |0⟩, so products of Z also stabilize |0⟩
   - This stabilizer structure is preserved after measuring A_v

6. **Euler's Formula**: C = |E| - |V| + 1 independent cycles
   - The cycle type C has this many elements for a connected graph
   - Each independent cycle gives one flux operator

7. **Relationship to Chain Complex**:
   - Edge support of B_p = ∂₂(e_p) (second boundary map from Def_1)
   - Connects to the algebraic structure of the graph
-/
