import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Remarks.Rem_2_GraphConvention
import QEC1.Remarks.Rem_3_BinaryVectorNotation

/-!
# Def_2: Gauss's Law Operators

## Statement
Given a connected graph $G = (V_G, E_G)$ whose vertices are identified with the qubits in the
support of a logical operator $L = \prod_{v \in V_G} X_v$, the **Gauss's law operators** are
the set $\mathcal{A} = \{A_v\}_{v \in V_G}$ where:
$$A_v = X_v \prod_{e \ni v} X_e$$
Here $X_v$ is the Pauli-$X$ operator on the vertex qubit $v$, and $X_e$ is the Pauli-$X$ operator
on the edge qubit $e$. The product $\prod_{e \ni v}$ is over all edges incident to vertex $v$.

The Gauss's law operators satisfy:
1. Each $A_v$ is Hermitian with eigenvalues $\pm 1$.
2. All $A_v$ mutually commute: $[A_v, A_{v'}] = 0$ for all $v, v' \in V_G$.
3. $\prod_{v \in V_G} A_v = L \cdot \prod_{e \in E_G} X_e^{2} = L$ (since $X_e^2 = I$).

This last property is the key to the gauging measurement: measuring all $A_v$ and multiplying
the outcomes yields the eigenvalue of $L$.

## Main Definitions
- `GaussLawOperator` : The support of a Gauss law operator A_v as binary vectors
- `gaussLawOperator_vertexSupport` : The vertex support (1 at v, 0 elsewhere)
- `gaussLawOperator_edgeSupport` : The edge support (1 at incident edges, 0 elsewhere)

## Key Properties
- `gaussLaw_hermitian` : A_v² = I (implies Hermitian with eigenvalues ±1)
- `gaussLaw_commute` : [A_v, A_w] = 0 for all v, w (X-type operators always commute)
- `gaussLaw_product_vertex_support` : Product of vertex supports is the all-ones vector (= L)
- `gaussLaw_product_edge_support` : Product of edge supports is zero (edges cancel pairwise)

## Corollaries
- `gaussLaw_product_is_L` : ∏_v A_v has vertex support = all 1s (represents L)
- `gaussLaw_independent_count` : |V| - 1 independent generators
-/

namespace GraphWithCycles

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]

/-! ## Gauss Law Operator Support

A Gauss law operator A_v is an X-type Pauli operator. We represent it by its support:
- On vertex qubits: 1 at position v, 0 elsewhere
- On edge qubits: 1 at edges incident to v, 0 elsewhere

In the binary vector representation (Rem_3), the support encodes where X operators act.
-/

/-- The vertex support of Gauss law operator A_v: a binary vector with 1 at v, 0 elsewhere.
    This represents X_v in the product A_v = X_v ∏_{e∋v} X_e. -/
def gaussLawOperator_vertexSupport (_G : GraphWithCycles V E C) (v : V) : VectorV' V :=
  basisV v

/-- The edge support of Gauss law operator A_v: 1 at edges incident to v, 0 elsewhere.
    This represents ∏_{e∋v} X_e in the product A_v = X_v ∏_{e∋v} X_e. -/
def gaussLawOperator_edgeSupport (G : GraphWithCycles V E C) (v : V) : VectorE' E :=
  G.coboundaryOfVertex v

/-! ## Basic Properties of Gauss Law Operator Support -/

@[simp]
lemma gaussLawOperator_vertexSupport_same (G : GraphWithCycles V E C) (v : V) :
    gaussLawOperator_vertexSupport G v v = 1 := by
  simp [gaussLawOperator_vertexSupport]

@[simp]
lemma gaussLawOperator_vertexSupport_ne (G : GraphWithCycles V E C) (v w : V) (h : v ≠ w) :
    gaussLawOperator_vertexSupport G v w = 0 := by
  simp [gaussLawOperator_vertexSupport, h]

@[simp]
lemma gaussLawOperator_edgeSupport_incident (G : GraphWithCycles V E C) (v : V) (e : E)
    (h : G.isIncident e v) : gaussLawOperator_edgeSupport G v e = 1 := by
  simp [gaussLawOperator_edgeSupport, coboundaryOfVertex_apply, h]

@[simp]
lemma gaussLawOperator_edgeSupport_not_incident (G : GraphWithCycles V E C) (v : V) (e : E)
    (h : ¬G.isIncident e v) : gaussLawOperator_edgeSupport G v e = 0 := by
  simp [gaussLawOperator_edgeSupport, coboundaryOfVertex_apply, h]

/-- The edge support at an edge e -/
lemma gaussLawOperator_edgeSupport_apply (G : GraphWithCycles V E C) (v : V) (e : E) :
    gaussLawOperator_edgeSupport G v e = if G.isIncident e v then 1 else 0 := by
  simp [gaussLawOperator_edgeSupport, coboundaryOfVertex_apply]

/-! ## Property 1: A_v² = I (Hermitian with eigenvalues ±1)

In the binary vector representation over ZMod 2:
- X² = I means the support XOR'd with itself gives 0
- Since x + x = 0 in ZMod 2 for any x, we have A_v² = I

This implies A_v is Hermitian (since X† = X, products of X are Hermitian)
and has eigenvalues ±1 (from A² = I, any eigenvalue λ satisfies λ² = 1).
-/

/-- In ZMod 2, any element added to itself is 0 -/
lemma ZMod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- A_v² = I on vertex support: support + support = 0 (in ZMod 2) -/
theorem gaussLaw_vertexSupport_squared (G : GraphWithCycles V E C) (v : V) :
    gaussLawOperator_vertexSupport G v + gaussLawOperator_vertexSupport G v = 0 := by
  ext w
  simp only [Pi.add_apply, Pi.zero_apply]
  exact ZMod2_add_self _

/-- A_v² = I on edge support: support + support = 0 (in ZMod 2) -/
theorem gaussLaw_edgeSupport_squared (G : GraphWithCycles V E C) (v : V) :
    gaussLawOperator_edgeSupport G v + gaussLawOperator_edgeSupport G v = 0 := by
  ext e
  simp only [Pi.add_apply, Pi.zero_apply]
  exact ZMod2_add_self _

/-- Property 1: A_v is Hermitian with eigenvalues ±1.
    Represented by A_v² = I, which in ZMod 2 is: 2 • support = 0.
    If A|ψ⟩ = λ|ψ⟩ and A² = I, then λ² = 1, so λ ∈ {-1, +1}. -/
theorem gaussLaw_hermitian (G : GraphWithCycles V E C) (v : V) :
    ∀ w, 2 • gaussLawOperator_vertexSupport G v w = 0 := by
  intro w
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have h : (2 : ZMod 2) = 0 := by decide
  simp [h]

/-! ## Property 2: All A_v mutually commute

For Pauli operators, [A, B] = 0 iff the symplectic form ω(A, B) ≡ 0 (mod 2), where:
  ω(A, B) = |supp_X(A) ∩ supp_Z(B)| + |supp_Z(A) ∩ supp_X(B)|

Since Gauss law operators are X-type (only X, no Z), they have:
- supp_Z(A_v) = ∅ for all v

Therefore ω(A_v, A_w) = |supp_X(A_v) ∩ ∅| + |∅ ∩ supp_X(A_w)| = 0.
-/

/-- The Z-support of a Gauss law operator is empty (X-type operators have no Z component) -/
def gaussLaw_ZSupport_vertex (_G : GraphWithCycles V E C) (_v : V) : Finset V := ∅

/-- The Z-support on edges is also empty -/
def gaussLaw_ZSupport_edge (_G : GraphWithCycles V E C) (_v : V) : Finset E := ∅

/-- The symplectic form between two Gauss law operators.
    For X-type operators: ω(A_v, A_w) = |X_v ∩ Z_w| + |Z_v ∩ X_w| = 0 + 0 = 0 -/
def gaussLaw_symplectic (G : GraphWithCycles V E C) (v w : V) : ℕ :=
  (gaussLaw_ZSupport_vertex G w).card + (gaussLaw_ZSupport_vertex G v).card

@[simp]
lemma gaussLaw_ZSupport_vertex_empty (G : GraphWithCycles V E C) (v : V) :
    gaussLaw_ZSupport_vertex G v = ∅ := rfl

@[simp]
lemma gaussLaw_ZSupport_edge_empty (G : GraphWithCycles V E C) (v : V) :
    gaussLaw_ZSupport_edge G v = ∅ := rfl

/-- The symplectic form is zero for X-type operators -/
theorem gaussLaw_symplectic_zero (G : GraphWithCycles V E C) (v w : V) :
    gaussLaw_symplectic G v w = 0 := by
  simp [gaussLaw_symplectic]

/-- Property 2: Two Gauss law operators commute.
    [A_v, A_w] = 0 since ω(A_v, A_w) = 0 (X-type operators always commute). -/
theorem gaussLaw_commute (G : GraphWithCycles V E C) (v w : V) :
    gaussLaw_symplectic G v w % 2 = 0 := by
  simp [gaussLaw_symplectic_zero]

/-! ## Property 3: ∏_{v ∈ V} A_v = L

The product of all Gauss law operators:
- On vertices: Each vertex v contributes 1 at position v, so sum = all 1s = support of L
- On edges: Each edge e is incident to exactly 2 vertices, so appears twice in the sum.
           In ZMod 2, 1 + 1 = 0, so edge contribution cancels.

Therefore ∏_v A_v = L (the logical operator with support on all vertices).
-/

/-- Sum of all vertex supports: ∑_v (A_v vertex support) -/
def gaussLaw_product_vertexSupport (G : GraphWithCycles V E C) : VectorV' V :=
  ∑ v : V, gaussLawOperator_vertexSupport G v

/-- Sum of all edge supports: ∑_v (A_v edge support) -/
def gaussLaw_product_edgeSupport (G : GraphWithCycles V E C) : VectorE' E :=
  ∑ v : V, gaussLawOperator_edgeSupport G v

/-- Each vertex w appears in exactly one A_v (namely when v = w), so the sum at w is 1 -/
theorem gaussLaw_product_vertexSupport_eq_one (G : GraphWithCycles V E C) (w : V) :
    gaussLaw_product_vertexSupport G w = 1 := by
  simp only [gaussLaw_product_vertexSupport, Finset.sum_apply]
  -- The sum ∑_v (if v = w then 1 else 0) = 1
  have h : ∑ v : V, gaussLawOperator_vertexSupport G v w =
           ∑ v : V, if v = w then (1 : ZMod 2) else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    simp only [gaussLawOperator_vertexSupport, basisV]
    split_ifs with hvw
    · subst hvw; simp
    · simp [hvw]
  rw [h, Finset.sum_ite_eq' Finset.univ w (fun _ => (1 : ZMod 2))]
  simp

/-- The product of all A_v has vertex support equal to the all-ones vector.
    This is the support of L = ∏_{v ∈ V} X_v. -/
theorem gaussLaw_product_vertexSupport_all_ones (G : GraphWithCycles V E C) :
    gaussLaw_product_vertexSupport G = fun _ => 1 := by
  ext w
  exact gaussLaw_product_vertexSupport_eq_one G w

/-- Each edge e is incident to exactly 2 vertices (its endpoints).
    In ZMod 2, 1 + 1 = 0, so edge contributions cancel. -/
theorem gaussLaw_product_edgeSupport_eq_zero (G : GraphWithCycles V E C) (e : E) :
    gaussLaw_product_edgeSupport G e = 0 := by
  simp only [gaussLaw_product_edgeSupport, Finset.sum_apply]
  -- Each edge is incident to exactly its two endpoints
  -- Sum over all v of (if isIncident e v then 1 else 0)
  have h : ∑ v : V, gaussLawOperator_edgeSupport G v e =
           ∑ v : V, if G.isIncident e v then (1 : ZMod 2) else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    exact gaussLawOperator_edgeSupport_apply G v e
  rw [h]
  -- The incident vertices are exactly the endpoints
  let v1 := (G.edgeEndpoints e).1
  let v2 := (G.edgeEndpoints e).2
  have hne : v1 ≠ v2 := G.edge_endpoints_ne e
  -- Split the sum into incident and non-incident vertices
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => G.isIncident e v)]
  -- Non-incident terms are 0
  have h_not : ∑ v ∈ Finset.univ.filter (fun v => ¬G.isIncident e v),
               (if G.isIncident e v then (1 : ZMod 2) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp [hv]
  rw [h_not, add_zero]
  -- Incident vertices are exactly {v1, v2}
  have h_filter : Finset.univ.filter (fun v => G.isIncident e v) = {v1, v2} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               Finset.mem_singleton, isIncident]
    constructor
    · intro hv
      rcases hv with h1 | h2
      · left; exact h1.symm
      · right; exact h2.symm
    · intro hv
      rcases hv with rfl | rfl
      · left; rfl
      · right; rfl
  rw [h_filter]
  -- Sum over {v1, v2} of 1 = 1 + 1 = 0 in ZMod 2
  have h_inc_v1 : G.isIncident e v1 := Or.inl rfl
  have h_inc_v2 : G.isIncident e v2 := Or.inr rfl
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  simp only [h_inc_v1, ↓reduceIte, h_inc_v2]
  -- 1 + 1 = 0 in ZMod 2
  rfl

/-- The product of all A_v has edge support equal to zero (edges cancel pairwise).
    This represents X_e² = I for each edge. -/
theorem gaussLaw_product_edgeSupport_zero (G : GraphWithCycles V E C) :
    gaussLaw_product_edgeSupport G = 0 := by
  ext e
  simp only [Pi.zero_apply]
  exact gaussLaw_product_edgeSupport_eq_zero G e

/-- Property 3: The product of all Gauss law operators equals L.
    - Vertex support: all 1s (= L = ∏_v X_v)
    - Edge support: all 0s (since X_e² = I, edge terms cancel)

    This is the key property: measuring all A_v and multiplying outcomes gives
    the eigenvalue of L. -/
theorem gaussLaw_product_is_L (G : GraphWithCycles V E C) :
    (gaussLaw_product_vertexSupport G = fun _ => 1) ∧
    gaussLaw_product_edgeSupport G = 0 :=
  ⟨gaussLaw_product_vertexSupport_all_ones G, gaussLaw_product_edgeSupport_zero G⟩

/-! ## Relationship to Coboundary Map

The edge support of A_v equals δ(v) where δ is the coboundary map from Def_1.
This connects Gauss law operators to the chain complex structure.
-/

/-- The edge support of A_v equals the coboundary of the basis vector at v -/
theorem gaussLawOperator_edgeSupport_eq_coboundary (G : GraphWithCycles V E C) (v : V) :
    gaussLawOperator_edgeSupport G v = G.coboundaryMap (basisV v) := by
  simp only [gaussLawOperator_edgeSupport]
  rw [coboundaryMap_basisV]

/-- The sum of all edge supports equals the coboundary of the all-ones vector -/
theorem gaussLaw_product_edgeSupport_eq_coboundary_ones (G : GraphWithCycles V E C) :
    gaussLaw_product_edgeSupport G = G.coboundaryMap (fun _ => 1) := by
  simp only [gaussLaw_product_edgeSupport, gaussLawOperator_edgeSupport_eq_coboundary]
  -- ∑_v δ(e_v) = δ(∑_v e_v) by linearity
  rw [← map_sum]
  congr 1
  ext w
  simp only [Finset.sum_apply, basisV, Pi.single_apply]
  rw [Finset.sum_ite_eq Finset.univ w (fun _ => (1 : ZMod 2))]
  simp

/-! ## Group Structure: |V| - 1 Independent Generators

The Gauss law operators satisfy one constraint: ∏_v A_v = L.
This means of the |V| generators, only |V| - 1 are independent.
The abelian group generated by {A_v} has order 2^{|V|-1}.
-/

/-- Number of Gauss law operators equals number of vertices -/
def gaussLaw_generator_count (_G : GraphWithCycles V E C) : ℕ := Fintype.card V

/-- Number of constraints among Gauss law operators (the single product constraint) -/
def gaussLaw_constraint_count (_G : GraphWithCycles V E C) : ℕ := 1

/-- Number of independent Gauss law generators = |V| - 1 -/
def gaussLaw_independent_count (G : GraphWithCycles V E C) : ℕ :=
  gaussLaw_generator_count G - gaussLaw_constraint_count G

/-- The independent count is |V| - 1 -/
theorem gaussLaw_independent_count_eq (G : GraphWithCycles V E C) (_h : Fintype.card V ≥ 1) :
    gaussLaw_independent_count G = Fintype.card V - 1 := by
  simp [gaussLaw_independent_count, gaussLaw_generator_count, gaussLaw_constraint_count]

/-- The abelian group generated by {A_v} has order 2^{|V|-1} -/
def gaussLaw_group_order (G : GraphWithCycles V E C) : ℕ :=
  2 ^ gaussLaw_independent_count G

/-- The constraint: sum of all generators (in ZMod 2) equals the all-ones vector -/
theorem gaussLaw_constraint_equation (G : GraphWithCycles V E C) (w : V) :
    ∑ v : V, gaussLawOperator_vertexSupport G v w = 1 := by
  have := gaussLaw_product_vertexSupport_eq_one G w
  simp only [gaussLaw_product_vertexSupport, Finset.sum_apply] at this
  exact this

/-- There exists a generator that is a linear combination of the others (linear dependency) -/
theorem gaussLaw_linear_dependency (G : GraphWithCycles V E C) [Nonempty V] :
    ∃ v₀ : V, ∀ w : V,
      gaussLawOperator_vertexSupport G v₀ w =
      1 - ∑ v ∈ Finset.univ.erase v₀, gaussLawOperator_vertexSupport G v w := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  use v₀
  intro w
  have hsum := gaussLaw_constraint_equation G w
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v₀)] at hsum
  -- In ZMod 2: a + b = 1 implies a = 1 - b
  calc gaussLawOperator_vertexSupport G v₀ w
      = gaussLawOperator_vertexSupport G v₀ w + 0 := by ring
    _ = gaussLawOperator_vertexSupport G v₀ w +
        (∑ v ∈ Finset.univ.erase v₀, gaussLawOperator_vertexSupport G v w -
         ∑ v ∈ Finset.univ.erase v₀, gaussLawOperator_vertexSupport G v w) := by ring
    _ = (gaussLawOperator_vertexSupport G v₀ w +
         ∑ v ∈ Finset.univ.erase v₀, gaussLawOperator_vertexSupport G v w) -
        ∑ v ∈ Finset.univ.erase v₀, gaussLawOperator_vertexSupport G v w := by ring
    _ = 1 - ∑ v ∈ Finset.univ.erase v₀, gaussLawOperator_vertexSupport G v w := by rw [hsum]

/-! ## Support Size and Degree

The support size of A_v is 1 + degree(v):
- 1 for the vertex qubit v
- degree(v) for the edge qubits incident to v
-/

/-- The degree of vertex v in the graph -/
noncomputable def vertexDegree (G : GraphWithCycles V E C) (v : V) : ℕ :=
  (G.incidentEdges v).card

/-- The support size of A_v on edge qubits equals the degree of v -/
theorem gaussLawOperator_edgeSupport_size (G : GraphWithCycles V E C) (v : V) :
    (Finset.univ.filter (fun e => gaussLawOperator_edgeSupport G v e = 1)).card =
    vertexDegree G v := by
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, incidentEdges]
  rw [gaussLawOperator_edgeSupport_apply]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Total support size of A_v is 1 (vertex) + degree(v) (edges) -/
noncomputable def gaussLawOperator_totalSupport (G : GraphWithCycles V E C) (v : V) : ℕ :=
  1 + vertexDegree G v

/-! ## Equivalence with Coboundary in Chain Complex

The Gauss law operators are closely related to the coboundary map δ.
Specifically, A_v has edge support δ(e_v) where e_v is the basis vector at v.
-/

/-- The Gauss law operator A_v corresponds to:
    - Vertex support: e_v (basis vector at v)
    - Edge support: δ(e_v) (coboundary of basis vector at v)
    This shows A_v = X_v · ∏_{e∋v} X_e in the binary vector representation. -/
theorem gaussLawOperator_as_coboundary (G : GraphWithCycles V E C) (v : V) :
    gaussLawOperator_edgeSupport G v = G.coboundaryMap (gaussLawOperator_vertexSupport G v) := by
  simp only [gaussLawOperator_vertexSupport, gaussLawOperator_edgeSupport]
  rw [coboundaryMap_basisV]

/-! ## Measurement Property

The key property for the gauging measurement:
Measuring all A_v and multiplying the outcomes (±1) gives the eigenvalue of L.

In our ZMod 2 representation:
- Each measurement outcome is represented as 0 (for +1) or 1 (for -1)
- The product of outcomes corresponds to XOR (addition in ZMod 2)
- The total measurement result equals the eigenvalue of L
-/

/-- Convert a measurement outcome to ZMod 2: +1 → 0, -1 → 1 -/
def measurementToZMod2 : GraphMeasurementOutcome → ZMod 2
  | GraphMeasurementOutcome.plus => 0
  | GraphMeasurementOutcome.minus => 1

/-- Product of measurement outcomes as ZMod 2 sum -/
def measurementProduct (outcomes : V → GraphMeasurementOutcome) : ZMod 2 :=
  ∑ v : V, measurementToZMod2 (outcomes v)

/-- Helper: ZMod 2 values are 0 or 1 -/
private lemma ZMod2_cases' (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- The sum of ZMod 2 values equals the count of 1s mod 2 -/
private lemma ZMod2_sum_eq_card_mod2 {α : Type*} [Fintype α] (f : α → ZMod 2) :
    ∑ a : α, f a = (Finset.univ.filter (fun a => f a = 1)).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => f a = 1)]
  have h1 : ∑ a ∈ Finset.univ.filter (fun a => f a = 1), f a =
            (Finset.univ.filter (fun a => f a = 1)).card := by
    have hcard : ((Finset.univ.filter (fun a => f a = 1)).card : ZMod 2) =
                  ∑ _x ∈ Finset.univ.filter (fun a => f a = 1), (1 : ZMod 2) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul, mul_one]
    rw [hcard]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ha
  have h0 : ∑ a ∈ Finset.univ.filter (fun a => ¬f a = 1), f a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ZMod2_cases' (f a) with h | h
    · exact h
    · exact absurd h ha
  rw [h1, h0, add_zero]

/-- The measurement of all A_v determines the eigenvalue of L.
    The XOR of all measurement outcomes (in ZMod 2) equals the L eigenvalue:
    0 means L eigenvalue +1, 1 means L eigenvalue -1.
    Sum = 0 iff even number of -1 outcomes. -/
theorem gaussLaw_measurement_determines_L (_G : GraphWithCycles V E C)
    (outcomes : V → GraphMeasurementOutcome) :
    measurementProduct outcomes = 0 ↔
    (Finset.univ.filter (fun v => measurementToZMod2 (outcomes v) = 1)).card % 2 = 0 := by
  simp only [measurementProduct]
  rw [ZMod2_sum_eq_card_mod2]
  constructor
  · intro h
    have hval := congrArg ZMod.val h
    simp only [ZMod.val_natCast, ZMod.val_zero] at hval
    exact hval
  · intro h
    have : (Finset.univ.filter (fun v => measurementToZMod2 (outcomes v) = 1)).card % 2 = 0 := h
    have heq : ((Finset.univ.filter (fun v => measurementToZMod2 (outcomes v) = 1)).card : ZMod 2) =
               ((Finset.univ.filter (fun v => measurementToZMod2 (outcomes v) = 1)).card % 2 : ℕ) := by
      exact (ZMod.natCast_mod _ 2).symm
    rw [heq, this]
    simp

/-- If all outcomes are +1, the product is 0 (L eigenvalue +1) -/
theorem gaussLaw_all_plus_implies_L_plus (_G : GraphWithCycles V E C)
    (outcomes : V → GraphMeasurementOutcome) (h : ∀ v, outcomes v = GraphMeasurementOutcome.plus) :
    measurementProduct outcomes = 0 := by
  simp only [measurementProduct, measurementToZMod2]
  rw [Finset.sum_eq_zero]
  intro v _
  rw [h v]

end GraphWithCycles

/-! ## Summary

The Gauss law operators formalize the key concept from the gauging measurement protocol:

1. **Definition**: A_v = X_v ∏_{e∋v} X_e represented as binary vectors over ZMod 2
   - Vertex support: basis vector e_v (1 at v, 0 elsewhere)
   - Edge support: coboundary δ(e_v) (1 at incident edges, 0 elsewhere)

2. **Property 1 (Hermitian)**: A_v² = I
   - In ZMod 2: support + support = 0
   - Implies eigenvalues are ±1

3. **Property 2 (Commutativity)**: [A_v, A_w] = 0 for all v, w
   - X-type operators have zero symplectic form
   - All Gauss law operators mutually commute

4. **Property 3 (Product Constraint)**: ∏_v A_v = L
   - Vertex support: all 1s (= support of L = ∏_v X_v)
   - Edge support: 0 (edges cancel since each appears twice, and X² = I)

5. **Group Structure**: |V| generators with 1 constraint give |V|-1 independent generators
   - The generated abelian group has order 2^{|V|-1}

6. **Measurement**: Multiplying all A_v outcomes gives the L eigenvalue
   - Key to the gauging measurement protocol
-/
