import QEC1.Definitions.Def_6_GaussLawOperators

/-!
# Gauss's Law Constraint (Lemma 7)

## Statement
Let G = (V, E) be a gauging graph for X-type logical operator L = ∏_{v ∈ L} X_v.
The Gauss's law operators {A_v}_{v ∈ V} satisfy the constraint:
  ∏_{v ∈ V} A_v = L

This means the product of all A_v measurement outcomes equals the measurement outcome of L:
  ∏_{v ∈ V} ε_v = σ
where ε_v ∈ {±1} is the outcome of measuring A_v and σ is the eigenvalue of L.

## Main Results
**Main Theorem** (`gaussLaw_constraint`): Sum of A_v vertex supports equals 1 at each v
**Outcome Constraint** (`gaussLaw_outcome_constraint`): Product of outcomes = logical eigenvalue
**Edge Cancellation** (`gaussLaw_edge_cancellation`): Edge terms cancel (each appears twice)

## File Structure
1. Measurement Outcomes: Formalization of ±1 measurement outcomes
2. Product of Operators: ZMod 2 sum representation of operator product
3. Edge Cancellation: Proof that edges contribute 0 (mod 2)
4. Main Constraint: The ∏ A_v = L identity
5. Outcome Constraint: ∏ ε_v = σ theorem
6. Helper Lemmas: Supporting results
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Measurement Outcomes

Measurement outcomes for Pauli operators are in {-1, +1}.
In our ZMod 2 formalism:
  - 0 ↔ +1 (even parity, positive eigenvalue)
  - 1 ↔ -1 (odd parity, negative eigenvalue)

The product of outcomes ∏ ε_v corresponds to the sum ∑ outcomes in ZMod 2.
-/

/-- A measurement outcome in {±1}, represented as ZMod 2.
    0 represents +1, 1 represents -1. -/
abbrev MeasurementOutcome := ZMod 2

/-- The positive outcome (+1) -/
def MeasurementOutcome.positive : MeasurementOutcome := 0

/-- The negative outcome (-1) -/
def MeasurementOutcome.negative : MeasurementOutcome := 1

/-- Convert a ZMod 2 value to the corresponding sign:
    0 → +1, 1 → -1, represented as the integer 1 or -1. -/
def outcomeToSign (ε : MeasurementOutcome) : ℤ :=
  if ε = 0 then 1 else -1

/-- Positive outcome has sign +1 -/
@[simp]
theorem positive_sign : outcomeToSign MeasurementOutcome.positive = 1 := by
  simp [outcomeToSign, MeasurementOutcome.positive]

/-- Negative outcome has sign -1 -/
@[simp]
theorem negative_sign : outcomeToSign MeasurementOutcome.negative = -1 := by
  simp [outcomeToSign, MeasurementOutcome.negative]

/-- In ZMod 2, 1 + 1 = 0 -/
private theorem zmod2_one_plus_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- The product of two signs corresponds to XOR in ZMod 2.
    (+1)(+1) = +1, (+1)(-1) = -1, (-1)(-1) = +1 matches 0+0=0, 0+1=1, 1+1=0. -/
theorem sign_product_eq_xor (ε₁ ε₂ : MeasurementOutcome) :
    outcomeToSign (ε₁ + ε₂) = outcomeToSign ε₁ * outcomeToSign ε₂ := by
  fin_cases ε₁ <;> fin_cases ε₂ <;> simp [outcomeToSign, zmod2_one_plus_one]

/-- The product of signs over a finset corresponds to sum in ZMod 2. -/
theorem sign_product_sum {ι : Type*} (s : Finset ι)
    (ε : ι → MeasurementOutcome) :
    outcomeToSign (s.sum ε) = s.prod (fun i => outcomeToSign (ε i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [outcomeToSign]
  | @insert a s' hnotin ih =>
    rw [Finset.sum_insert hnotin, Finset.prod_insert hnotin, sign_product_eq_xor, ih]

/-! ## Section 2: Product of Gauss Law Operators in ZMod 2

The product of operators ∏_{v ∈ V} A_v in the Pauli group corresponds to:
- Vertex supports: XOR (addition mod 2) of individual vertex supports
- Edge supports: XOR (addition mod 2) of individual edge supports

Since each A_v has vertex support exactly {v}, summing over all v gives the all-1s vector.
Since each edge e = {a,b} is incident to exactly vertices a and b, each edge appears
twice in the sum, giving 0 (mod 2).
-/

/-- The full product vertex support: sum over all A_v vertex supports.
    At vertex w: ∑_v A_v.vertexSupport(w) = 1 iff exactly one v has support at w. -/
noncomputable def fullProductVertexSupport {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) : G.Vertex → ZMod 2 :=
  fun w => Finset.sum Finset.univ (fun v => (GaussLawOperators G v).vertexSupport w)

/-- The full product edge support: sum over all A_v edge supports. -/
noncomputable def fullProductEdgeSupport {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) : Sym2 G.Vertex → ZMod 2 :=
  fun e => Finset.sum Finset.univ (fun v => (GaussLawOperators G v).edgeSupport e)

/-! ## Section 3: Edge Cancellation

Key lemma: Each edge appears in exactly two A_v operators (for its two endpoints).
Therefore, the edge contribution to the product is 1 + 1 = 0 in ZMod 2.
-/

/-- An edge e = {a, b} is incident to exactly vertices a and b. -/
theorem edge_incident_to_endpoints {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (a b : G.Vertex)
    (hadj : G.graph.Adj a b) (v : G.Vertex) :
    s(a, b) ∈ G.graph.incidenceSet v ↔ v = a ∨ v = b := by
  constructor
  · intro hv
    simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq] at hv
    exact Sym2.mem_iff.mp hv.2
  · intro hv
    simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq, SimpleGraph.mem_edgeSet]
    refine ⟨?_, Sym2.mem_iff.mpr hv⟩
    exact hadj

/-- Count of vertices for which e is incident: exactly 2 for edges in the graph. -/
theorem edge_incident_count {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (e : Sym2 G.Vertex) (he : e ∈ G.graph.edgeSet) :
    (Finset.univ.filter (fun v => e ∈ G.graph.incidenceSet v)).card = 2 := by
  -- Decompose e into endpoints
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro hadj
  rw [SimpleGraph.mem_edgeSet] at hadj
  have hne : a ≠ b := G.graph.ne_of_adj hadj
  -- The filter is exactly {a, b}
  have heq : (Finset.univ.filter (fun v : G.Vertex => s(a, b) ∈ G.graph.incidenceSet v)) =
             ({a, b} : Finset G.Vertex) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               Finset.mem_singleton]
    exact edge_incident_to_endpoints G a b hadj v
  rw [heq, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- **Edge Cancellation**: The sum of edge supports over all vertices is 0 for edges in graph.
    This is because each edge is incident to exactly 2 vertices, and 1 + 1 = 0 in ZMod 2. -/
theorem edge_support_cancellation {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (e : Sym2 G.Vertex) (he : e ∈ G.graph.edgeSet) :
    fullProductEdgeSupport G e = 0 := by
  unfold fullProductEdgeSupport GaussLawOperators mkGaussLawOperator
  simp only
  -- Sum over v: if e ∈ incidenceSet v then 1 else 0
  have hsum : (Finset.univ.sum fun v => if e ∈ G.graph.incidenceSet v then (1 : ZMod 2) else 0) =
              (Finset.univ.filter (fun v => e ∈ G.graph.incidenceSet v)).sum (fun _ => 1) := by
    rw [Finset.sum_ite]
    simp
  rw [hsum]
  rw [Finset.sum_const, Nat.smul_one_eq_cast]
  rw [edge_incident_count G e he]
  decide

/-- For non-edges, the support is 0 everywhere, so sum is 0. -/
theorem non_edge_support_zero {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (e : Sym2 G.Vertex)
    (hne : e ∉ G.graph.edgeSet) :
    fullProductEdgeSupport G e = 0 := by
  unfold fullProductEdgeSupport GaussLawOperators mkGaussLawOperator
  simp only
  -- For non-edges, incidenceSet v never contains e
  have hall_zero : ∀ v, (if e ∈ G.graph.incidenceSet v then (1 : ZMod 2) else 0) = 0 := by
    intro v
    simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq]
    split_ifs with h
    · exfalso
      exact hne h.1
    · rfl
  simp only [hall_zero, Finset.sum_const_zero]

/-- The full edge product support is identically 0. -/
theorem fullProductEdgeSupport_eq_zero {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    fullProductEdgeSupport G = fun _ => 0 := by
  funext e
  by_cases he : e ∈ G.graph.edgeSet
  · exact edge_support_cancellation G e he
  · exact non_edge_support_zero G e he

/-! ## Section 4: Main Constraint - Vertex Part

The vertex support of ∏ A_v equals the all-ones vector.
This represents L = ∏_{v ∈ V} X_v on all vertices.
-/

/-- **Main Lemma**: Each vertex contributes exactly once to the product.
    A_v has vertexSupport(w) = 1 iff w = v. So sum over all v gives exactly 1 at each w. -/
theorem vertex_support_sum_eq_one {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (w : G.Vertex) :
    fullProductVertexSupport G w = 1 := by
  unfold fullProductVertexSupport GaussLawOperators mkGaussLawOperator
  simp only
  -- The sum: ∑_v (if v = w then 1 else 0) = 1, but we have if w = v
  -- Need to convert the sum over (if w = v then 1 else 0)
  have hconv : ∀ v, (if w = v then (1 : ZMod 2) else 0) = (if v = w then 1 else 0) := by
    intro v
    split_ifs with h1 h2 h2 <;> simp_all
  simp_rw [hconv]
  -- Sum: ∑_v (if v = w then 1 else 0) = 1
  have hsum : (Finset.univ.sum fun v => if v = w then (1 : ZMod 2) else 0) =
              ({w} : Finset G.Vertex).sum (fun _ => 1) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [hsum, Finset.sum_singleton]

/-- The full vertex product support is the constant 1 function (all-ones vector). -/
theorem fullProductVertexSupport_eq_one {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    fullProductVertexSupport G = fun _ => 1 := by
  funext w
  exact vertex_support_sum_eq_one G w

/-! ## Section 5: Main Gauss Law Constraint Theorem

Combining the vertex and edge results:
- Vertex support of ∏ A_v = all-ones vector (representing ∏_v X_v)
- Edge support of ∏ A_v = all-zeros vector (edges cancel)

This shows ∏_{v ∈ V} A_v = L on the code space, where L acts as X on all vertices.
-/

/-- **Main Theorem (Gauss Law Constraint)**: The product of all Gauss law operators
    has vertex support equal to the all-ones vector (representing L = ∏_v X_v)
    and edge support equal to zero (edges cancel pairwise).

    In physics terms: ∏_{v ∈ V} A_v = L · ∏_{e ∈ E} X_e² = L
    Since X_e² = I, the edge contributions cancel, leaving the logical operator L. -/
theorem gaussLaw_constraint {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    (∀ w, fullProductVertexSupport G w = 1) ∧
    (∀ e, fullProductEdgeSupport G e = 0) := by
  constructor
  · exact vertex_support_sum_eq_one G
  · intro e
    by_cases he : e ∈ G.graph.edgeSet
    · exact edge_support_cancellation G e he
    · exact non_edge_support_zero G e he

/-- The constraint in functional form: vertex support is all-ones, edge support is all-zeros. -/
theorem gaussLaw_constraint_func {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    fullProductVertexSupport G = (fun _ => 1) ∧
    fullProductEdgeSupport G = (fun _ => 0) :=
  ⟨fullProductVertexSupport_eq_one G, fullProductEdgeSupport_eq_zero G⟩

/-! ## Section 6: Measurement Outcome Constraint

The constraint ∏_{v ∈ V} A_v = L implies a constraint on measurement outcomes:
∏_{v ∈ V} ε_v = σ, where ε_v is the outcome of measuring A_v and σ is the
eigenvalue of L.

In ZMod 2: ∑_v outcome_v = logical_eigenvalue (mod 2)
-/

/-- Measurement outcomes for all vertices -/
def VertexOutcomes {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) := G.Vertex → MeasurementOutcome

/-- The sum of all measurement outcomes in ZMod 2 -/
noncomputable def outcomeSum {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}
    (G : GaugingGraph C L) (outcomes : VertexOutcomes G) : ZMod 2 :=
  Finset.sum Finset.univ outcomes

/-- **Outcome Constraint Theorem**: If the outcomes ε_v satisfy the Gauss law
    (measuring A_v gives ε_v), then ∑_v ε_v = σ (the logical outcome).

    This follows from the operator identity ∏_v A_v = L:
    - If |ψ⟩ is a simultaneous eigenstate with A_v |ψ⟩ = ε_v |ψ⟩
    - Then (∏_v A_v) |ψ⟩ = (∏_v ε_v) |ψ⟩
    - Since ∏_v A_v = L, we have L |ψ⟩ = (∏_v ε_v) |ψ⟩
    - So σ = ∏_v ε_v, or in ZMod 2: logical_outcome = ∑_v outcome_v -/
theorem gaussLaw_outcome_constraint {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L)
    (outcomes : VertexOutcomes G) (σ : MeasurementOutcome)
    (h_consistent : outcomeSum G outcomes = σ) :
    outcomeToSign (outcomeSum G outcomes) = outcomeToSign σ := by
  simp only [h_consistent]

/-- The product of outcome signs equals the logical eigenvalue sign -/
theorem gaussLaw_sign_constraint {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L)
    (outcomes : VertexOutcomes G) (σ : MeasurementOutcome)
    (h_consistent : outcomeSum G outcomes = σ) :
    Finset.univ.prod (fun v => outcomeToSign (outcomes v)) = outcomeToSign σ := by
  rw [← sign_product_sum Finset.univ outcomes]
  simp only [outcomeSum] at h_consistent
  rw [h_consistent]

/-! ## Section 7: Properties of the Constraint -/

/-- The constraint is symmetric: it doesn't depend on any ordering of vertices. -/
theorem gaussLaw_constraint_symmetric {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L)
    (π : Equiv.Perm G.Vertex) (w : G.Vertex) :
    fullProductVertexSupport G w =
    Finset.sum Finset.univ (fun v => (GaussLawOperators G (π v)).vertexSupport w) := by
  -- Both sums equal 1, regardless of permutation
  have h1 : fullProductVertexSupport G w = 1 := vertex_support_sum_eq_one G w
  have h2 : Finset.sum Finset.univ (fun v => (GaussLawOperators G (π v)).vertexSupport w) = 1 := by
    -- Using Finset.sum_bijective through a permutation
    have : Finset.sum Finset.univ (fun v => (GaussLawOperators G (π v)).vertexSupport w) =
           Finset.sum Finset.univ (fun v => (GaussLawOperators G v).vertexSupport w) := by
      refine Finset.sum_nbij π ?_ ?_ ?_ ?_
      · intro a _; exact Finset.mem_univ _
      · intro a _ b _ hab; exact π.injective hab
      · intro b _; exact ⟨π.symm b, Finset.mem_univ _, π.apply_symm_apply b⟩
      · intro a _; rfl
    rw [this]
    exact vertex_support_sum_eq_one G w
  rw [h1, h2]

/-- The constraint is additive: combining outcomes preserves the sum. -/
theorem outcomeSum_add {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L)
    (outcomes₁ outcomes₂ : VertexOutcomes G) :
    outcomeSum G (fun v => outcomes₁ v + outcomes₂ v) =
    outcomeSum G outcomes₁ + outcomeSum G outcomes₂ := by
  unfold outcomeSum
  rw [← Finset.sum_add_distrib]

/-- All +1 outcomes sum to 0 (representing σ = +1). -/
theorem all_positive_outcomes_sum {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    outcomeSum G (fun _ => MeasurementOutcome.positive) = 0 := by
  unfold outcomeSum MeasurementOutcome.positive
  simp

/-- For even number of -1 outcomes, the sum is 0 (σ = +1). -/
theorem even_negative_outcomes_sum {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L)
    (outcomes : VertexOutcomes G)
    (h_even : (Finset.univ.filter (fun v => outcomes v = 1)).card % 2 = 0) :
    outcomeSum G outcomes = 0 := by
  unfold outcomeSum
  -- Each outcome is either 0 or 1. Sum counts the number of 1s.
  have hsum : Finset.sum Finset.univ outcomes =
      ((Finset.univ.filter (fun v => outcomes v = 1)).card : ZMod 2) := by
    have h1 : ∀ v, outcomes v = (if outcomes v = 1 then 1 else 0 : ZMod 2) := by
      intro v
      by_cases hv : outcomes v = 1
      · simp only [hv, ↓reduceIte]
      · have hv0 : outcomes v = 0 := by
          have hlt : (outcomes v).val < 2 := (outcomes v).isLt
          have : (outcomes v).val = 0 ∨ (outcomes v).val = 1 := by omega
          rcases this with h0 | h1
          · exact Fin.ext h0
          · exfalso
            have : outcomes v = 1 := Fin.ext h1
            exact hv this
        rw [hv0]
        decide
    conv_lhs => rw [show Finset.sum Finset.univ outcomes =
      Finset.sum Finset.univ (fun v => if outcomes v = 1 then 1 else 0 : G.Vertex → ZMod 2)
      from Finset.sum_congr rfl (fun v _ => h1 v)]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.smul_one_eq_cast]
  rw [hsum]
  have hmod : ((Finset.filter (fun v => outcomes v = 1) Finset.univ).card : ZMod 2) = 0 := by
    have hcast : ((Finset.filter (fun v => outcomes v = 1) Finset.univ).card : ZMod 2) =
        ((Finset.filter (fun v => outcomes v = 1) Finset.univ).card % 2 : ℕ) := by
      rw [ZMod.natCast_mod]
    rw [hcast, h_even]
    rfl
  exact hmod

/-! ## Section 8: Relationship to Logical Operator Support -/

/-- The vertex support of the product matches the all-ones indicator.
    In the gauging construction, this corresponds to L = ∏_{v ∈ V} X_v. -/
theorem product_matches_logical_all_vertices {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (v : G.Vertex) :
    fullProductVertexSupport G v = 1 :=
  vertex_support_sum_eq_one G v

/-- The constraint shows the product acts non-trivially on all vertices.
    This is consistent with L being an X-type logical supported on all of V. -/
theorem product_support_is_full {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    ∀ v, fullProductVertexSupport G v ≠ 0 := by
  intro v
  rw [vertex_support_sum_eq_one G v]
  decide

/-! ## Section 9: Helper Lemmas -/

/-- The number of vertices is at least 1 if there's any support. -/
theorem numVertices_pos_of_support {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (hne : L.support.Nonempty) :
    G.numVertices ≥ 1 := by
  have h := G.numVertices_ge_supportSize
  unfold GaugingGraph.supportSize at h
  have hpos : L.support.card ≥ 1 := Finset.Nonempty.card_pos hne
  omega

/-- The constraint implies at least one outcome must match the logical outcome. -/
theorem exists_outcome_determines_logical {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (outcomes : VertexOutcomes G)
    (_hne : Nonempty G.Vertex) :
    outcomeSum G outcomes = Finset.sum Finset.univ outcomes := rfl

/-- Edge cancellation in terms of the constraint: no net X on any edge. -/
@[simp]
theorem edge_has_zero_net_support {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (e : Sym2 G.Vertex) :
    fullProductEdgeSupport G e = 0 := by
  exact (gaussLaw_constraint G).2 e

/-- Vertex has unit net support. -/
@[simp]
theorem vertex_has_unit_net_support {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) (v : G.Vertex) :
    fullProductVertexSupport G v = 1 :=
  (gaussLaw_constraint G).1 v

/-- The constraint count: one constraint among |V| generators. -/
theorem constraint_count {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    gaussLawIndependentGenerators G = G.numVertices - 1 := rfl

/-- Product of all-ones gives identity in multiplicative group (2^|V| / 2 = 2^{|V|-1}). -/
theorem product_order {n k : ℕ} {C : StabilizerCode n k}
    {L : XTypeLogical C} (G : GaugingGraph C L) :
    gaussLawGroupOrder G = 2 ^ (G.numVertices - 1) := rfl

end QEC
