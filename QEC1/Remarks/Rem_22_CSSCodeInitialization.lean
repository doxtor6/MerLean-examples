import QEC1.Remarks.Rem_21_RelationToCohenEtAl
import QEC1.Remarks.Rem_14_HypergraphGeneralization

/-!
# CSS Code Initialization (Remark 22)

## Statement
The generalized (hypergraph) gauging measurement can implement CSS code initialization:

**Standard CSS initialization**: Prepare |0⟩^⊗n, then measure X-type checks.

**Gauging interpretation**:
- Start with a trivial code having one dummy vertex per X-type check
- Apply generalized gauging using the hypergraph corresponding to Z-type checks
- The "ungauging" step performs Z measurement on all qubits (read-out)

**Steane-style measurement**: Combine initialization gauging with a pairwise XX gauging
measurement between data and ancilla blocks:
1. Initialize ancilla block via gauging (as above)
2. Apply gauging measurement of XX on matching qubit pairs
3. Ungauge to read out Z on all ancilla qubits

This recovers Steane's method for fault-tolerant syndrome extraction.

## Formalization Approach

This remark explains the conceptual connection between CSS initialization and the
hypergraph gauging framework from Remark 14. We formalize the key algebraic property
that makes this work:

**Main mathematical content**:
The CSS orthogonality condition (every X-check commutes with every Z-check) implies
that all X-type checks lie in the kernel of the Z-check hypergraph transpose matrix.
This is the algebraic foundation for "measuring X-checks via Z-hypergraph gauging".

We formalize:
1. CSS code structure with X-type and Z-type checks
2. The Z-check hypergraph for initialization
3. **Core theorem**: CSS orthogonality ⟹ X-checks ∈ ker(H^T)
4. Steane measurement structure (data + ancilla blocks)

## Main Results
- `CSSCode`: CSS code structure with X and Z type checks
- `CSSCode.xCheck_in_kernel`: X-checks are in ker(H^T) by CSS orthogonality
- `CSSCode.xCheck_commutes_with_hyperedge`: X-checks commute with Z-hyperedge operators
- `CSSCode.xChecks_in_measurable_group`: X-checks are measurable via hypergraph gauging
- `pairwiseXX_weight`: Pairwise XX operators have weight 2

## File Structure
1. CSS Code Definition: X-type and Z-type checks with orthogonality
2. Initialization Hypergraph: Z-checks as hyperedges
3. Kernel Theorem: X-checks in ker(H^T)
4. Steane Measurement: Data/ancilla structure
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: CSS Code Structure

A CSS (Calderbank-Shor-Steane) code has two types of check generators:
- X-type checks: Products of X operators (define X-stabilizers)
- Z-type checks: Products of Z operators (define Z-stabilizers)

The CSS condition requires: every X-check commutes with every Z-check.
In support notation: |supp(X_check) ∩ supp(Z_check)| ≡ 0 (mod 2).
-/

/-- A CSS (Calderbank-Shor-Steane) code.
    CSS codes have separate X-type and Z-type checks satisfying orthogonality. -/
structure CSSCode where
  /-- Number of physical qubits -/
  numQubits : ℕ
  /-- Number of X-type check generators -/
  numXChecks : ℕ
  /-- Number of Z-type check generators -/
  numZChecks : ℕ
  /-- We have at least one qubit -/
  numQubits_pos : 0 < numQubits
  /-- Support of X-type check i (qubits where X acts) -/
  xCheckSupport : Fin numXChecks → Finset (Fin numQubits)
  /-- Support of Z-type check i (qubits where Z acts) -/
  zCheckSupport : Fin numZChecks → Finset (Fin numQubits)
  /-- X-checks have non-empty support -/
  xCheck_nonempty : ∀ i, (xCheckSupport i).Nonempty
  /-- Z-checks have non-empty support -/
  zCheck_nonempty : ∀ i, (zCheckSupport i).Nonempty
  /-- CSS orthogonality: every X-check commutes with every Z-check
      Symplectic form = |X_support ∩ Z_support| mod 2 = 0 -/
  css_orthogonality : ∀ (i : Fin numXChecks) (j : Fin numZChecks),
    (xCheckSupport i ∩ zCheckSupport j).card % 2 = 0

namespace CSSCode

variable (C : CSSCode)

/-- Number of logical qubits (informally: n - rx - rz where rx, rz are ranks) -/
def numLogicalQubits : ℕ := C.numQubits - C.numXChecks - C.numZChecks

/-- The weight of an X-type check -/
def xCheckWeight (i : Fin C.numXChecks) : ℕ := (C.xCheckSupport i).card

/-- The weight of a Z-type check -/
def zCheckWeight (i : Fin C.numZChecks) : ℕ := (C.zCheckSupport i).card

end CSSCode

/-! ## Section 2: Initialization Hypergraph

For CSS initialization via gauging, we use the Z-type checks to define the hypergraph:
- Vertices = physical qubits (indices 0, ..., n-1)
- Hyperedges = supports of Z-type checks

This hypergraph defines the "gauging structure" for initialization.
-/

/-- The initialization hypergraph for a CSS code.
    Vertices are qubits, hyperedges are Z-check supports. -/
def CSSCode.initializationHypergraph (C : CSSCode) : Hypergraph where
  Vertex := Fin C.numQubits
  EdgeIdx := Fin C.numZChecks
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  vertexDecEq := inferInstance
  edgeDecEq := inferInstance
  hyperedge := C.zCheckSupport
  hyperedge_nonempty := C.zCheck_nonempty

/-- The initialization hypergraph vertices are the qubits -/
theorem CSSCode.initHypergraph_vertex (C : CSSCode) :
    C.initializationHypergraph.Vertex = Fin C.numQubits := rfl

/-- The initialization hypergraph edges correspond to Z-checks -/
theorem CSSCode.initHypergraph_edge_count (C : CSSCode) :
    C.initializationHypergraph.numEdges = C.numZChecks := by
  unfold Hypergraph.numEdges CSSCode.initializationHypergraph
  simp only [Fintype.card_fin]

/-- The initialization hypergraph vertices count -/
theorem CSSCode.initHypergraph_vertex_count (C : CSSCode) :
    C.initializationHypergraph.numVertices = C.numQubits := by
  unfold Hypergraph.numVertices CSSCode.initializationHypergraph
  simp only [Fintype.card_fin]

/-! ## Section 3: X-Checks in Kernel of H^T

The key algebraic fact: CSS orthogonality ensures that every X-type check
is in the kernel of the Z-check hypergraph transpose matrix.

This is why gauging with the Z-check hypergraph allows measuring X-checks:
operators in ker(H^T) commute with all Z-type hyperedge operators B_e.
-/

/-- X-check support as an operator support function over ZMod 2 -/
def CSSCode.xCheckAsOperator (C : CSSCode) (i : Fin C.numXChecks) :
    XOperatorSupport C.initializationHypergraph :=
  fun v => if v ∈ C.xCheckSupport i then 1 else 0

/-- **Core Theorem**: X-checks are in the kernel of the hypergraph transpose by CSS orthogonality.

    This is the algebraic foundation for CSS initialization via gauging:
    H^T · x_i = 0 where x_i is the indicator vector of the i-th X-check support.

    Proof: (H^T · x_i)_e = Σ_v H[v,e] · x_i[v] = |xSupp_i ∩ zSupp_e| ≡ 0 (mod 2)
    by the CSS orthogonality condition. -/
theorem CSSCode.xCheck_in_kernel (C : CSSCode) (i : Fin C.numXChecks) :
    inKernelOfTranspose C.initializationHypergraph (C.xCheckAsOperator i) := by
  intro e
  unfold matrixVectorProduct
  simp only [incidenceMatrix_apply]
  unfold CSSCode.xCheckAsOperator CSSCode.initializationHypergraph
  simp only
  -- The sum is |xCheckSupport i ∩ zCheckSupport e| mod 2
  have h_transform : ∀ v, (if v ∈ C.zCheckSupport e then (1 : ZMod 2) else 0) *
      (if v ∈ C.xCheckSupport i then (1 : ZMod 2) else 0) =
      if v ∈ C.xCheckSupport i ∧ v ∈ C.zCheckSupport e then 1 else 0 := by
    intro v
    by_cases hx : v ∈ C.xCheckSupport i
    · by_cases hz : v ∈ C.zCheckSupport e
      · simp [hx, hz]
      · simp [hx, hz]
    · by_cases hz : v ∈ C.zCheckSupport e
      · simp [hx, hz]
      · simp [hx, hz]
  simp_rw [h_transform]
  -- The sum counts elements in the intersection
  have h_count : Finset.sum Finset.univ (fun v =>
      if v ∈ C.xCheckSupport i ∧ v ∈ C.zCheckSupport e then (1 : ZMod 2) else 0) =
      (C.xCheckSupport i ∩ C.zCheckSupport e).card := by
    rw [Finset.sum_boole]
    have h_eq : (Finset.filter
        (fun v => v ∈ C.xCheckSupport i ∧ v ∈ C.zCheckSupport e) Finset.univ) =
        C.xCheckSupport i ∩ C.zCheckSupport e := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    rw [h_eq]
  rw [h_count]
  -- Apply CSS orthogonality: |intersection| ≡ 0 (mod 2)
  have h_even := C.css_orthogonality i e
  have hval : ((C.xCheckSupport i ∩ C.zCheckSupport e).card : ZMod 2) = 0 := by
    have hmod : (C.xCheckSupport i ∩ C.zCheckSupport e).card % 2 = 0 := h_even
    have hcast : ((C.xCheckSupport i ∩ C.zCheckSupport e).card : ZMod 2).val =
        (C.xCheckSupport i ∩ C.zCheckSupport e).card % 2 := by
      exact @ZMod.val_natCast 2 (C.xCheckSupport i ∩ C.zCheckSupport e).card
    rw [hmod] at hcast
    exact Fin.ext hcast
  exact hval

/-- X-checks commute with all Z-type hyperedge operators.
    This follows from the kernel characterization. -/
theorem CSSCode.xCheck_commutes_with_hyperedge (C : CSSCode) (i : Fin C.numXChecks) :
    commutesWithAllChecks C.initializationHypergraph (C.xCheckAsOperator i) := by
  rw [commutes_iff_in_kernel]
  exact C.xCheck_in_kernel i

/-- X-checks are in the measurable group of the initialization hypergraph.
    This means they can be measured via the hypergraph gauging procedure. -/
theorem CSSCode.xChecks_in_measurable_group (C : CSSCode) (i : Fin C.numXChecks) :
    C.xCheckAsOperator i ∈ measurableGroup C.initializationHypergraph := by
  simp only [measurableGroup, Set.mem_setOf_eq]
  exact C.xCheck_commutes_with_hyperedge i

/-! ## Section 4: Dummy Vertex Structure

In the gauging interpretation of CSS initialization, we start with a "trivial code"
having one dummy vertex per X-type check. Each dummy corresponds to an X-check
measurement outcome.
-/

/-- Vertex type for CSS initialization: physical qubits plus dummy vertices -/
inductive CSSInitVertex (C : CSSCode) where
  | qubit : Fin C.numQubits → CSSInitVertex C
  | dummy : Fin C.numXChecks → CSSInitVertex C
  deriving DecidableEq

namespace CSSInitVertex

variable {C : CSSCode}

/-- Qubit vertices are injective -/
theorem qubit_injective : Function.Injective (qubit : Fin C.numQubits → CSSInitVertex C) := by
  intro i j h
  cases h
  rfl

/-- Dummy vertices are injective -/
theorem dummy_injective : Function.Injective (dummy : Fin C.numXChecks → CSSInitVertex C) := by
  intro i j h
  cases h
  rfl

/-- Qubits and dummies are disjoint -/
theorem qubit_ne_dummy (i : Fin C.numQubits) (j : Fin C.numXChecks) :
    qubit i ≠ dummy j := by intro h; cases h

end CSSInitVertex

/-- Fintype instance for CSSInitVertex -/
instance (C : CSSCode) : Fintype (CSSInitVertex C) :=
  Fintype.ofEquiv (Fin C.numQubits ⊕ Fin C.numXChecks) {
    toFun := fun x => match x with
      | Sum.inl i => CSSInitVertex.qubit i
      | Sum.inr i => CSSInitVertex.dummy i
    invFun := fun v => match v with
      | CSSInitVertex.qubit i => Sum.inl i
      | CSSInitVertex.dummy i => Sum.inr i
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun v => by cases v <;> rfl
  }

/-- Total vertices = qubits + dummies (one dummy per X-check) -/
theorem cssInitVertex_card (C : CSSCode) :
    Fintype.card (CSSInitVertex C) = C.numQubits + C.numXChecks := by
  have h := Fintype.card_congr (β := Fin C.numQubits ⊕ Fin C.numXChecks) {
    toFun := fun v => match v with
      | CSSInitVertex.qubit i => Sum.inl i
      | CSSInitVertex.dummy i => Sum.inr i
    invFun := fun x => match x with
      | Sum.inl i => CSSInitVertex.qubit i
      | Sum.inr i => CSSInitVertex.dummy i
    left_inv := fun v => by cases v <;> rfl
    right_inv := fun x => by cases x <;> rfl
  }
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  exact h

/-! ## Section 5: Steane-Style Measurement Structure

Steane's method for fault-tolerant syndrome extraction:
1. Initialize ancilla block (copy of code) via CSS initialization
2. Apply transversal CNOT between data and ancilla (pairwise XX gauging)
3. Measure ancilla in Z basis (ungauging readout)

We formalize the data/ancilla block structure and the pairwise XX operators.
-/

/-- Vertex type for Steane measurement: data block + ancilla block -/
inductive SteaneVertex (n : ℕ) where
  | data : Fin n → SteaneVertex n
  | ancilla : Fin n → SteaneVertex n
  deriving DecidableEq

namespace SteaneVertex

variable {n : ℕ}

/-- Get the index of the qubit -/
def index : SteaneVertex n → Fin n
  | data i => i
  | ancilla i => i

/-- Data vertices are injective -/
theorem data_injective : Function.Injective (data : Fin n → SteaneVertex n) := by
  intro i j h; cases h; rfl

/-- Ancilla vertices are injective -/
theorem ancilla_injective : Function.Injective (ancilla : Fin n → SteaneVertex n) := by
  intro i j h; cases h; rfl

/-- Data and ancilla are disjoint -/
theorem data_ne_ancilla (i j : Fin n) : data i ≠ ancilla j := by
  intro h; cases h

end SteaneVertex

/-- Fintype instance for SteaneVertex -/
instance {n : ℕ} [NeZero n] : Fintype (SteaneVertex n) :=
  Fintype.ofEquiv (Fin n ⊕ Fin n) {
    toFun := fun x => match x with
      | Sum.inl i => SteaneVertex.data i
      | Sum.inr i => SteaneVertex.ancilla i
    invFun := fun v => match v with
      | SteaneVertex.data i => Sum.inl i
      | SteaneVertex.ancilla i => Sum.inr i
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun v => by cases v <;> rfl
  }

/-- Total Steane vertices = 2n (data block + ancilla block) -/
theorem steaneVertex_card {n : ℕ} [NeZero n] :
    Fintype.card (SteaneVertex n) = 2 * n := by
  have h := Fintype.card_congr (β := Fin n ⊕ Fin n) {
    toFun := fun v => match v with
      | SteaneVertex.data i => Sum.inl i
      | SteaneVertex.ancilla i => Sum.inr i
    invFun := fun x => match x with
      | Sum.inl i => SteaneVertex.data i
      | Sum.inr i => SteaneVertex.ancilla i
    left_inv := fun v => by cases v <;> rfl
    right_inv := fun x => by cases x <;> rfl
  }
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- Pairwise XX operator support: 1 on data[i] and ancilla[i], 0 elsewhere.
    This represents the XX operator on matching qubit pairs for Steane measurement. -/
def pairwiseXXSupport {n : ℕ} [NeZero n] (i : Fin n) :
    SteaneVertex n → ZMod 2 := fun v =>
  match v with
  | SteaneVertex.data j => if j = i then 1 else 0
  | SteaneVertex.ancilla j => if j = i then 1 else 0

/-- **Weight of pairwise XX operator is 2**.
    Each XX operator acts on exactly 2 qubits: data[i] and ancilla[i]. -/
theorem pairwiseXX_weight {n : ℕ} [NeZero n] (i : Fin n) :
    (Finset.filter (fun v => pairwiseXXSupport i v = 1) Finset.univ).card = 2 := by
  have h_eq : Finset.filter (fun v => pairwiseXXSupport i v = 1) Finset.univ =
      {SteaneVertex.data i, SteaneVertex.ancilla i} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hv
      cases v with
      | data j =>
        left
        simp only [pairwiseXXSupport] at hv
        split_ifs at hv with h
        · exact congr_arg SteaneVertex.data h
        · exact absurd hv (by decide : ¬(0 : ZMod 2) = 1)
      | ancilla j =>
        right
        simp only [pairwiseXXSupport] at hv
        split_ifs at hv with h
        · exact congr_arg SteaneVertex.ancilla h
        · exact absurd hv (by decide : ¬(0 : ZMod 2) = 1)
    · intro hv
      cases hv with
      | inl h => simp [pairwiseXXSupport, h]
      | inr h => simp [pairwiseXXSupport, h]
  rw [h_eq]
  have h_ne : SteaneVertex.data i ≠ SteaneVertex.ancilla i := SteaneVertex.data_ne_ancilla i i
  rw [Finset.card_insert_of_notMem (by simp [h_ne]), Finset.card_singleton]

/-! ## Section 6: Measurable Group Properties -/

/-- The identity operator is in the measurable group -/
theorem identity_measurable (C : CSSCode) :
    (fun _ => 0) ∈ measurableGroup C.initializationHypergraph :=
  zero_in_measurableGroup C.initializationHypergraph

/-- Sum (XOR) of X-checks is measurable (closed under addition in ZMod 2) -/
theorem xCheck_sum_measurable (C : CSSCode)
    (i j : Fin C.numXChecks) :
    (fun v => C.xCheckAsOperator i v + C.xCheckAsOperator j v) ∈
    measurableGroup C.initializationHypergraph := by
  apply sum_in_measurableGroup
  · exact C.xChecks_in_measurable_group i
  · exact C.xChecks_in_measurable_group j

/-! ## Section 7: X-Check Operator Properties -/

/-- X-check operator at support is 1 -/
@[simp]
theorem xCheckAsOperator_at_support (C : CSSCode) (i : Fin C.numXChecks)
    (v : Fin C.numQubits) (h : v ∈ C.xCheckSupport i) :
    C.xCheckAsOperator i v = 1 := by
  simp only [CSSCode.xCheckAsOperator, h, ↓reduceIte]

/-- X-check operator outside support is 0 -/
@[simp]
theorem xCheckAsOperator_outside_support (C : CSSCode) (i : Fin C.numXChecks)
    (v : Fin C.numQubits) (h : v ∉ C.xCheckSupport i) :
    C.xCheckAsOperator i v = 0 := by
  simp only [CSSCode.xCheckAsOperator, h, ↓reduceIte]

/-- X-check weights are positive -/
theorem xCheck_weight_pos (C : CSSCode) (i : Fin C.numXChecks) :
    0 < C.xCheckWeight i := by
  unfold CSSCode.xCheckWeight
  exact Finset.Nonempty.card_pos (C.xCheck_nonempty i)

/-- Z-check weights are positive -/
theorem zCheck_weight_pos (C : CSSCode) (i : Fin C.numZChecks) :
    0 < C.zCheckWeight i := by
  unfold CSSCode.zCheckWeight
  exact Finset.Nonempty.card_pos (C.zCheck_nonempty i)

end QEC
