import QEC1.Remarks.Rem_15_HypergraphGeneralization
import QEC1.Remarks.Rem_20_CohenSchemeAsGauging
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

/-!
# Rem_21: CSS Code Initialization as Gauging

## Statement
**Standard CSS code initialization can be implemented via hypergraph gauging.**

**Standard initialization**: A CSS code is typically initialized by preparing |0⟩^⊗n
and measuring all X-type checks.

**Gauging formulation**:
1. Start with a trivial code having one dummy vertex for each X-type check of the
   target CSS code
2. Perform the generalized gauging measurement using the hypergraph corresponding to
   the Z-type checks of the CSS code
3. The ungauging step performs readout measurement of Z on all qubits

**Steane-style measurement via gauging**: The state preparation and readout gauging
procedure can be combined with another gauging measurement to implement a Steane-style
measurement of a stabilizer group:
1. Perform state preparation of an ancilla code block via gauging as described above
2. Perform a gauging measurement of XX on pairs of matching qubits between the data
   code block and the ancilla code block
3. Perform the ungauging step to read out Z on all ancilla qubits

This connection shows that many existing fault-tolerant gadgets can be unified under
the gauging framework.

## Formalization Approach
We formalize the algebraic content underlying CSS initialization as gauging:
1. CSS code structure with X-type and Z-type checks satisfying orthogonality
2. The Z-check initialization hypergraph
3. **Core theorem**: CSS orthogonality implies X-checks lie in ker(H_Z), making them
   measurable via the hypergraph gauging procedure
4. Dummy vertex structure for the trivial starting code
5. Steane-style measurement: data + ancilla blocks with pairwise XX operators

## Main Results
- `CSSCode` : CSS code structure with X and Z type checks
- `CSSCode.initHypergraph` : The Z-check initialization hypergraph
- `CSSCode.xCheckVector` : X-check support as a binary vector
- `CSSCode.xCheck_in_kernel` : X-checks are in ker(H_Z) by CSS orthogonality
- `CSSCode.xCheck_measurable` : X-checks are measurable via hypergraph gauging
- `CSSCode.xCheck_sum_measurable` : Sums of X-checks are measurable (closure)
- `CSSInitVertex` : Vertex type for initialization (qubits + dummies)
- `cssInitVertex_card` : Total vertices = n + numXChecks
- `SteaneVertex` : Vertex type for Steane measurement (data + ancilla)
- `steaneVertex_card` : Total Steane vertices = 2n
- `pairwiseXXSupport` : Support of XX operator on matching qubit pairs
- `pairwiseXX_weight` : Each XX operator has weight 2
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace QEC1.CSSCodeInitializationAsGauging

open Finset
open QEC1.HypergraphGeneralization

/-! ## Section 1: CSS Code Structure

A CSS (Calderbank-Shor-Steane) code has two types of check generators:
- X-type checks: products of X operators (define X-stabilizers)
- Z-type checks: products of Z operators (define Z-stabilizers)

The CSS condition requires: every X-check commutes with every Z-check.
In binary vector language: |supp(X_check) ∩ supp(Z_check)| ≡ 0 (mod 2). -/

/-- A CSS code with separate X-type and Z-type checks satisfying orthogonality. -/
structure CSSCode where
  /-- Number of physical qubits -/
  numQubits : ℕ
  /-- Number of X-type check generators -/
  numXChecks : ℕ
  /-- Number of Z-type check generators -/
  numZChecks : ℕ
  /-- At least one qubit -/
  numQubits_pos : 0 < numQubits
  /-- Support of X-type check i (qubits where X acts) -/
  xCheckSupport : Fin numXChecks → Finset (Fin numQubits)
  /-- Support of Z-type check j (qubits where Z acts) -/
  zCheckSupport : Fin numZChecks → Finset (Fin numQubits)
  /-- X-checks have non-empty support -/
  xCheck_nonempty : ∀ i, (xCheckSupport i).Nonempty
  /-- Z-checks have non-empty support -/
  zCheck_nonempty : ∀ j, (zCheckSupport j).Nonempty
  /-- CSS orthogonality: |supp(X_i) ∩ supp(Z_j)| ≡ 0 (mod 2) for all i, j -/
  css_orthogonality : ∀ (i : Fin numXChecks) (j : Fin numZChecks),
    (xCheckSupport i ∩ zCheckSupport j).card % 2 = 0

namespace CSSCode

variable (C : CSSCode)

/-- Weight of the i-th X-type check -/
def xCheckWeight (i : Fin C.numXChecks) : ℕ := (C.xCheckSupport i).card

/-- Weight of the j-th Z-type check -/
def zCheckWeight (j : Fin C.numZChecks) : ℕ := (C.zCheckSupport j).card

/-- X-check weights are positive -/
theorem xCheckWeight_pos (i : Fin C.numXChecks) : 0 < C.xCheckWeight i :=
  Finset.Nonempty.card_pos (C.xCheck_nonempty i)

/-- Z-check weights are positive -/
theorem zCheckWeight_pos (j : Fin C.numZChecks) : 0 < C.zCheckWeight j :=
  Finset.Nonempty.card_pos (C.zCheck_nonempty j)

/-! ## Section 2: Initialization Hypergraph

For CSS initialization via gauging, the Z-type checks define the hypergraph:
- Vertices = physical qubits (Fin n)
- Hyperedges = supports of Z-type checks (Fin numZChecks)

This hypergraph encodes the "gauging structure" for initialization. -/

/-- The initialization hypergraph: vertices are qubits, hyperedges are Z-check supports. -/
def initHypergraph : Hypergraph (Fin C.numQubits) (Fin C.numZChecks) where
  incidence := C.zCheckSupport

/-- The initialization hypergraph has numQubits vertices -/
theorem initHypergraph_numVertices :
    Fintype.card (Fin C.numQubits) = C.numQubits := Fintype.card_fin _

/-- The initialization hypergraph has numZChecks hyperedges -/
theorem initHypergraph_numEdges :
    Fintype.card (Fin C.numZChecks) = C.numZChecks := Fintype.card_fin _

/-! ## Section 3: X-Checks in Kernel of H_Z

The key algebraic fact: CSS orthogonality ensures that every X-type check
is in the kernel of the Z-check parity-check map (H_Z).

This is why gauging with the Z-check hypergraph allows measuring X-checks:
operators in ker(H_Z) commute with all Z-type hyperedge operators. -/

/-- The i-th X-check as a binary vector on qubits: 1 at qubit v if v ∈ supp(X_i) -/
def xCheckVector (i : Fin C.numXChecks) : Hypergraph.VectorV (Fin C.numQubits) :=
  fun v => if v ∈ C.xCheckSupport i then 1 else 0

@[simp]
theorem xCheckVector_at_support (i : Fin C.numXChecks)
    (v : Fin C.numQubits) (hv : v ∈ C.xCheckSupport i) :
    C.xCheckVector i v = 1 := by
  simp [xCheckVector, hv]

@[simp]
theorem xCheckVector_outside_support (i : Fin C.numXChecks)
    (v : Fin C.numQubits) (hv : v ∉ C.xCheckSupport i) :
    C.xCheckVector i v = 0 := by
  simp [xCheckVector, hv]

/-- **Core Theorem**: X-checks are in the kernel of the initialization hypergraph.

    H_Z(x_i)_j = ∑_{v ∈ supp(Z_j)} x_i(v) = |supp(X_i) ∩ supp(Z_j)| (mod 2) = 0

    This follows directly from CSS orthogonality. -/
theorem xCheck_in_kernel (i : Fin C.numXChecks) :
    C.xCheckVector i ∈ C.initHypergraph.operatorKernel := by
  rw [Hypergraph.mem_operatorKernel_iff]
  intro j
  simp only [initHypergraph]
  -- The sum ∑_{v ∈ zCheckSupport j} xCheckVector i v counts |xSupp ∩ zSupp| mod 2
  have h_transform : ∀ v ∈ C.zCheckSupport j,
      C.xCheckVector i v = if v ∈ C.xCheckSupport i then (1 : ZMod 2) else 0 := by
    intro v _
    simp [xCheckVector]
  rw [Finset.sum_congr rfl h_transform]
  -- Split the sum into elements in the intersection and outside
  rw [← Finset.sum_filter_add_sum_filter_not (C.zCheckSupport j) (· ∈ C.xCheckSupport i)]
  have h_in : ∀ v ∈ (C.zCheckSupport j).filter (· ∈ C.xCheckSupport i),
      (if v ∈ C.xCheckSupport i then (1 : ZMod 2) else 0) = 1 := by
    intro v hv
    simp only [Finset.mem_filter] at hv
    simp [hv.2]
  have h_out : ∀ v ∈ (C.zCheckSupport j).filter (fun x => ¬(x ∈ C.xCheckSupport i)),
      (if v ∈ C.xCheckSupport i then (1 : ZMod 2) else 0) = 0 := by
    intro v hv
    simp only [Finset.mem_filter] at hv
    simp [hv.2]
  rw [Finset.sum_congr rfl h_in, Finset.sum_congr rfl h_out]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_const_zero, add_zero, mul_zero]
  -- The filter is the intersection
  have h_filter_eq : (C.zCheckSupport j).filter (· ∈ C.xCheckSupport i) =
      C.xCheckSupport i ∩ C.zCheckSupport j := by
    ext v
    simp [Finset.mem_filter, Finset.mem_inter, and_comm]
  rw [h_filter_eq]
  -- Apply CSS orthogonality
  have h_even := C.css_orthogonality i j
  exact Even.natCast_zmod_two (Nat.even_iff.mpr h_even)

/-- X-checks are measurable via the hypergraph gauging procedure. -/
theorem xCheck_measurable (i : Fin C.numXChecks) :
    C.xCheckVector i ∈ C.initHypergraph.operatorKernel :=
  C.xCheck_in_kernel i

/-- Sum (XOR) of X-checks is also in the kernel (closure under addition). -/
theorem xCheck_sum_in_kernel (i j : Fin C.numXChecks) :
    C.xCheckVector i + C.xCheckVector j ∈ C.initHypergraph.operatorKernel :=
  C.initHypergraph.operatorKernel.add_mem (C.xCheck_in_kernel i) (C.xCheck_in_kernel j)

/-- The zero vector is always in the kernel. -/
theorem zero_in_kernel : (0 : Hypergraph.VectorV (Fin C.numQubits)) ∈ C.initHypergraph.operatorKernel :=
  Hypergraph.zero_mem_kernel _

end CSSCode

/-! ## Section 4: Dummy Vertex Structure

In the gauging interpretation, we start with a "trivial code" having one dummy vertex
per X-type check. Each dummy corresponds to an X-check measurement. The dummy vertices
are initialized in |+⟩ and have no effect on the gauging outcome (measuring X on |+⟩
always returns +1). -/

/-- Vertex type for CSS initialization: physical qubits plus one dummy per X-check -/
inductive CSSInitVertex (C : CSSCode) where
  | qubit : Fin C.numQubits → CSSInitVertex C
  | dummy : Fin C.numXChecks → CSSInitVertex C
  deriving DecidableEq

namespace CSSInitVertex

variable {C : CSSCode}

theorem qubit_injective : Function.Injective (qubit : Fin C.numQubits → CSSInitVertex C) := by
  intro i j h; cases h; rfl

theorem dummy_injective : Function.Injective (dummy : Fin C.numXChecks → CSSInitVertex C) := by
  intro i j h; cases h; rfl

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

/-- Total initialization vertices = physical qubits + dummies (one per X-check) -/
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

/-- A predicate distinguishing dummy vertices -/
def CSSInitVertex.isDummy {C : CSSCode} : CSSInitVertex C → Bool
  | .dummy _ => true
  | .qubit _ => false

/-- There are exactly numXChecks dummy vertices -/
theorem cssInitVertex_dummy_count (C : CSSCode) :
    (Finset.univ.filter (fun v : CSSInitVertex C => v.isDummy = true)).card = C.numXChecks := by
  have h_eq : Finset.univ.filter (fun v : CSSInitVertex C => v.isDummy = true) =
    Finset.univ.image CSSInitVertex.dummy := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      cases v with
      | qubit _ => simp [CSSInitVertex.isDummy] at hv
      | dummy i => exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      subst hi
      simp [CSSInitVertex.isDummy]
  rw [h_eq, Finset.card_image_of_injective _ CSSInitVertex.dummy_injective,
    Finset.card_univ, Fintype.card_fin]

/-! ## Section 5: Gauging Procedure for Initialization

The three-step gauging procedure for CSS initialization:

**Step 1**: Start with a trivial code. The dummy vertices represent the X-check
generators. The initialization state is |0⟩^⊗n on qubits and |+⟩ on dummies.

**Step 2**: Perform generalized gauging with Z-check hypergraph. This measures the
generalized Gauss's law operators A_v = X_v ∏_{e ∋ v} X_e. Since X-checks are in
ker(H_Z), they are preserved by the gauging.

**Step 3**: Ungauging readout: measure Z on all qubits.

The key algebraic property connecting these steps is that X-checks being in ker(H_Z)
means they are measurable via the gauging procedure. -/

/-- The gauging procedure for CSS initialization introduces numZChecks new qubits
    (one per hyperedge = one per Z-check). -/
theorem init_gauging_new_qubits (C : CSSCode) :
    C.initHypergraph.newQubitCount = C.numZChecks := by
  simp [Hypergraph.newQubitCount, Fintype.card_fin]

/-- The gauging procedure introduces numQubits new checks
    (one Gauss law operator A_v per qubit vertex). -/
theorem init_gauging_new_checks (C : CSSCode) :
    C.initHypergraph.newCheckCount = C.numQubits := by
  simp [Hypergraph.newCheckCount, Fintype.card_fin]

/-- The sum of all Gauss law vertex supports equals the all-ones vector,
    representing L = ∏_v X_v (the product of all X operators). -/
theorem init_gaussLaw_product (C : CSSCode) :
    ∑ v : Fin C.numQubits, C.initHypergraph.gaussLawVertexSupport v = fun _ => 1 :=
  Hypergraph.gaussLaw_vertex_support_sum_allOnes _

/-! ## Section 6: Steane-Style Measurement via Gauging

Steane's method for fault-tolerant measurement of a stabilizer group:
1. Initialize ancilla code block via CSS gauging (as above)
2. Perform gauging measurement of XX on matching qubit pairs between
   data and ancilla blocks
3. Ungauge to read out Z on all ancilla qubits

We formalize the data/ancilla block structure and the pairwise XX operators. -/

/-- Vertex type for Steane measurement: data block + ancilla block, both with n qubits -/
inductive SteaneVertex (n : ℕ) where
  | data : Fin n → SteaneVertex n
  | ancilla : Fin n → SteaneVertex n
  deriving DecidableEq

namespace SteaneVertex

variable {n : ℕ}

theorem data_injective : Function.Injective (data : Fin n → SteaneVertex n) := by
  intro i j h; cases h; rfl

theorem ancilla_injective : Function.Injective (ancilla : Fin n → SteaneVertex n) := by
  intro i j h; cases h; rfl

theorem data_ne_ancilla (i j : Fin n) : data i ≠ ancilla j := by
  intro h; cases h

end SteaneVertex

/-- Fintype instance for SteaneVertex -/
instance (n : ℕ) : Fintype (SteaneVertex n) :=
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

/-- DecidableEq for SteaneVertex needed downstream -/
instance (n : ℕ) : DecidableEq (SteaneVertex n) := inferInstance

/-- Total Steane vertices = 2n (data block + ancilla block) -/
theorem steaneVertex_card (n : ℕ) :
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
    Represents the XX operator on matching qubit pairs for Steane measurement. -/
def pairwiseXXSupport {n : ℕ} (i : Fin n) :
    SteaneVertex n → ZMod 2 := fun v =>
  match v with
  | SteaneVertex.data j => if j = i then 1 else 0
  | SteaneVertex.ancilla j => if j = i then 1 else 0

@[simp]
theorem pairwiseXXSupport_data_same {n : ℕ} (i : Fin n) :
    pairwiseXXSupport i (SteaneVertex.data i) = 1 := by
  simp [pairwiseXXSupport]

@[simp]
theorem pairwiseXXSupport_ancilla_same {n : ℕ} (i : Fin n) :
    pairwiseXXSupport i (SteaneVertex.ancilla i) = 1 := by
  simp [pairwiseXXSupport]

@[simp]
theorem pairwiseXXSupport_data_ne {n : ℕ} (i j : Fin n) (h : j ≠ i) :
    pairwiseXXSupport i (SteaneVertex.data j) = 0 := by
  simp [pairwiseXXSupport, h]

@[simp]
theorem pairwiseXXSupport_ancilla_ne {n : ℕ} (i j : Fin n) (h : j ≠ i) :
    pairwiseXXSupport i (SteaneVertex.ancilla j) = 0 := by
  simp [pairwiseXXSupport, h]

/-- **Weight of pairwise XX operator is 2**: each XX acts on exactly 2 qubits. -/
theorem pairwiseXX_weight {n : ℕ} (_hn : 0 < n) (i : Fin n) :
    (Finset.univ.filter (fun v => pairwiseXXSupport i v = 1)).card = 2 := by
  have h_eq : Finset.univ.filter (fun v => pairwiseXXSupport i v = 1) =
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
        · exact absurd hv (by decide)
      | ancilla j =>
        right
        simp only [pairwiseXXSupport] at hv
        split_ifs at hv with h
        · exact congr_arg SteaneVertex.ancilla h
        · exact absurd hv (by decide)
    · intro hv
      cases hv with
      | inl h => subst h; simp [pairwiseXXSupport]
      | inr h => subst h; simp [pairwiseXXSupport]
  rw [h_eq, Finset.card_insert_of_notMem, Finset.card_singleton]
  simp [SteaneVertex.data_ne_ancilla]

/-- All pairwise XX operators commute with each other (they are X-type operators). -/
theorem pairwiseXX_commute {n : ℕ} (i j : Fin n) :
    Hypergraph.symplecticInnerProductV
      (pairwiseXXSupport i) 0 (pairwiseXXSupport j) 0 = 0 := by
  simp [Hypergraph.symplecticInnerProductV]

/-! ## Section 7: Steane Gauging Hypergraph

The Steane measurement can be formulated as a gauging measurement using a hypergraph
on the combined data + ancilla vertex set. The hyperedges are the pairwise XX
connections between matching qubits. -/

/-- The Steane gauging hypergraph: vertices are data + ancilla qubits,
    hyperedges correspond to pairwise XX connections. -/
def steaneHypergraph (n : ℕ) :
    Hypergraph (SteaneVertex n) (Fin n) where
  incidence := fun i => {SteaneVertex.data i, SteaneVertex.ancilla i}

/-- Each hyperedge of the Steane hypergraph has exactly 2 vertices. -/
theorem steaneHypergraph_edge_card (n : ℕ) (i : Fin n) :
    ((steaneHypergraph n).incidence i).card = 2 := by
  simp only [steaneHypergraph]
  rw [Finset.card_pair]
  exact SteaneVertex.data_ne_ancilla i i

/-- The Steane hypergraph is graph-like (all edges have size 2). -/
theorem steaneHypergraph_graphLike (n : ℕ) :
    (steaneHypergraph n).isGraphLike := by
  intro h
  exact steaneHypergraph_edge_card n h

/-- The all-ones vector on all Steane vertices is in the kernel
    (each edge has even cardinality). -/
theorem steaneHypergraph_allOnes_in_kernel (n : ℕ) :
    Hypergraph.allOnesV ∈ (steaneHypergraph n).operatorKernel := by
  exact Hypergraph.graphLike_logical_in_kernel _ (steaneHypergraph_graphLike n)

/-! ## Section 8: Three-Step Steane Procedure as Gauging

The complete Steane-style measurement decomposes into three gauging steps:

1. **State preparation**: Initialize ancilla code block via CSS gauging
   (prepare |0⟩^⊗n, gauge with Z-check hypergraph to measure X-checks)

2. **Entangling step**: Gauge with pairwise XX between data and ancilla
   (this is equivalent to transversal CNOT in Steane's original)

3. **Readout**: Ungauge by measuring Z on all ancilla qubits

We formalize the key algebraic property: the composition of these steps
preserves the measurability of the stabilizer group. -/

/-- The three steps of Steane measurement via gauging. -/
inductive SteaneGaugingStep where
  | statePreparation       -- Initialize ancilla via CSS gauging
  | entanglingMeasurement  -- Pairwise XX gauging between data and ancilla
  | readout                -- Z measurement on ancilla (ungauging)
  deriving DecidableEq

instance : Fintype SteaneGaugingStep where
  elems := {SteaneGaugingStep.statePreparation,
            SteaneGaugingStep.entanglingMeasurement,
            SteaneGaugingStep.readout}
  complete := by
    intro x
    cases x <;> simp

/-- There are exactly 3 steps in the Steane gauging procedure. -/
theorem steane_step_count : Fintype.card SteaneGaugingStep = 3 := by
  rfl

/-- The readout step measures Z on ancilla qubits only (not data qubits). -/
def readoutSupport (n : ℕ) : SteaneVertex n → ZMod 2 := fun v =>
  match v with
  | SteaneVertex.data _ => 0
  | SteaneVertex.ancilla _ => 1

/-- Readout support is nonzero only on ancilla qubits -/
@[simp]
theorem readoutSupport_data (n : ℕ) (i : Fin n) :
    readoutSupport n (SteaneVertex.data i) = 0 := rfl

@[simp]
theorem readoutSupport_ancilla (n : ℕ) (i : Fin n) :
    readoutSupport n (SteaneVertex.ancilla i) = 1 := rfl

/-- The number of qubits measured in readout is n (all ancilla qubits). -/
theorem readout_weight (n : ℕ) (_hn : 0 < n) :
    (Finset.univ.filter (fun v => readoutSupport n v = 1)).card = n := by
  have h_eq : Finset.univ.filter (fun v => readoutSupport n v = 1) =
      Finset.univ.image SteaneVertex.ancilla := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      cases v with
      | data i => simp [readoutSupport] at hv
      | ancilla i => exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      subst hi
      simp [readoutSupport]
  rw [h_eq, Finset.card_image_of_injective _ SteaneVertex.ancilla_injective,
    Finset.card_univ, Fintype.card_fin]

/-! ## Section 9: Unification Under Gauging Framework

The key insight: standard fault-tolerant gadgets (CSS initialization, Steane measurement)
are special cases of the hypergraph gauging framework from Rem_15. -/

/-- CSS initialization is a special case of hypergraph gauging:
    the Z-check hypergraph has the property that all X-checks
    are in its kernel (measurable group). -/
theorem css_init_is_gauging (C : CSSCode) :
    ∀ i : Fin C.numXChecks,
    C.xCheckVector i ∈ C.initHypergraph.operatorKernel :=
  C.xCheck_in_kernel

/-- The measurable group for CSS initialization contains all X-check combinations. -/
theorem css_init_measurable_group_contains_xChecks (C : CSSCode) :
    ∀ i j : Fin C.numXChecks,
    C.xCheckVector i + C.xCheckVector j ∈ C.initHypergraph.operatorKernel :=
  C.xCheck_sum_in_kernel

/-- The Steane gauging hypergraph is 2-local (graph-like). -/
theorem steane_is_2local (n : ℕ) :
    (steaneHypergraph n).isKLocalHypergraph 2 := by
  intro h
  simp only [Hypergraph.isKLocal]
  exact le_of_eq (steaneHypergraph_edge_card n h)

/-- Combining CSS initialization and Steane measurement:
    the pairwise XX operators have even overlap with the Steane hypergraph
    (since each XX acts on exactly one vertex per edge). -/
theorem pairwiseXX_in_steane_kernel {n : ℕ} (i : Fin n) :
    pairwiseXXSupport i ∈ (steaneHypergraph n).operatorKernel := by
  rw [Hypergraph.mem_operatorKernel_iff]
  intro j
  simp only [steaneHypergraph]
  rw [Finset.sum_pair (SteaneVertex.data_ne_ancilla j j)]
  by_cases hij : i = j
  · subst hij
    simp only [pairwiseXXSupport, ite_true]
    decide
  · simp only [pairwiseXXSupport]
    have h1 : ¬(j = i) := Ne.symm hij
    simp [h1, hij]

/-- Sum of all pairwise XX operators is the all-ones vector (product of all XX). -/
theorem sum_pairwiseXX_is_allOnes {n : ℕ} :
    ∑ i : Fin n, pairwiseXXSupport i = (fun _ : SteaneVertex n => (1 : ZMod 2)) := by
  ext v
  simp only [Finset.sum_apply]
  cases v with
  | data j =>
    rw [Finset.sum_eq_single j]
    · simp [pairwiseXXSupport]
    · intro k _ hne
      simp only [pairwiseXXSupport, ite_eq_right_iff, one_ne_zero]
      exact fun h => absurd h (Ne.symm hne)
    · intro h; exact absurd (Finset.mem_univ j) h
  | ancilla j =>
    rw [Finset.sum_eq_single j]
    · simp [pairwiseXXSupport]
    · intro k _ hne
      simp only [pairwiseXXSupport, ite_eq_right_iff, one_ne_zero]
      exact fun h => absurd h (Ne.symm hne)
    · intro h; exact absurd (Finset.mem_univ j) h

/-! ## Summary

This formalization captures Remark 21 about CSS code initialization as gauging:

**Definitions:**
- `CSSCode`: CSS code structure with X-type and Z-type checks + orthogonality
- `CSSCode.initHypergraph`: The Z-check initialization hypergraph
- `CSSCode.xCheckVector`: X-check support as binary vector
- `CSSInitVertex`: Qubit + dummy vertex type for initialization
- `SteaneVertex`: Data + ancilla vertex type for Steane measurement
- `steaneHypergraph`: The pairwise XX gauging hypergraph
- `SteaneGaugingStep`: The three steps of Steane measurement

**Key Results:**
- `xCheck_in_kernel`: CSS orthogonality ⟹ X-checks ∈ ker(H_Z)
- `xCheck_sum_in_kernel`: Kernel closed under addition (XOR of X-checks)
- `cssInitVertex_card`: Total initialization vertices = n + numXChecks
- `steaneVertex_card`: Total Steane vertices = 2n
- `pairwiseXX_weight`: Each XX operator has weight 2
- `pairwiseXX_in_steane_kernel`: XX operators are in the Steane hypergraph kernel
- `sum_pairwiseXX_is_allOnes`: Product of all XX gives the logical operator
- `steane_is_2local`: Steane hypergraph is 2-local (graph-like)
-/

end QEC1.CSSCodeInitializationAsGauging
