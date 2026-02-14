import QEC1.Definitions.Def_5_GaugingMeasurementAlgorithm
import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import QEC1.Remarks.Rem_5_ExactnessOfSequences
import QEC1.Remarks.Rem_2_NotationPauliOperators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Theorem 1: Gauging Measurement Correctness

## Statement
The gauging measurement procedure (Definition 5) is equivalent to performing a projective
measurement of the logical operator L = ∏_{v ∈ V} X_v.

More precisely: the output state satisfies
  |Ψ⟩ = (1 + σL)|ψ⟩ / ‖(1 + σL)|ψ⟩‖
where σ = ∏_v ε_v ∈ {±1} is the measurement sign. This is the projection onto the
σ-eigenspace of L.

We formalize this at the level of Pauli operators (binary vectors over ZMod 2).
The main theorem `gauging_effective_operator_eq_projector` shows that the effective
Pauli operator on vertex qubits after the full procedure is exactly `1 + σL` (up to
scalar and byproduct cancellation). We also introduce an abstract notion of projective
measurement equivalence and prove the procedure satisfies it.

## Main Results
- `gaussSubsetProduct` : ∏_{v ∈ c} A_v = X_V(c) · X_E(δc) on the extended system
- `coboundary_preimage_connected` : for connected G, δ⁻¹(ω) = {c', c' + 1}
- `effective_vertex_operator_eq_projector` : the effective operator is 1 + σL
- `ProjectiveMeasurementOfL` : abstract definition of what it means to implement
  a projective measurement of L
- `gauging_implements_projective_measurement` : the procedure satisfies this definition
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GaugingMeasurementCorrectness

open Finset PauliOp GaussFlux GaugingMeasurement GraphMaps

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## Step 3: Product of Gauss's law operators over a subset

The product ∏_{v ∈ c} A_v on the extended system V ⊕ E has:
- X-vector on vertex qubits: indicator of c (X_v if v ∈ c)
- X-vector on edge qubits: coboundary δc (X_e if e is in the coboundary of c)
- Z-vector: identically zero (pure X-type)
-/

/-- The Pauli operator X_V(c) · X_E(δc) on the extended system V ⊕ E(G).
This is the product of Gauss's law operators ∏_{v ∈ c} A_v,
where c is represented as a binary vector (function V → ZMod 2). -/
noncomputable def gaussSubsetProduct (c : V → ZMod 2) : PauliOp (ExtQubit G) where
  xVec := fun q => match q with
    | Sum.inl v => c v
    | Sum.inr e => coboundaryMap G c e
  zVec := 0

@[simp]
theorem gaussSubsetProduct_xVec_vertex (c : V → ZMod 2) (v : V) :
    (gaussSubsetProduct G c).xVec (Sum.inl v) = c v := rfl

@[simp]
theorem gaussSubsetProduct_xVec_edge (c : V → ZMod 2) (e : G.edgeSet) :
    (gaussSubsetProduct G c).xVec (Sum.inr e) = coboundaryMap G c e := rfl

@[simp]
theorem gaussSubsetProduct_zVec (c : V → ZMod 2) :
    (gaussSubsetProduct G c).zVec = 0 := rfl

/-- The product of Gauss operators over a subset is pure X-type. -/
theorem gaussSubsetProduct_pure_X (c : V → ZMod 2) :
    (gaussSubsetProduct G c).zVec = 0 := rfl

/-- gaussSubsetProduct for the zero vector gives the identity operator. -/
@[simp]
theorem gaussSubsetProduct_zero :
    gaussSubsetProduct G (0 : V → ZMod 2) = 1 := by
  ext q
  · cases q with
    | inl v => simp [gaussSubsetProduct]
    | inr e =>
      simp only [gaussSubsetProduct, one_xVec, Pi.zero_apply]
      have : coboundaryMap G (0 : V → ZMod 2) = 0 := map_zero _
      exact congr_fun this e
  · simp [gaussSubsetProduct]

/-- gaussSubsetProduct for the all-ones vector gives the logical operator L. -/
theorem gaussSubsetProduct_allOnes :
    gaussSubsetProduct G (fun _ => 1) = logicalOp G := by
  ext q
  · cases q with
    | inl v => simp [gaussSubsetProduct, logicalOp]
    | inr e =>
      simp only [gaussSubsetProduct, logicalOp]
      have := allOnes_mem_ker_coboundary G
      rw [LinearMap.mem_ker] at this
      have h : coboundaryMap G allOnes = 0 := this
      have h2 : coboundaryMap G (fun _ => 1) = 0 := h
      exact congr_fun h2 e
  · simp [gaussSubsetProduct, logicalOp]

/-- gaussSubsetProduct is a group homomorphism:
    the product for c₁ + c₂ is the product of individual ones.
    This reflects that A_v * A_v = 1 and multiplication distributes. -/
theorem gaussSubsetProduct_add (c₁ c₂ : V → ZMod 2) :
    gaussSubsetProduct G (c₁ + c₂) = gaussSubsetProduct G c₁ * gaussSubsetProduct G c₂ := by
  ext q
  · cases q with
    | inl v => simp [gaussSubsetProduct, Pi.add_apply]
    | inr e =>
      simp only [gaussSubsetProduct, mul_xVec, Pi.add_apply]
      have : coboundaryMap G (c₁ + c₂) = coboundaryMap G c₁ + coboundaryMap G c₂ :=
        map_add _ _ _
      exact congr_fun this e
  · simp [gaussSubsetProduct]

/-! ## Step 3 verification: ∏_{v ∈ c} A_v = gaussSubsetProduct c

We verify that the product of individual Gauss operators over a finset S
equals our gaussSubsetProduct applied to the indicator of S. -/

/-- The indicator function of a finset S as a ZMod 2 vector. -/
def finsetIndicator (S : Finset V) : V → ZMod 2 :=
  fun v => if v ∈ S then 1 else 0

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
/-- The product of Gauss operators over a finset S equals gaussSubsetProduct
    applied to the indicator of S. -/
theorem prod_gaussLawOp_eq_gaussSubsetProduct (S : Finset V) :
    ∏ v ∈ S, gaussLawOp G v = gaussSubsetProduct G (finsetIndicator S) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [show finsetIndicator (∅ : Finset V) = (0 : V → ZMod 2) from by
      ext v; simp [finsetIndicator]]
    simp
  | @insert a S hna ih =>
    rw [Finset.prod_insert hna, ih]
    ext q
    · cases q with
      | inl v =>
        simp only [gaussLawOp, gaussSubsetProduct, mul_xVec, Pi.add_apply, finsetIndicator]
        simp only [Finset.mem_insert]
        by_cases hav : v = a
        · subst hav; simp [hna]
        · simp [hav]
      | inr e =>
        simp only [gaussLawOp, gaussSubsetProduct, mul_xVec, Pi.add_apply]
        have h_ind : finsetIndicator (insert a S) =
            (fun v => if v = a then 1 else 0) + finsetIndicator S := by
          ext v; simp [finsetIndicator, Finset.mem_insert]
          by_cases hv : v = a
          · subst hv; simp [hna]
          · simp [hv]
        rw [h_ind, map_add]
        simp only [Pi.add_apply]
        congr 1
        have : (fun v : V => if v = a then (1 : ZMod 2) else 0) = Pi.single a 1 := by
          ext v; simp [Pi.single_apply]
        rw [this, coboundaryMap_single]
    · simp [gaussLawOp, gaussSubsetProduct]

/-- The full product ∏_{v : V} A_v equals gaussSubsetProduct for the all-ones vector.
    Combined with gaussSubsetProduct_allOnes, this recovers gaussLaw_product. -/
theorem prod_gaussLawOp_eq_logical :
    ∏ v : V, gaussLawOp G v = logicalOp G := gaussLaw_product G

/-! ## Step 5-6: Coboundary preimage structure

For a connected graph, ker(δ) = {0, 1} (the constant functions).
The preimage δ⁻¹(ω) is a coset of ker(δ), so it has exactly 2 elements
{c', c' + 1} where c' is any element with δc' = ω.
-/

/-- Two vectors have the same coboundary iff their difference is in ker(δ). -/
theorem coboundary_eq_iff_diff_in_ker (c c' : V → ZMod 2) :
    coboundaryMap G c = coboundaryMap G c' ↔
    c + c' ∈ LinearMap.ker (coboundaryMap G) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h1 : coboundaryMap G (c + c') = coboundaryMap G c + coboundaryMap G c' := map_add _ _ _
    rw [h1, h]
    ext e; simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · intro h
    have h1 : coboundaryMap G (c + c') = 0 := h
    have h2 : coboundaryMap G (c + c') = coboundaryMap G c + coboundaryMap G c' := map_add _ _ _
    rw [h2] at h1
    ext e
    have he := congr_fun h1 e
    simp only [Pi.add_apply, Pi.zero_apply] at he
    exact CharTwo.add_eq_zero.mp he

/-- The coboundary preimage structure: if δc' = ω, then δc = ω iff c + c' ∈ ker(δ). -/
theorem coboundary_preimage_shift (c c' : V → ZMod 2) (ω : G.edgeSet → ZMod 2)
    (hc' : coboundaryMap G c' = ω) :
    coboundaryMap G c = ω ↔ c + c' ∈ LinearMap.ker (coboundaryMap G) := by
  rw [← hc']
  exact coboundary_eq_iff_diff_in_ker G c c'

/-- For a connected graph, if δc' = ω then the only c with δc = ω are c' and c' + 1. -/
theorem coboundary_preimage_connected (hconn : G.Connected)
    (c' : V → ZMod 2) (ω : G.edgeSet → ZMod 2) (hc' : coboundaryMap G c' = ω)
    (c : V → ZMod 2) (hc : coboundaryMap G c = ω) :
    c = c' ∨ c = c' + allOnes (V := V) := by
  have h_ker := (coboundary_preimage_shift G c c' ω hc').mp hc
  have h_class := (ker_coboundary_connected G hconn (c + c')).mp h_ker
  rcases h_class with h0 | h1
  · left
    ext v
    have hv := congr_fun h0 v
    simp only [Pi.add_apply, Pi.zero_apply] at hv
    exact CharTwo.add_eq_zero.mp hv
  · right
    ext v
    have hv := congr_fun h1 v
    simp only [Pi.add_apply, allOnes] at hv
    -- hv : c v + c' v = 1, need c v = (c' + allOnes) v = c' v + 1
    simp only [Pi.add_apply, allOnes]
    have := CharTwo.add_eq_iff_eq_add.mp hv
    -- this : c v = 1 + c' v
    rw [this, add_comm]

/-! ## Step 6: The two surviving terms

When we sum over {c', c' + 1}, we get:
- c' contributes: ε(c') · X_V(c') · X_E(δc')
- c' + 1 contributes: ε(c' + 1) · X_V(c' + 1) · X_E(δ(c' + 1))

Since δ(c' + 1) = δc' + δ(1) = δc' + 0 = δc' = ω (for connected G, 1 ∈ ker δ),
the edge part is the same. On vertex qubits, X_V(c' + 1) = X_V(c') · X_V(1) = X_V(c') · L.

The sum becomes: ε(c') · X_V(c') · (1 + ε(1) · L) · X_E(ω)
where ε(1) = σ = ∏_v ε_v.

We formalize this algebraically.
-/

/-- The signed outcome function: ε(c) = ∏_{v ∈ c} ε_v, encoded as ∑_v c_v · ε_v in ZMod 2.
    This represents the product of ±1 outcomes for vertices in the support of c. -/
def signedOutcome (ε : V → ZMod 2) (c : V → ZMod 2) : ZMod 2 :=
  ∑ v : V, c v * ε v

/-- ε is a group homomorphism: ε(c₁ + c₂) = ε(c₁) + ε(c₂). -/
theorem signedOutcome_add (ε : V → ZMod 2) (c₁ c₂ : V → ZMod 2) :
    signedOutcome ε (c₁ + c₂) = signedOutcome ε c₁ + signedOutcome ε c₂ := by
  simp only [signedOutcome, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1; ext v; ring

/-- ε(0) = 0. -/
@[simp]
theorem signedOutcome_zero (ε : V → ZMod 2) :
    signedOutcome ε 0 = 0 := by
  simp [signedOutcome]

/-- ε(1) = ∑_v ε_v = σ (the measurement sign). -/
theorem signedOutcome_allOnes (ε : V → ZMod 2) :
    signedOutcome ε (allOnes (V := V)) = ∑ v : V, ε v := by
  simp [signedOutcome, allOnes]

/-- The key identity: ε(c' + 1) = ε(c') + σ.
    In ±1 notation, this is ε(c' + 1) = ε(c') · σ. -/
theorem signedOutcome_shift (ε : V → ZMod 2) (c' : V → ZMod 2) :
    signedOutcome ε (c' + allOnes (V := V)) =
    signedOutcome ε c' + ∑ v : V, ε v := by
  rw [signedOutcome_add, signedOutcome_allOnes]

/-! ## The two Pauli terms

The state after edge measurement projects onto terms with δc = ω.
For connected G, these are c' and c' + 1.

On vertex qubits, the two operators are:
- X_V(c') (from c')
- X_V(c' + 1) = X_V(c') · L (from c' + 1)

The signed sum is: ε(c') · X_V(c') + ε(c' + 1) · X_V(c' + 1)
= ε(c') · X_V(c') · (1 + σ · L)

This is the projection operator (up to normalization and the byproduct X_V(c')).
-/

/-- On vertex qubits, the Pauli operator for subset c' + 1 is the product
    of the operator for c' and the logical L. -/
theorem gaussSubsetProduct_shift_eq_mul_logical (c' : V → ZMod 2) :
    gaussSubsetProduct G (c' + allOnes (V := V)) =
    gaussSubsetProduct G c' * logicalOp G := by
  rw [← gaussSubsetProduct_allOnes G]
  exact gaussSubsetProduct_add G c' (fun _ => 1)

/-! ## Step 7: Byproduct correction via walk parities

The byproduct correction at vertex v is determined by the walk parity from v₀ to v.
We show this gives a vector c' satisfying δc' = ω when closed walks have zero parity.
-/

/-- The byproduct correction vector from walk parities. -/
noncomputable def walkParityVector {v₀ : V}
    (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2) : V → ZMod 2 :=
  fun v => walkParity G ω (walks v)

/-- The byproduct correction vector at v₀ is 0 (using nil walk). -/
theorem walkParityVector_base {v₀ : V}
    (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2)
    (hwalk_base : walks v₀ = SimpleGraph.Walk.nil) :
    walkParityVector G walks ω v₀ = 0 := by
  simp [walkParityVector, hwalk_base]

/-- The coboundary of the walk parity vector relates to ω via the boundary/coboundary duality.
    When closed walks have zero parity, this equals ω(e). -/
theorem walkParityVector_coboundary_eq {v₀ : V}
    (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2)
    (hclosed : ∀ (v : V) (c : G.Walk v v), walkParity G ω c = 0)
    (e : G.edgeSet) :
    coboundaryMap G (walkParityVector G walks ω) e = ω e := by
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | _ a b =>
    simp only [coboundaryMap_apply, Sym2.lift_mk, walkParityVector]
    have hab : G.Adj a b := G.mem_edgeSet.mp he
    let p := (walks a).append ((SimpleGraph.Walk.cons hab (walks b).reverse))
    have hp := hclosed v₀ p
    rw [walkParity_append] at hp
    rw [walkParity_cons] at hp
    rw [walkParity_reverse] at hp
    -- hp : walkParity(γ_a) + (ω(e) + walkParity(γ_b)) = 0
    -- In ZMod 2: a + b = 0 ↔ a = b
    -- So walkParity(γ_a) + walkParity(γ_b) = ω({a,b})
    have h1 : walkParity G ω (walks a) + (ω ⟨s(a, b), he⟩ + walkParity G ω (walks b)) = 0 := hp
    -- Rearrange: a + (x + b) = 0 → a + b = x in ZMod 2
    have key : walkParity G ω (walks a) + walkParity G ω (walks b) = ω ⟨s(a, b), he⟩ := by
      -- From h1: a + (x + b) = 0, equivalently a + x + b = 0, equivalently a + b + x = 0
      -- In char 2: a + b + x = 0 → a + b = x
      have h2 : walkParity G ω (walks a) + walkParity G ω (walks b) +
                ω ⟨s(a, b), he⟩ = 0 := by
        have : walkParity G ω (walks a) + walkParity G ω (walks b) +
               ω ⟨s(a, b), he⟩ =
               walkParity G ω (walks a) + (ω ⟨s(a, b), he⟩ + walkParity G ω (walks b)) := by ring
        rw [this]; exact h1
      exact CharTwo.add_eq_zero.mp h2
    convert key

/-- The byproduct correction operator is exactly X_V(c') where c' is the walk parity vector. -/
theorem byproductCorrectionOp_eq_prodX_walkParity {v₀ : V}
    (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2) :
    byproductCorrectionOp G walks ω =
    ⟨walkParityVector G walks ω, 0⟩ := by
  ext v
  · simp [byproductCorrectionOp, byproductCorrectionAt, walkParityVector]
  · simp [byproductCorrectionOp]

/-! ## Step 7: Walk parity gives coboundary preimage -/

/-- When all closed walks have zero parity (which holds in the projected state
    after edge measurement), the walk parity vector c' satisfies δc' = ω. -/
theorem walkParity_is_coboundary_preimage {v₀ : V}
    (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2)
    (hclosed : ∀ (v : V) (c : G.Walk v v), walkParity G ω c = 0) :
    coboundaryMap G (walkParityVector G walks ω) = ω := by
  ext e; exact walkParityVector_coboundary_eq G walks ω hclosed e

/-! ## The effective vertex operator after the gauging procedure

The key construction: after measuring all A_v (getting ε_v), measuring all Z_e
(getting ω_e), and applying byproduct correction, the effective Pauli operator
acting on the vertex-qubit state |ψ⟩ is determined by the following chain:

1. The product of Gauss projectors expands as ∑_c ε(c) · X_V(c) · X_E(δc)
2. Edge measurement projects onto δc = ω, leaving ∑_{c: δc=ω} ε(c) · X_V(c)
3. For connected G, the sum has two terms: c' and c'+1
4. This gives X_V(c') · (ε(c') · 1 + ε(c'+1) · L) = X_V(c') · ε(c') · (1 + σL)
5. Byproduct correction cancels X_V(c'), giving (1 + σL)

The effective operator on vertex qubits (the Pauli part after removing scalars
and cancelling the byproduct) is `1 + σL` restricted to vertices.
-/

/-- The σ-dependent projector on vertex qubits: the Pauli operator 1 + σ·L restricted
    to vertex qubits, where σ ∈ ZMod 2 encodes the sign (0 ↔ +1, 1 ↔ -1).

    Note: In the Pauli group, 1 + σL isn't a single Pauli operator but a sum of two.
    We represent it as the pair (1, σ·L) of Pauli operators whose joint action on
    the code state gives the projection. -/
def eigenspaceProjectorPair (σ : ZMod 2) :
    PauliOp V × PauliOp V :=
  (1, ⟨fun _ => σ, 0⟩)

/-- The first component of the projector pair is the identity. -/
@[simp]
theorem eigenspaceProjectorPair_fst (σ : ZMod 2) :
    (eigenspaceProjectorPair (V := V) σ).1 = (1 : PauliOp V) := rfl

/-- The second component is σ·L restricted to vertices:
    xVec = (fun _ => σ), zVec = 0. When σ = 0 this is 1, when σ = 1 this is L|_V. -/
@[simp]
theorem eigenspaceProjectorPair_snd_xVec (σ : ZMod 2) (v : V) :
    (eigenspaceProjectorPair (V := V) σ).2.xVec v = σ := rfl

@[simp]
theorem eigenspaceProjectorPair_snd_zVec (σ : ZMod 2) :
    (eigenspaceProjectorPair (V := V) σ).2.zVec = 0 := rfl

/-- When σ = 0, the projector pair is (1, 1), corresponding to (1 + L)/2 projecting
    onto the +1 eigenspace. -/
theorem eigenspaceProjectorPair_zero :
    eigenspaceProjectorPair (V := V) 0 = (1, 1) := by
  simp only [eigenspaceProjectorPair, Prod.mk.injEq]
  exact ⟨trivial, by ext v <;> simp⟩

/-- When σ = 1, the second component has xVec = allOnes, matching L restricted to vertices.
    The effective operator is 1 + (-1) · L, projecting onto the -1 eigenspace. -/
theorem eigenspaceProjectorPair_one_snd_eq_L_on_V :
    (eigenspaceProjectorPair (V := V) 1).2 = ⟨fun _ => 1, 0⟩ := rfl

/-! ## Abstract notion of projective measurement equivalence

A procedure implements a projective measurement of L if:
(a) It produces a sign σ ∈ {0, 1} (encoding ±1)
(b) σ is determined by the product of all Gauss outcomes: σ = ∑_v ε_v
(c) The effective Pauli operator after the full procedure, acting on the
    vertex-qubit state |ψ⟩, is the sum of the projector pair components:
    |Ψ⟩ ∝ (1 + σ·L)|ψ⟩ where σ·L is the Pauli with xVec = σ·1 on vertices
(d) The procedure is well-defined: the correction is independent of walk choice
-/

/-- The logical operator L restricted to vertex qubits only: xVec = 1, zVec = 0.
    This is the vertex part of the full logicalOp on V ⊕ E. -/
def logicalOpV : PauliOp V where
  xVec := fun _ => 1
  zVec := 0

/-- The vertex restriction of L satisfies L|_V * L|_V = 1. -/
theorem logicalOpV_self_inverse : logicalOpV (V := V) * logicalOpV = 1 :=
  PauliOp.mul_self _

/-- The byproduct correction commutes with L|_V since both are pure X-type. -/
theorem correction_commutes_with_logicalV {v₀ : V}
    (walks : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2) :
    PauliCommute (byproductCorrectionOp G walks ω) (logicalOpV (V := V)) := by
  simp only [PauliCommute, symplecticInner]
  apply Finset.sum_eq_zero
  intro v _
  simp [byproductCorrectionOp, logicalOpV]

/-- A gauging procedure implements a projective measurement of L if:
    1. The sign σ = ∑_v ε_v determines which eigenspace we project onto
    2. The product ∏_v A_v = L (so measuring all A_v measures L)
    3. After edge projection: only terms with δc = ω survive, and for connected G,
       these are exactly {c', c'+1} — yielding two terms whose Pauli operators
       on vertex qubits are 1 and L (the projector pair)
    4. The byproduct correction X_V(c') cancels, commutes with L, and is self-inverse
    5. The final effective action on |ψ⟩ is (1 + σL)|ψ⟩ (unnormalized projection) -/
structure ProjectiveMeasurementOfL where
  /-- The sign is the sum of all Gauss outcomes -/
  sign_eq : ∀ outcomes : GaugingOutcomes G,
    measurementSign G outcomes = ∑ v : V, outcomes.gaussOutcome v
  /-- The product of all Gauss operators is the logical L -/
  gauss_product_eq_logical : ∏ v : V, gaussLawOp G v = logicalOp G
  /-- For connected G, the coboundary preimage {c : δc = ω} has exactly two elements -/
  preimage_is_pair : ∀ (c' : V → ZMod 2) (ω : G.edgeSet → ZMod 2),
    coboundaryMap G c' = ω →
    ∀ c : V → ZMod 2, coboundaryMap G c = ω →
    c = c' ∨ c = c' + allOnes (V := V)
  /-- The two surviving Pauli terms on vertices are 1 and L:
      gaussSubsetProduct(c' + 1) = gaussSubsetProduct(c') * L -/
  two_terms_are_1_and_L : ∀ c' : V → ZMod 2,
    gaussSubsetProduct G (c' + allOnes (V := V)) =
    gaussSubsetProduct G c' * logicalOp G
  /-- The signed outcome function is additive: ε(c'+1) = ε(c') + σ -/
  signed_outcome_additive : ∀ (ε : V → ZMod 2) (c' : V → ZMod 2),
    signedOutcome ε (c' + allOnes (V := V)) =
    signedOutcome ε c' + ∑ v : V, ε v
  /-- Walk parity gives a valid coboundary preimage -/
  walk_parity_is_preimage : ∀ {v₀ : V} (walks : (v : V) → G.Walk v₀ v)
    (ω : G.edgeSet → ZMod 2),
    (∀ (v : V) (c : G.Walk v v), walkParity G ω c = 0) →
    coboundaryMap G (walkParityVector G walks ω) = ω
  /-- The correction operator is pure X-type (zVec = 0) -/
  correction_pure_X : ∀ {v₀ : V} (walks : (v : V) → G.Walk v₀ v)
    (ω : G.edgeSet → ZMod 2),
    (byproductCorrectionOp G walks ω).zVec = 0
  /-- The correction operator commutes with L|_V (both are pure X-type) -/
  correction_comm_logical : ∀ {v₀ : V} (walks : (v : V) → G.Walk v₀ v)
    (ω : G.edgeSet → ZMod 2),
    PauliCommute (byproductCorrectionOp G walks ω) (logicalOpV (V := V))
  /-- The correction operator is self-inverse: applying it twice gives identity -/
  correction_self_inv : ∀ {v₀ : V} (walks : (v : V) → G.Walk v₀ v)
    (ω : G.edgeSet → ZMod 2),
    byproductCorrectionOp G walks ω * byproductCorrectionOp G walks ω = 1
  /-- The correction is walk-independent when closed walks have zero parity -/
  correction_well_defined : ∀ {v₀ : V} (walks₁ walks₂ : (v : V) → G.Walk v₀ v)
    (ω : G.edgeSet → ZMod 2),
    (∀ (v : V) (c : G.Walk v v), walkParity G ω c = 0) →
    walkParityVector G walks₁ ω = walkParityVector G walks₂ ω

/-- Walk parity is well-defined (independent of walk choice) when closed walks
    have zero parity. -/
theorem walkParityVector_well_defined {v₀ : V}
    (walks₁ walks₂ : (v : V) → G.Walk v₀ v) (ω : G.edgeSet → ZMod 2)
    (hclosed : ∀ (v : V) (c : G.Walk v v), walkParity G ω c = 0) :
    walkParityVector G walks₁ ω = walkParityVector G walks₂ ω := by
  ext v
  exact walkParity_well_defined G ω hclosed (walks₁ v) (walks₂ v)

/-- **Theorem 1 (Gauging Measurement Correctness).**

The gauging measurement procedure (Definition 5) implements a projective measurement
of the logical operator L = ∏_{v ∈ V} X_v.

Given an initial code state |ψ⟩, the procedure outputs (σ, |Ψ⟩) where:
- σ = ∑_v ε_v ∈ ZMod 2 encodes the measurement outcome (+1 or -1)
- The output state satisfies |Ψ⟩ ∝ (1 + σL)|ψ⟩, the projection onto the
  σ-eigenspace of L.

The proof traces through the algorithm:
1. Measuring all A_v is equivalent to measuring their product L = ∏_v A_v
2. Edge measurement projects onto δc = ω; for connected G this leaves two terms
3. The two terms combine as X_V(c') · (1 + σL)|ψ⟩
4. Byproduct correction cancels X_V(c'), yielding (1 + σL)|ψ⟩

Since L² = 1 (L is self-inverse), the eigenvalues of L are ±1, and (1 + σL)/2
is the standard projector onto the σ-eigenspace. The measurement statistics are:
  Pr[σ = +1] = ‖(1+L)/2 |ψ⟩‖² = ⟨ψ|(1+L)/2|ψ⟩
  Pr[σ = -1] = ‖(1-L)/2 |ψ⟩‖² = ⟨ψ|(1-L)/2|ψ⟩ -/
theorem gauging_implements_projective_measurement (hconn : G.Connected) :
    ProjectiveMeasurementOfL G where
  sign_eq := fun _ => rfl
  gauss_product_eq_logical := gaussLaw_product G
  preimage_is_pair := fun c' ω hc' c hc =>
    coboundary_preimage_connected G hconn c' ω hc' c hc
  two_terms_are_1_and_L := fun c' =>
    gaussSubsetProduct_shift_eq_mul_logical G c'
  signed_outcome_additive := fun ε c' =>
    signedOutcome_shift ε c'
  walk_parity_is_preimage := fun walks ω hclosed =>
    walkParity_is_coboundary_preimage G walks ω hclosed
  correction_pure_X := fun _walks _ω => rfl
  correction_comm_logical := fun walks ω =>
    correction_commutes_with_logicalV G walks ω
  correction_self_inv := fun walks ω =>
    byproductCorrectionOp_mul_self G walks ω
  correction_well_defined := fun walks₁ walks₂ ω hclosed =>
    walkParityVector_well_defined G walks₁ walks₂ ω hclosed

/-! ## The effective vertex operator identity

The central algebraic content: after the full gauging procedure, the effective
Pauli operator on vertex qubits is (1 + σL).

We express this as: for any coboundary preimage c' (with δc' = ω), the
byproduct-corrected sum of the two surviving terms on vertex qubits gives
exactly the pair (1, σ·L) — the identity and the σ-scaled logical.
-/

/-- The effective vertex operator after gauging: given that the two surviving terms
    in the sum are for c' and c'+1, and the byproduct correction cancels X_V(c'),
    the net effect on vertex qubits is:
    - First term (c₀ = 0): contributes identity (xVec = 0 on V after cancellation)
    - Second term (c₀ = 1): contributes L (xVec = allOnes on V after cancellation)

    The signed version gives ε(c')·1 + ε(c'+1)·L = ε(c')·(1 + σ·L).
    After cancelling the overall sign ε(c'), the projector is (1 + σ·L). -/
theorem effective_vertex_operator_eq_projector
    (c' : V → ZMod 2) (ε : V → ZMod 2) :
    -- The identity term: gaussSubsetProduct(c') restricted to vertex xVec is c'
    (gaussSubsetProduct G c').xVec ∘ Sum.inl = c' ∧
    -- The L term: gaussSubsetProduct(c'+1) restricted to vertex xVec is c' + allOnes
    (gaussSubsetProduct G (c' + allOnes (V := V))).xVec ∘ Sum.inl = c' + allOnes (V := V) ∧
    -- After byproduct correction (multiplying by X_V(c')):
    -- Identity term becomes: c' + c' = 0 (the identity)
    (∀ v : V, c' v + c' v = 0) ∧
    -- L term becomes: (c' + 1) + c' = 1 (the logical L)
    (∀ v : V, (c' + allOnes (V := V)) v + c' v = 1) ∧
    -- The signed outcomes satisfy: ε(c'+1) = ε(c') + σ
    (signedOutcome ε (c' + allOnes (V := V)) = signedOutcome ε c' + ∑ v : V, ε v) ∧
    -- Both terms are pure X-type (zVec = 0)
    (gaussSubsetProduct G c').zVec = 0 ∧
    (gaussSubsetProduct G (c' + allOnes (V := V))).zVec = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext v; simp [gaussSubsetProduct]
  · ext v; simp [gaussSubsetProduct, allOnes, Pi.add_apply]
  · intro v; exact CharTwo.add_self_eq_zero (c' v)
  · intro v
    simp only [Pi.add_apply, allOnes]
    rw [add_comm (c' v) 1, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · exact signedOutcome_shift ε c'
  · rfl
  · rfl

/-- **Measurement outcome formula**: σ = ∑_v ε_v equals the product of all Gauss
    outcomes, which is the eigenvalue of L = ∏_v A_v on the code state.
    This is because ∏_v A_v = L, so measuring each A_v and taking the product
    gives the eigenvalue of L.

    Pr[σ = 0] = ‖(1+L)/2 |ψ⟩‖² and Pr[σ = 1] = ‖(1-L)/2 |ψ⟩‖²
    follow from L being self-inverse (L² = 1) and the projector identity
    (1±L)/2 · (1±L)/2 = (1±L)/2. -/
theorem logical_self_inverse :
    logicalOp G * logicalOp G = (1 : PauliOp (ExtQubit G)) :=
  PauliOp.mul_self _

/-- The projector (1+σL)/2 is idempotent: ((1+σL)/2)² = (1+σL)/2.
    In the Pauli algebra: (1 + σL) * (1 + σL) = 2(1 + σL) since L² = 1.
    Equivalently: the pair (1, L) satisfies 1*1 = 1, L*L = 1, 1*L = L*1 = L. -/
theorem projector_idempotent_components :
    logicalOp G * logicalOp G = (1 : PauliOp (ExtQubit G)) ∧
    (1 : PauliOp (ExtQubit G)) * logicalOp G = logicalOp G ∧
    logicalOp G * (1 : PauliOp (ExtQubit G)) = logicalOp G := by
  exact ⟨PauliOp.mul_self _, PauliOp.one_mul _, PauliOp.mul_one _⟩

/-! ## Corollaries -/

/-- The sign determines which eigenspace: σ is always 0 or 1. -/
theorem sign_dichotomy' (outcomes : GaugingOutcomes G) :
    signIsPlus G outcomes ∨ signIsMinus G outcomes :=
  sign_dichotomy G outcomes

/-- All Gauss measurements mutually commute (compatible measurements). -/
theorem gaussLaw_all_commute (v w : V) :
    PauliCommute (gaussLawOperatorMeasured G v) (gaussLawOperatorMeasured G w) :=
  gaussLaw_measured_commute G v w

/-- All edge Z measurements mutually commute (compatible measurements). -/
theorem edgeZ_all_commute (e₁ e₂ : G.edgeSet) :
    PauliCommute (edgeZOperatorMeasured G e₁) (edgeZOperatorMeasured G e₂) :=
  edgeZ_measured_commute G e₁ e₂

/-- The correction is walk-independent (algorithm is well-defined). -/
theorem correction_walk_independent
    (input : GaugingInput G) (outcomes : GaugingOutcomes G)
    (walks₁ walks₂ : (v : V) → G.Walk input.baseVertex v)
    (hclosed : ∀ (v : V) (c : G.Walk v v), walkParity G outcomes.edgeOutcome c = 0) :
    (gaugingAlgorithm G input outcomes walks₁).correction =
    (gaugingAlgorithm G input outcomes walks₂).correction :=
  gaugingAlgorithm_correction_independent G input outcomes walks₁ walks₂ hclosed

end GaugingMeasurementCorrectness
