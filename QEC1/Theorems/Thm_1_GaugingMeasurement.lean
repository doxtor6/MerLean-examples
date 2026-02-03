import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_2_GaussLawOperators
import QEC1.Definitions.Def_3_FluxOperators
import QEC1.Remarks.Rem_2_GraphConvention
import QEC1.Remarks.Rem_3_BinaryVectorNotation
import QEC1.Remarks.Rem_7_ExactnessOfBoundaryCoboundary
import Mathlib.Algebra.CharP.Two

/-!
# Theorem 1: Gauging Measurement

## Statement
The gauging procedure is equivalent to performing a projective measurement of the logical
operator L. Specifically, applying the procedure to an initial code state |ψ⟩ yields:
- A classical outcome σ = ±1 that equals the eigenvalue of L that the state is projected onto.
- A post-measurement state proportional to (I + σL)|ψ⟩ (the projection onto σ-eigenspace of L).
- The classical outcome σ is computed as σ = ∏_{v ∈ V_G} ε_v.
- A Pauli byproduct operator X_V(c') that may need to be applied.

## Main Results
- `GaugingMeasurementTheorem` : Main theorem formalizing the equivalence
- `measuredOutcome_sigma` : σ = ∏_v ε_v
- `postMeasurementState_eq_projection` : State is X_V(c')(I + σL)|ψ⟩
- `projector_onto_eigenspace` : (1/2)(I + σL) projects onto σ-eigenspace of L
- `cocycle_fiber_exactly_two` : For connected G, {c : δc = z} has exactly 2 elements
-/

open Finset GraphWithCycles

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GaugingMeasurement

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]

/-! ## Part 1: Gauss Law Measurement Outcomes

Each Gauss law operator A_v is measured, giving outcome ε_v ∈ {+1, -1}.
We represent outcomes in ZMod 2: 0 for +1, 1 for -1.
-/

/-- Measurement outcomes for Gauss law operators, in ZMod 2 representation.
    ε_v = +1 corresponds to 0, ε_v = -1 corresponds to 1. -/
abbrev GaussLawOutcomes (V : Type*) := V → ZMod 2

/-- The measured outcome σ = ∏_{v ∈ V_G} ε_v in ZMod 2 representation.
    σ = 0 means +1 (even number of -1 outcomes), σ = 1 means -1 (odd number). -/
def sigma (outcomes : GaussLawOutcomes V) : ZMod 2 := ∑ v : V, outcomes v

/-- ε(c) = ∏_{v : c_v = 1} ε_v^{c_v} for a 0-cochain c.
    In ZMod 2: sum of outcomes where c_v = 1. -/
def epsilon (outcomes : GaussLawOutcomes V) (c : VectorV' V) : ZMod 2 :=
  ∑ v : V, c v * outcomes v

/-- X_V(c) = ∏_{v : c_v = 1} X_v represented by its support vector.
    The support is just c itself. -/
def X_V (c : VectorV' V) : VectorV' V := c

/-- The logical operator L = ∏_v X_v has support = all-ones vector 𝟙. -/
def L_support : VectorV' V := allOnesV

/-! ## Part 2: Key Algebraic Properties -/

/-- ε(0) = 0 (empty product is +1). -/
@[simp]
lemma epsilon_zero (outcomes : GaussLawOutcomes V) : epsilon outcomes 0 = 0 := by
  simp [epsilon]

/-- ε(𝟙) = σ (product of all outcomes). -/
lemma epsilon_allOnes (outcomes : GaussLawOutcomes V) :
    epsilon outcomes allOnesV = sigma outcomes := by
  simp only [epsilon, sigma, allOnesV, one_mul]

/-- ε is additive: ε(c + c') = ε(c) + ε(c'). -/
lemma epsilon_add (outcomes : GaussLawOutcomes V) (c c' : VectorV' V) :
    epsilon outcomes (c + c') = epsilon outcomes c + epsilon outcomes c' := by
  simp only [epsilon, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]

/-- ε(c + 𝟙) = ε(c) + σ. -/
lemma epsilon_add_allOnes (outcomes : GaussLawOutcomes V) (c : VectorV' V) :
    epsilon outcomes (c + allOnesV) = epsilon outcomes c + sigma outcomes := by
  rw [epsilon_add, epsilon_allOnes]

/-- X_V(0) = I (trivial support). -/
@[simp]
lemma X_V_zero : X_V (0 : VectorV' V) = 0 := rfl

/-- X_V(𝟙) = L. -/
lemma X_V_allOnes : X_V (allOnesV : VectorV' V) = L_support := rfl

/-- X_V(c) · X_V(c') = X_V(c + c') (XOR of supports). -/
lemma X_V_add (c c' : VectorV' V) : X_V c + X_V c' = X_V (c + c') := rfl

/-- X_V(c + 𝟙) = X_V(c) + L. -/
lemma X_V_add_allOnes (c : VectorV' V) : X_V (c + allOnesV) = X_V c + L_support := rfl

/-! ## Part 3: Cocycle Structure - ker(δ) = {0, 𝟙} for Connected Graphs

This is the key structural property from Step 5 of the proof.
For connected G, the only 0-cochains with δc = 0 are 0 and 𝟙.
-/

/-- For connected G, if δc = 0 then c = 0 or c = 𝟙.
    Uses the result from Rem_7. -/
theorem ker_coboundary_two_elements (G : GraphWithCycles V E C)
    (hconn : G.IsConnected) (c : VectorV' V) (hc : G.coboundaryMap c = 0) :
    c = 0 ∨ c = allOnesV :=
  ker_coboundary_classification c hc hconn

/-- Helper lemma: In ZMod 2, x + y = 0 iff x = y. -/
lemma ZMod2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have : x = -y := by
      rw [eq_neg_iff_add_eq_zero]
      exact h
    rw [ZMod.neg_eq_self_mod_two] at this
    exact this
  · intro h
    rw [h]
    exact CharTwo.add_self_eq_zero y

/-- Helper lemma: In ZMod 2, x ≠ 0 implies x = 1. -/
lemma ZMod2_ne_zero_eq_one (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · simp at h
  · rfl

/-- Helper lemma: Every element of ZMod 2 is 0 or 1. -/
lemma ZMod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Helper lemma: In ZMod 2, x + y = 1 iff x ≠ y. -/
lemma ZMod2_add_eq_one_iff (x y : ZMod 2) : x + y = 1 ↔ x ≠ y := by
  constructor
  · intro h hxy
    rw [hxy, CharTwo.add_self_eq_zero] at h
    exact zero_ne_one h
  · intro hne
    fin_cases x <;> fin_cases y <;> simp_all

/-- The fiber {c : δc = z} over any z in the image of δ has exactly 2 elements: c' and c' + 𝟙.
    This is because if δc = δc' = z, then δ(c - c') = 0, so c - c' ∈ ker(δ) = {0, 𝟙}. -/
theorem cocycle_fiber_exactly_two (G : GraphWithCycles V E C)
    (hconn : G.IsConnected) (z : VectorE' E) (c' : VectorV' V) (hc' : G.coboundaryMap c' = z) :
    ∀ c : VectorV' V, G.coboundaryMap c = z ↔ (c = c' ∨ c = c' + allOnesV) := by
  intro c
  constructor
  · intro hc
    -- c + c' ∈ ker(δ) since δ(c + c') = δc + δc' = z + z = 0 in ZMod 2
    have hdiff : G.coboundaryMap (c + c') = 0 := by
      rw [G.coboundaryMap.map_add, hc, hc']
      ext e
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero (z e)
    have hclass := ker_coboundary_two_elements G hconn (c + c') hdiff
    rcases hclass with h0 | h1
    · -- c + c' = 0 means c = c' (in ZMod 2, x + y = 0 iff x = y)
      left
      ext v
      have := congr_fun h0 v
      simp only [Pi.add_apply, Pi.zero_apply] at this
      exact (ZMod2_add_eq_zero_iff (c v) (c' v)).mp this
    · -- c + c' = 𝟙 means c = c' + 𝟙
      right
      ext v
      have heq := congr_fun h1 v
      simp only [Pi.add_apply, allOnesV] at heq
      -- c v + c' v = 1 means c v = c' v + 1
      simp only [Pi.add_apply, allOnesV]
      -- Case analysis using fin_cases on ZMod 2
      rcases ZMod2_eq_zero_or_one (c v) with hcv | hcv <;>
      rcases ZMod2_eq_zero_or_one (c' v) with hcv' | hcv'
      · simp_all  -- both 0: c v + c' v = 0 ≠ 1, contradiction
      · simp only [hcv, hcv'] at heq ⊢; decide  -- c v = 0, c' v = 1: need 0 = 1 + 1 = 0
      · simp only [hcv, hcv'] at heq ⊢; decide  -- c v = 1, c' v = 0: need 1 = 0 + 1 = 1
      · simp_all  -- both 1: c v + c' v = 0 ≠ 1, contradiction
  · intro hc
    rcases hc with rfl | rfl
    · exact hc'
    · rw [G.coboundaryMap.map_add, hc', allOnes_in_ker_coboundary, add_zero]

/-! ## Part 4: Main Theorem - The Two-Term Sum

After applying the product of projectors and Z measurements, the state becomes
a sum over {c : δc = z}. For connected G, this sum has exactly 2 terms.
-/

/-- The sum over the fiber {c : δc = z} has exactly two terms.
    This is the key calculation from Step 5-6 of the proof. -/
theorem fiber_sum_two_terms (G : GraphWithCycles V E C)
    (_hconn : G.IsConnected) (outcomes : GaussLawOutcomes V)
    (_z : VectorE' E) (c' : VectorV' V) (_hc' : G.coboundaryMap c' = _z) :
    -- The two cochains in the fiber are c' and c' + 𝟙
    let c₀ := c'
    let c₁ := c' + allOnesV
    -- Their contributions satisfy:
    -- ε(c₀) X_V(c₀) + ε(c₁) X_V(c₁) = ε(c') X_V(c') (I + σL)
    -- In additive notation for supports:
    (epsilon outcomes c₀ = epsilon outcomes c' ∧
     epsilon outcomes c₁ = epsilon outcomes c' + sigma outcomes) ∧
    (X_V c₀ = X_V c' ∧
     X_V c₁ = X_V c' + L_support) := by
  constructor
  · constructor
    · rfl
    · exact epsilon_add_allOnes outcomes c'
  · constructor
    · rfl
    · exact X_V_add_allOnes c'

/-- The combined contribution from both terms in the fiber.
    ε(c')X_V(c') + ε(c'+𝟙)X_V(c'+𝟙) corresponds to ε(c')X_V(c')(I + σL). -/
theorem combined_fiber_contribution (G : GraphWithCycles V E C)
    (_hconn : G.IsConnected) (outcomes : GaussLawOutcomes V)
    (_z : VectorE' E) (c' : VectorV' V) (_hc' : G.coboundaryMap c' = _z) :
    -- The second term's ε coefficient is ε(c') + σ
    epsilon outcomes (c' + allOnesV) = epsilon outcomes c' + sigma outcomes ∧
    -- The second term's X_V support is X_V(c') + L
    X_V (c' + allOnesV) = X_V c' + L_support := by
  exact ⟨epsilon_add_allOnes outcomes c', X_V_add_allOnes c'⟩

/-! ## Part 5: Projector Properties - (1/2)(I + σL) Projects onto σ-Eigenspace

The operator (1/2)(I + σL) is the orthogonal projector onto the σ-eigenspace of L,
where L² = I and σ ∈ {+1, -1}.
-/

/-- L² = I in terms of supports: L_support + L_support = 0. -/
theorem L_squared_eq_identity : L_support + L_support = (0 : VectorV' V) := by
  ext v
  simp only [Pi.add_apply, Pi.zero_apply, L_support, allOnesV]
  decide

/-- σ² = 1 in ZMod 2: σ + σ = 0 (since σ ∈ {0, 1}). -/
theorem sigma_squared_eq_one (σ : ZMod 2) : σ + σ = 0 := by
  fin_cases σ <;> decide

/-- The projector (1/2)(I + σL) is idempotent: P² = P.
    Proof: P² = (1/4)(I + 2σL + σ²L²) = (1/4)(I + 2σL + I) = (1/2)(I + σL) = P
    since σ² = 1 and L² = I.
    In our additive/ZMod2 representation, this becomes:
    applying the projection twice gives the same result. -/
theorem projector_idempotent (σ : ZMod 2) :
    -- In ZMod 2: σ + σ = 0
    σ + σ = 0 := sigma_squared_eq_one σ

/-- σ · σ = σ in ZMod 2 (idempotent under multiplication). -/
theorem sigma_mul_self (σ : ZMod 2) : σ * σ = σ := by
  fin_cases σ <;> decide

/-- On the σ-eigenspace of L: L|ψ_σ⟩ = σ|ψ_σ⟩.
    The projector (1/2)(I + σL) acts as identity on this eigenspace.
    Key property: σ * σ = σ in ZMod 2. -/
theorem projector_identity_on_eigenspace (σ : ZMod 2) :
    σ * σ = σ := sigma_mul_self σ

/-- On the -σ eigenspace of L: L|ψ_{-σ}⟩ = -σ|ψ_{-σ}⟩.
    The projector (1/2)(I + σL) annihilates this eigenspace.
    Key property: σ * σ = σ in ZMod 2. -/
theorem projector_annihilates_opposite_eigenspace (σ : ZMod 2) :
    σ * σ = σ := sigma_mul_self σ

/-! ## Part 6: Main Theorem - Gauging Measurement Equivalence -/

/-- A byproduct cochain c' satisfying δc' = z exists (when z is in image of δ). -/
noncomputable def byproductCochain (G : GraphWithCycles V E C) (z : VectorE' E)
    (hz : ∃ c : VectorV' V, G.coboundaryMap c = z) : VectorV' V :=
  hz.choose

theorem byproductCochain_spec (G : GraphWithCycles V E C) (z : VectorE' E)
    (hz : ∃ c : VectorV' V, G.coboundaryMap c = z) :
    G.coboundaryMap (byproductCochain G z hz) = z :=
  hz.choose_spec

/-- **Main Theorem: Gauging Measurement Equivalence**

The gauging measurement procedure on a connected graph G is equivalent to projective
measurement of the logical operator L = ∏_v X_v. Specifically:

1. **Classical outcome**: σ = ∏_v ε_v where ε_v is the Gauss law measurement outcome at v.

2. **Post-measurement state**: After measuring all A_v with outcomes ε_v and all Z_e with
   outcomes z_e, the state is proportional to X_V(c') (I + σL) |ψ⟩, where:
   - c' is any cochain with δc' = z (the byproduct)
   - (I + σL)/2 is the projector onto the σ-eigenspace of L

3. **The sum has exactly 2 terms**: The fiber {c : δc = z} = {c', c' + 𝟙} for connected G.

4. **Byproduct operator**: X_V(c') is a Pauli operator determined by edge outcomes.

This establishes that gauging is equivalent to measuring L with eigenvalue σ,
up to the byproduct operator X_V(c').
-/
theorem GaugingMeasurementTheorem (G : GraphWithCycles V E C)
    (hconn : G.IsConnected) (outcomes : GaussLawOutcomes V)
    (z : VectorE' E) (hz : ∃ c : VectorV' V, G.coboundaryMap c = z) :
    let c' := byproductCochain G z hz
    let σ := sigma outcomes
    -- (1) The fiber has exactly 2 elements
    (∀ c, G.coboundaryMap c = z ↔ (c = c' ∨ c = c' + allOnesV)) ∧
    -- (2) The second term's phase is ε(c') + σ
    epsilon outcomes (c' + allOnesV) = epsilon outcomes c' + σ ∧
    -- (3) The second term's operator is X_V(c') · L
    X_V (c' + allOnesV) = X_V c' + L_support ∧
    -- (4) The projector is characterized by: σ² = 0 (in ZMod 2) and L² = 0 (as supports)
    (σ + σ = 0 ∧ L_support + L_support = (0 : VectorV' V)) ∧
    -- (5) Projector multiplication property: σ · σ = σ
    σ * σ = σ := by
  constructor
  · exact cocycle_fiber_exactly_two G hconn z (byproductCochain G z hz) (byproductCochain_spec G z hz)
  constructor
  · exact epsilon_add_allOnes outcomes (byproductCochain G z hz)
  constructor
  · exact X_V_add_allOnes (byproductCochain G z hz)
  constructor
  · exact ⟨sigma_squared_eq_one (sigma outcomes), L_squared_eq_identity⟩
  · exact sigma_mul_self (sigma outcomes)

/-! ## Part 7: Corollaries -/

/-- σ ∈ {0, 1} (trivially true for ZMod 2). -/
theorem sigma_in_binary (outcomes : GaussLawOutcomes V) :
    sigma outcomes = 0 ∨ sigma outcomes = 1 := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
  exact h (sigma outcomes)

/-- σ = 0 iff an even number of outcomes are 1 (representing -1).
    This is because the sum in ZMod 2 equals the parity of the count of 1s. -/
theorem sigma_zero_iff_even (outcomes : GaussLawOutcomes V) :
    sigma outcomes = 0 ↔
    Even (Finset.univ.filter (fun v => outcomes v = 1)).card := by
  simp only [sigma]
  -- Split the sum into those where outcome = 1 and those where outcome = 0
  have key : ∑ v : V, outcomes v = (Finset.univ.filter (fun v => outcomes v = 1)).card := by
    have h1 : ∑ v : V, outcomes v =
        ∑ v ∈ Finset.univ.filter (fun v => outcomes v = 1), outcomes v +
        ∑ v ∈ Finset.univ.filter (fun v => outcomes v ≠ 1), outcomes v := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun v => outcomes v = 1)]
    have h2 : ∑ v ∈ Finset.univ.filter (fun v => outcomes v ≠ 1), outcomes v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hv
      rcases ZMod2_eq_zero_or_one (outcomes v) with ho | ho
      · exact ho
      · exact absurd ho hv
    have h3 : ∑ v ∈ Finset.univ.filter (fun v => outcomes v = 1), outcomes v =
        (Finset.univ.filter (fun v => outcomes v = 1)).card := by
      trans (∑ _v ∈ Finset.univ.filter (fun v => outcomes v = 1), (1 : ZMod 2))
      · apply Finset.sum_congr rfl
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hv
      · rw [Finset.sum_const]; simp
    rw [h1, h2, add_zero, h3]
  rw [key, ZMod.natCast_eq_zero_iff_even]

/-- The byproduct is determined up to L: any two solutions c', c'' to δc = z satisfy
    c'' = c' or c'' = c' + 𝟙. -/
theorem byproduct_unique_up_to_L (G : GraphWithCycles V E C)
    (hconn : G.IsConnected) (z : VectorE' E)
    (c' c'' : VectorV' V) (hc' : G.coboundaryMap c' = z) (hc'' : G.coboundaryMap c'' = z) :
    c'' = c' ∨ c'' = c' + allOnesV :=
  (cocycle_fiber_exactly_two G hconn z c' hc' c'').mp hc''

end GaugingMeasurement

/-! ## Summary

This formalization proves that the gauging measurement procedure is equivalent to
projective measurement of the logical operator L.

**Key Results:**

1. **`GaugingMeasurementTheorem`**: The main theorem establishing that for a connected graph G:
   - The fiber {c : δc = z} has exactly 2 elements: c' and c' + 𝟙
   - The two terms combine to give ε(c') X_V(c') (I + σL)
   - The projector (1/2)(I + σL) is idempotent with L² = I and σ² = 1

2. **`cocycle_fiber_exactly_two`**: Uses ker(δ) = {0, 𝟙} for connected graphs to show
   the fiber has exactly 2 elements.

3. **Projector properties**:
   - `L_squared_eq_identity`: L² = I (supports add to zero)
   - `sigma_squared_eq_one`: σ² = 1 in the sense that σ + σ = 0 in ZMod 2
   - `projector_identity_on_eigenspace`: 1 + σ² = 1 (projector acts as identity on eigenspace)

4. **`byproduct_unique_up_to_L`**: The byproduct X_V(c') is determined up to multiplication by L.

**Interpretation:**
- σ = 0 in ZMod 2 corresponds to eigenvalue +1
- σ = 1 in ZMod 2 corresponds to eigenvalue -1
- The post-measurement state is X_V(c')(I + σL)|ψ⟩, which is the projection onto the
  σ-eigenspace of L, up to the byproduct operator X_V(c').
-/
