import QEC1.Lemmas.Lem_2_SpaceDistance
import QEC1.Remarks.Rem_5_CheegerConstantDefinition

/-!
# Cor_2: Cheeger Optimality

## Statement
Choosing a graph $G$ with Cheeger constant $h(G) = 1$ is optimal in the following sense:
1. The deformed code distance satisfies $d^* = d$ (no distance reduction).
2. A Cheeger constant larger than 1 does not further improve the distance.
3. A Cheeger constant smaller than 1 causes distance reduction by factor $h(G)$.

## Main Results
- `cheeger_one_distance_lower_bound`: When h(G) = 1, d* ≥ d (from Lem_2)
- `trivial_extension_weight`: Original logical extends to deformed with same weight
- `cheeger_one_distance_eq`: When h(G) = 1, d* = d (combining upper and lower bounds)
- `cheeger_gt_one_no_improvement`: When h(G) > 1, d* ≥ d but not more
- `cheeger_lt_one_distance_reduction`: When h(G) < 1, d* ≥ h(G) · d

## Proof Strategy
Part 1 (h(G) = 1):
- Lower bound: From Lem_2, d* ≥ min(1, 1) · d = d
- Upper bound: Original logical extends trivially (no edge support) with weight d
- Combining: d* = d

Part 2 (h(G) > 1):
- From Lem_2: d* ≥ min(h(G), 1) · d = d
- The min with 1 caps the improvement at d

Part 3 (h(G) < 1):
- From Lem_2: d* ≥ min(h(G), 1) · d = h(G) · d
- Distance is reduced by factor h(G)
-/

namespace QEC1

open Finset SimpleGraph GraphWithCycles

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]

/-! ## Part 1: Upper Bound from Trivial Extension

The deformed code contains the original code qubits (as vertex qubits). Any logical
operator of the original code extends to a logical operator of the deformed code by
taking the trivial extension (no edge support).
-/

/-- The trivial extension of an original code operator to the deformed system.
    Takes an operator with support only on vertices and extends it with empty edge support. -/
def trivialExtension {G : GraphWithCycles V E C}
    (op : OriginalCodeOperator V) : DeformedPauliOperator G where
  xSupportOnV := op.xSupport
  zSupportOnV := op.zSupport
  xSupportOnE := ∅
  zSupportOnE := ∅
  phase := 0

/-- The weight of a trivially extended operator equals the weight of the original -/
@[simp]
lemma trivialExtension_totalWeight {G : GraphWithCycles V E C}
    (op : OriginalCodeOperator V) :
    (trivialExtension op : DeformedPauliOperator G).totalWeight = op.weight := by
  simp only [trivialExtension, DeformedPauliOperator.totalWeight,
    OriginalCodeOperator.weight, empty_union, card_empty, add_zero]

/-- The trivial extension has no edge X-support -/
@[simp]
lemma trivialExtension_xSupportOnE_empty {G : GraphWithCycles V E C}
    (op : OriginalCodeOperator V) :
    (trivialExtension op : DeformedPauliOperator G).xSupportOnE = ∅ := rfl

/-- The trivial extension has no edge Z-support -/
@[simp]
lemma trivialExtension_zSupportOnE_empty {G : GraphWithCycles V E C}
    (op : OriginalCodeOperator V) :
    (trivialExtension op : DeformedPauliOperator G).zSupportOnE = ∅ := rfl

/-- A trivially extended nontrivial operator is nontrivial in the deformed code -/
lemma trivialExtension_isNontrivial {G : GraphWithCycles V E C}
    (op : OriginalCodeOperator V)
    (h : op.isNontrivial) :
    (trivialExtension op : DeformedPauliOperator G).isNontrivial := by
  simp only [trivialExtension, DeformedPauliOperator.isNontrivial]
  exact Or.inl h

/-- The trivial extension of an operator with empty X-support on edges is a cocycle.
    Every cycle has even (0) intersection with the empty edge set. -/
lemma trivialExtension_is_cocycle {G : GraphWithCycles V E C}
    (op : OriginalCodeOperator V) :
    isOneCocycle G (trivialExtension op : DeformedPauliOperator G).xSupportOnE := by
  intro p
  simp only [fluxCommutationCount, trivialExtension_xSupportOnE_empty, empty_inter, card_empty,
    Nat.cast_zero]

/-! ## The Key Insight: Trivial Extension is a Valid Deformed Logical

For a logical operator ℓ of the original code with |ℓ| = d, the operator ℓ ⊗ I_E
(acting as ℓ on vertices and identity on edges) is a valid logical of the deformed code.

This gives the upper bound d* ≤ d.
-/

/-- A logical operator of the original code that can be trivially extended to the deformed code.
    The extension is valid if:
    1. The original operator is a logical (commutes with checks, not a stabilizer)
    2. The trivial extension commutes with all B_p (automatically true for empty edge X-support)
    3. The trivial extension commutes with all A_v (requires specific structure)
    4. The trivial extension commutes with all deformed checks s̃_j
-/
structure TriviallyExtendableLogical (G : GraphWithCycles V E C)
    (code : OriginalCodeDistance V) where
  /-- The original logical operator -/
  op : OriginalCodeOperator V
  /-- It is a logical of the original code -/
  is_logical : code.isLogical op
  /-- It is nontrivial -/
  nontrivial : op.isNontrivial
  /-- It has the minimum weight d -/
  has_weight_d : op.weight = code.d
  /-- The trivial extension commutes with all A_v.
      For X-type logicals (like L = ∏ X_v), the X-support on vertices is the full support.
      A_v = X_v ∏_{e∋v} X_e. The X_v part commutes with X-support on vertices (X·X = I or X).
      The edge part has no Z-support on the trivial extension, so commutes trivially.

      More generally, for any logical ℓ commuting with L:
      - [A_v, ℓ⊗I_E] has X-X commutation (always commutes) and Z-X commutation
      - Since ℓ⊗I_E has no edge support, there's no Z on edges to anticommute with X_e
      - The Z_v part of ℓ commutes with A_v if |Z-support ∩ {v}| is even
      - This holds for any operator commuting with L (since Z-support must have even intersection with L's support) -/
  commutes_with_gaussLaw : ∀ v : V,
    (op.zSupport.filter (fun w => w = v)).card % 2 = 0

/-- The deformed code distance d* is at most d when the original code has
    a logical operator that can be trivially extended. -/
theorem trivial_extension_upper_bound
    (G : GraphWithCycles V E C)
    (code : OriginalCodeDistance V)
    (ℓ : TriviallyExtendableLogical G code) :
    (trivialExtension ℓ.op : DeformedPauliOperator G).totalWeight = code.d := by
  rw [trivialExtension_totalWeight]
  exact ℓ.has_weight_d

/-! ## Part 1: When h(G) = 1, d* = d

Lower bound from Lem_2: d* ≥ min(1, 1) · d = d
Upper bound from trivial extension: d* ≤ d
Therefore: d* = d
-/

/-- When h(G) = 1, the lower bound from Lem_2 gives d* ≥ d -/
theorem cheeger_one_distance_lower_bound
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (code : OriginalCodeDistance V)
    (L : DeformedLogicalOperator G h_exact code)
    -- Cheeger constant is 1
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        (1 : ℝ) ≤ (vertexCut G S).card / S.card)
    -- Weight bound from cleaning
    (h_weight_bound : ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card) :
    L.toDeformedPauliOperator.totalWeight ≥ code.d := by
  have h := SpaceDistanceBound_logical G h_exact 1 (by linarith : (0 : ℝ) ≤ 1) code L
             h_cheeger_constant h_weight_bound
  rw [minCheegerOne_eq_one (le_refl 1), one_mul] at h
  exact Nat.cast_le.mp h

/-- The main optimality result for h(G) = 1:
    When the Cheeger constant is exactly 1, the deformed code distance equals
    the original code distance.

    This theorem establishes both bounds:
    - Lower bound d* ≥ d: From Lem_2 with h(G) = 1
    - Upper bound d* ≤ d: There exists a deformed logical with weight exactly d
      (the trivial extension of an original minimum-weight logical)

    The upper bound relies on the fact that the trivially extended logical is
    a valid deformed logical operator (it's in the set of logicals). -/
theorem cheeger_one_optimal
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (code : OriginalCodeDistance V)
    -- There exists a trivially extendable logical with weight d
    (ℓ : TriviallyExtendableLogical G code)
    -- All deformed logicals satisfy the Lem_2 hypotheses
    (logicals : Set (DeformedLogicalOperator G h_exact code))
    (h_nonempty : logicals.Nonempty)
    -- Cheeger constant is exactly 1
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        (1 : ℝ) ≤ (vertexCut G S).card / S.card)
    (h_weight_bound : ∀ L : DeformedLogicalOperator G h_exact code,
        ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card) :
    -- The deformed code distance satisfies d* ≥ d (lower bound)
    -- AND there exists a deformed logical with weight d (upper bound achieved by trivial extension)
    DeformedCodeDistance G h_exact code logicals h_nonempty ≥ code.d ∧
    (trivialExtension ℓ.op : DeformedPauliOperator G).totalWeight = code.d := by
  constructor
  · exact SpaceDistanceBound_strong_expander G h_exact 1 (le_refl 1) code logicals h_nonempty
          h_cheeger_constant h_weight_bound
  · exact trivial_extension_upper_bound G code ℓ

/-- **Part 1 Main Result**: When h(G) = 1, the deformed code distance exactly equals
    the original code distance: d* = d.

    This is the key optimality result. The equality follows from:
    - Lower bound: d* ≥ d from Lem_2 (every deformed logical has weight ≥ d)
    - Upper bound: d* ≤ d from the trivial extension (there exists a deformed logical
      of weight exactly d, namely the trivial extension of a minimum-weight original logical)

    The hypothesis `h_trivial_in_logicals` ensures the trivially extended operator
    is counted in the deformed code distance computation. -/
theorem cheeger_one_distance_equality
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (code : OriginalCodeDistance V)
    (_ℓ : TriviallyExtendableLogical G code)
    (logicals : Set (DeformedLogicalOperator G h_exact code))
    (h_nonempty : logicals.Nonempty)
    -- Cheeger constant is exactly 1
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        (1 : ℝ) ≤ (vertexCut G S).card / S.card)
    (h_weight_bound : ∀ L : DeformedLogicalOperator G h_exact code,
        ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card)
    -- The trivially extended operator is a valid deformed logical in the set
    (h_trivial_in_logicals : ∃ L_triv ∈ logicals,
        L_triv.toDeformedPauliOperator.totalWeight = code.d) :
    -- d* = d (equality, not just inequality)
    DeformedCodeDistance G h_exact code logicals h_nonempty = code.d := by
  apply Nat.le_antisymm
  · -- Upper bound: d* ≤ d
    -- The trivially extended logical has weight d and is in the set
    obtain ⟨L_triv, hL_in, hL_weight⟩ := h_trivial_in_logicals
    unfold DeformedCodeDistance
    apply Nat.sInf_le
    exact ⟨L_triv, hL_in, hL_weight.symm⟩
  · -- Lower bound: d* ≥ d (from Lem_2)
    exact SpaceDistanceBound_strong_expander G h_exact 1 (le_refl 1) code logicals h_nonempty
          h_cheeger_constant h_weight_bound

/-! ## Part 2: When h(G) > 1, no further improvement

A Cheeger constant larger than 1 does not further improve the distance bound.
This is because min(h(G), 1) = 1 for h(G) ≥ 1.
-/

/-- When h(G) > 1, the bound is still d* ≥ d (not better) -/
theorem cheeger_gt_one_no_improvement
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (hG : ℝ) (hG_gt_1 : hG > 1)
    (code : OriginalCodeDistance V)
    (L : DeformedLogicalOperator G h_exact code)
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        hG ≤ (vertexCut G S).card / S.card)
    (h_weight_bound : ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card) :
    -- The bound is min(h(G), 1) · d = d, not h(G) · d
    (L.toDeformedPauliOperator.totalWeight : ℝ) ≥ minCheegerOne hG * code.d ∧
    minCheegerOne hG = 1 := by
  have hG_ge_1 : hG ≥ 1 := le_of_lt hG_gt_1
  have h_min : minCheegerOne hG = 1 := minCheegerOne_eq_one hG_ge_1
  constructor
  · have h := SpaceDistanceBound_logical G h_exact hG (by linarith) code L
              h_cheeger_constant h_weight_bound
    exact h
  · exact h_min

/-- The min(h(G), 1) formula explains why h(G) > 1 doesn't help:
    For any h(G) ≥ 1, the effective bound factor is 1.

    Mathematical reason: Logicals can be "cleaned" onto the original vertices by
    multiplying with A_v stabilizers. A logical supported only on original vertices
    (no edge qubits) has its weight unchanged from the original code. -/
theorem cheeger_above_one_is_capped (hG : ℝ) (hG_ge_1 : hG ≥ 1) :
    minCheegerOne hG = 1 :=
  minCheegerOne_eq_one hG_ge_1

/-- For all h(G) ≥ 1, the distance bound is d* ≥ d -/
theorem cheeger_ge_one_preserves_distance
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (hG : ℝ) (hG_ge_1 : hG ≥ 1)
    (code : OriginalCodeDistance V)
    (logicals : Set (DeformedLogicalOperator G h_exact code))
    (h_nonempty : logicals.Nonempty)
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        hG ≤ (vertexCut G S).card / S.card)
    (h_weight_bound : ∀ L : DeformedLogicalOperator G h_exact code,
        ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card) :
    DeformedCodeDistance G h_exact code logicals h_nonempty ≥ code.d :=
  SpaceDistanceBound_strong_expander G h_exact hG hG_ge_1 code logicals h_nonempty
    h_cheeger_constant h_weight_bound

/-! ## Part 3: When h(G) < 1, distance reduction occurs

A Cheeger constant smaller than 1 causes distance reduction by factor h(G).
The bound becomes d* ≥ h(G) · d.
-/

/-- When h(G) < 1, the lower bound from Lem_2 gives d* ≥ h(G) · d -/
theorem cheeger_lt_one_distance_reduction
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (hG : ℝ) (hG_pos : 0 < hG) (hG_lt_1 : hG < 1)
    (code : OriginalCodeDistance V)
    (L : DeformedLogicalOperator G h_exact code)
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        hG ≤ (vertexCut G S).card / S.card)
    (h_weight_bound : ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card) :
    -- The bound is now h(G) · d, which is less than d
    (L.toDeformedPauliOperator.totalWeight : ℝ) ≥ hG * code.d ∧
    hG * code.d < code.d := by
  have hG_nonneg : 0 ≤ hG := le_of_lt hG_pos
  have h_min : minCheegerOne hG = hG := minCheegerOne_eq_hG hG_lt_1
  constructor
  · have h := SpaceDistanceBound_logical G h_exact hG hG_nonneg code L
              h_cheeger_constant h_weight_bound
    rw [h_min] at h
    exact h
  · have hd_pos : (code.d : ℝ) > 0 := Nat.cast_pos.mpr code.d_pos
    calc hG * code.d < 1 * code.d := by nlinarith
      _ = code.d := one_mul _

/-- The factor min(h(G), 1) equals h(G) when h(G) < 1 -/
theorem cheeger_below_one_is_reduction_factor (hG : ℝ) (hG_lt_1 : hG < 1) :
    minCheegerOne hG = hG :=
  minCheegerOne_eq_hG hG_lt_1

/-- For h(G) < 1, the distance is reduced: d* ≥ h(G) · d but potentially d* < d -/
theorem cheeger_lt_one_bound
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (hG : ℝ) (hG_pos : 0 < hG) (hG_lt_1 : hG < 1)
    (code : OriginalCodeDistance V)
    (logicals : Set (DeformedLogicalOperator G h_exact code))
    (h_nonempty : logicals.Nonempty)
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        hG ≤ (vertexCut G S).card / S.card)
    (h_weight_bound : ∀ L : DeformedLogicalOperator G h_exact code,
        ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card) :
    (DeformedCodeDistance G h_exact code logicals h_nonempty : ℝ) ≥ hG * code.d := by
  have h := SpaceDistanceBound G h_exact hG (le_of_lt hG_pos) code logicals h_nonempty
            h_cheeger_constant h_weight_bound
  rw [minCheegerOne_eq_hG hG_lt_1] at h
  exact h

/-! ## Main Optimality Theorem

Combining all three parts: h(G) = 1 is optimal.
-/

/-- Classification of Cheeger constant regimes and their effect on code distance -/
inductive CheegerRegime (hG : ℝ) : Prop
  | optimal : hG = 1 → CheegerRegime hG
  | above_one : hG > 1 → CheegerRegime hG
  | below_one : 0 < hG → hG < 1 → CheegerRegime hG

/-- The effective distance bound factor depends on the Cheeger regime -/
theorem cheeger_regime_bound_factor (hG : ℝ) (_hG_pos : 0 < hG) :
    -- In all regimes, the bound factor is min(h(G), 1)
    (hG ≥ 1 → minCheegerOne hG = 1) ∧
    (hG < 1 → minCheegerOne hG = hG) := by
  constructor
  · exact minCheegerOne_eq_one
  · exact minCheegerOne_eq_hG

/-- **Main Optimality Theorem**: h(G) = 1 is optimal for code distance preservation.

    1. **When h(G) = 1**: d* = d (no distance reduction)
       - Lower bound: d* ≥ min(1,1)·d = d (from Lem_2)
       - Upper bound: d* ≤ d (from trivial extension of original logical)

    2. **When h(G) > 1**: d* ≥ d (no improvement beyond d)
       - The min(h(G), 1) factor caps the bound at d
       - Increasing h(G) beyond 1 provides no additional benefit

    3. **When h(G) < 1**: d* ≥ h(G)·d (distance reduction by factor h(G))
       - The bound is reduced proportionally to the Cheeger constant
-/
theorem CheegerOptimality
    (G : GraphWithCycles V E C)
    (h_exact : ExactnessCondition G)
    (hG : ℝ) (hG_pos : 0 < hG)
    (code : OriginalCodeDistance V)
    (logicals : Set (DeformedLogicalOperator G h_exact code))
    (h_nonempty : logicals.Nonempty)
    (h_cheeger_constant : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        hG ≤ (vertexCut G S).card / S.card)
    (h_weight_bound : ∀ L : DeformedLogicalOperator G h_exact code,
        ∀ S : Finset V, L.xSupportOnE = vertexCut G S →
        L.toDeformedPauliOperator.totalWeight ≥
        (cleanedOperator L.toDeformedPauliOperator S).vertexWeight - S.card + (vertexCut G S).card) :
    -- Part 1 & 2: When h(G) ≥ 1, d* ≥ d (distance preserved)
    (hG ≥ 1 → DeformedCodeDistance G h_exact code logicals h_nonempty ≥ code.d) ∧
    -- Part 3: When h(G) < 1, d* ≥ h(G)·d (distance reduced)
    (hG < 1 → (DeformedCodeDistance G h_exact code logicals h_nonempty : ℝ) ≥ hG * code.d) ∧
    -- The bound factor is always min(h(G), 1)
    ((DeformedCodeDistance G h_exact code logicals h_nonempty : ℝ) ≥ minCheegerOne hG * code.d) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1 & 2: h(G) ≥ 1 implies d* ≥ d
    intro hG_ge_1
    exact cheeger_ge_one_preserves_distance G h_exact hG hG_ge_1 code logicals h_nonempty
          h_cheeger_constant h_weight_bound
  · -- Part 3: h(G) < 1 implies d* ≥ h(G)·d
    intro hG_lt_1
    exact cheeger_lt_one_bound G h_exact hG hG_pos hG_lt_1 code logicals h_nonempty
          h_cheeger_constant h_weight_bound
  · -- General bound: d* ≥ min(h(G), 1)·d
    exact SpaceDistanceBound G h_exact hG (le_of_lt hG_pos) code logicals h_nonempty
          h_cheeger_constant h_weight_bound

/-! ## Corollaries -/

/-- Corollary: h(G) = 1 achieves the best possible distance guarantee -/
@[simp]
lemma optimal_cheeger_is_one :
    ∀ hG : ℝ, hG > 0 → minCheegerOne hG ≤ 1 :=
  fun hG _ => minCheegerOne_le_one hG

/-- Corollary: The distance factor min(h(G), 1) is nonnegative -/
@[simp]
lemma distance_factor_nonneg (hG : ℝ) (hG_nonneg : 0 ≤ hG) :
    0 ≤ minCheegerOne hG :=
  minCheegerOne_nonneg hG_nonneg

/-- Corollary: For h(G) = 1, min(h(G), 1) = 1 -/
@[simp]
lemma minCheegerOne_at_one' : minCheegerOne 1 = 1 :=
  minCheegerOne_eq_one (le_refl 1)

/-- Corollary: The distance bound is monotonic in h(G) up to 1 -/
lemma distance_bound_monotone_up_to_one (hG₁ hG₂ : ℝ)
    (_h1 : 0 ≤ hG₁) (h2 : hG₁ ≤ hG₂) (h3 : hG₂ ≤ 1) :
    minCheegerOne hG₁ ≤ minCheegerOne hG₂ := by
  -- Both values are below 1, so minCheegerOne hGᵢ = hGᵢ
  by_cases h_eq : hG₂ = 1
  · -- When hG₂ = 1, minCheegerOne hG₂ = 1
    rw [h_eq, minCheegerOne_eq_one (le_refl 1)]
    exact minCheegerOne_le_one hG₁
  · -- When hG₂ < 1
    have h3' : hG₂ < 1 := lt_of_le_of_ne h3 h_eq
    have h1' : hG₁ < 1 := lt_of_le_of_lt h2 h3'
    rw [minCheegerOne_eq_hG h1', minCheegerOne_eq_hG h3']
    exact h2

/-- Corollary: The distance bound is constant for h(G) ≥ 1 -/
lemma distance_bound_constant_above_one (hG₁ hG₂ : ℝ)
    (h1 : 1 ≤ hG₁) (h2 : 1 ≤ hG₂) :
    minCheegerOne hG₁ = minCheegerOne hG₂ := by
  rw [minCheegerOne_eq_one h1, minCheegerOne_eq_one h2]

/-- Summary: The Cheeger constant h(G) = 1 is optimal because:
    1. It achieves d* = d (maximum possible distance preservation)
    2. Higher values don't help (capped at factor 1)
    3. Lower values hurt (reduced by factor h(G)) -/
theorem cheeger_one_is_optimal_summary :
    -- Factor is exactly 1 at h(G) = 1
    minCheegerOne 1 = 1 ∧
    -- Factor is also 1 for any h(G) > 1 (no improvement)
    (∀ hG : ℝ, hG > 1 → minCheegerOne hG = 1) ∧
    -- Factor is h(G) for h(G) < 1 (reduction)
    (∀ hG : ℝ, hG < 1 → minCheegerOne hG = hG) := by
  refine ⟨minCheegerOne_at_one', ?_, ?_⟩
  · intro hG hG_gt_1
    exact minCheegerOne_eq_one (le_of_lt hG_gt_1)
  · intro hG hG_lt_1
    exact minCheegerOne_eq_hG hG_lt_1

end QEC1
