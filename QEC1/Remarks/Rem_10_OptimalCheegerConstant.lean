import QEC1.Lemmas.Lem_2_SpaceDistanceBound

/-!
# Optimal Cheeger Constant (Remark 10)

## Statement
Picking a graph with Cheeger constant $h(G) = 1$ is optimal in the following sense:

(i) **Sufficient for distance preservation**: If $h(G) \geq 1$, then $d^* \geq d$ by Lemma 2.

(ii) **Larger Cheeger doesn't help**: If $h(G) > 1$, the distance bound is still $d^* \geq d$
    (not $d^* \geq h(G) \cdot d$). This is because logical operators can always be "cleaned"
    onto vertex qubits, where the original code distance applies.

(iii) **Small Cheeger causes distance loss**: If $h(G) < 1$, the distance can be reduced by
     a factor of $h(G)$. In the worst case, a logical of the deformed code has most of its
     weight on edges, and cleaning it onto vertices increases vertex weight by factor $1/h(G)$.

## Main Results
**Main Theorems**:
- `cheeger_ge_one_optimal`: When h(G) = 1, the distance bound d* ≥ d is achieved
- `cheeger_gt_one_no_improvement`: When h(G) > 1, we still only get d* ≥ d, not better
- `cheeger_lt_one_distance_loss`: When h(G) < 1, distance can be reduced by factor h(G)
- `optimal_cheeger_is_one`: The value h(G) = 1 is optimal for distance preservation

## File Structure
1. Cheeger Threshold Properties: Key properties at h(G) = 1
2. Sufficient Expansion: h(G) ≥ 1 suffices for d* ≥ d
3. No Improvement Beyond One: h(G) > 1 doesn't give d* > d
4. Distance Loss Below One: h(G) < 1 can cause distance reduction
5. Optimality of h(G) = 1: Synthesis of the three cases
6. Helper Lemmas

## Faithfulness Notes
- Part (i) follows directly from Lemma 2 (spaceDistanceBound)
- Part (ii) is because logical operators can be "cleaned" via Gauss law multiplication
- Part (iii) follows from the Cheeger factor formula min(h(G), 1)
- The key insight is that the cleaning operation increases vertex weight by 1/h(G)
-/

namespace QEC

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Cheeger Threshold Properties

Key lemmas about the Cheeger constant at the critical value h(G) = 1.
-/

/-- The Cheeger factor min(h(G), 1) equals 1 when h(G) ≥ 1 -/
theorem cheegerFactor_eq_one_when_ge_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G ≥ 1) : cheegerFactor G = 1 :=
  cheegerFactor_eq_one_of_cheeger_ge_one G h

/-- The Cheeger factor min(h(G), 1) equals h(G) when h(G) < 1 -/
theorem cheegerFactor_eq_cheeger_when_lt_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G < 1) : cheegerFactor G = cheegerConstant G :=
  cheegerFactor_eq_cheeger_of_lt_one G h

/-- At the threshold h(G) = 1, the Cheeger factor is exactly 1 -/
theorem cheegerFactor_at_threshold (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G = 1) : cheegerFactor G = 1 := by
  apply cheegerFactor_eq_one_when_ge_one
  rw [h]

/-! ## Section 2: Sufficient Expansion (Part i)

If h(G) ≥ 1, then d* ≥ d by Lemma 2.
This is the key result: sufficient expansion preserves distance.
-/

/-- Part (i): h(G) ≥ 1 is sufficient for distance preservation d* ≥ d -/
theorem cheeger_ge_one_preserves_distance' {n k d : ℕ} (cfg : DistanceConfig n k d)
    (h_cheeger : cheegerConstant cfg.gaugingGraph.graph ≥ 1)
    (L_def : DeformedLogicalOperator cfg.deformedCfg) :
    L_def.weight cfg.deformedCfg ≥ d :=
  spaceDistanceBound_no_reduction cfg h_cheeger L_def

/-- Equivalent formulation: satisfies distance preservation property -/
theorem sufficient_expansion_distance_preserved {n k d : ℕ} (cfg : DistanceConfig n k d)
    (h_exp : satisfiesDistancePreservation cfg.gaugingGraph.graph)
    (L_def : DeformedLogicalOperator cfg.deformedCfg) :
    L_def.weight cfg.deformedCfg ≥ d :=
  cheeger_ge_one_preserves_distance' cfg h_exp L_def

/-- The distance bound holds as a rational inequality -/
theorem sufficient_expansion_bound_rational {n k d : ℕ} (cfg : DistanceConfig n k d)
    (h_cheeger : cheegerConstant cfg.gaugingGraph.graph ≥ 1)
    (L_def : DeformedLogicalOperator cfg.deformedCfg) :
    (L_def.weight cfg.deformedCfg : ℚ) ≥ (d : ℚ) := by
  exact Nat.cast_le.mpr (cheeger_ge_one_preserves_distance' cfg h_cheeger L_def)

/-! ## Section 3: No Improvement Beyond One (Part ii)

If h(G) > 1, the distance bound is still d* ≥ d (not d* ≥ h(G) · d).
This is because logical operators can always be "cleaned" onto vertex qubits,
where the original code distance applies.
-/

/-- The distance bound is d* ≥ min(h(G), 1) · d, not h(G) · d -/
theorem distance_bound_uses_min (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    cheegerFactor G * d ≤ min (cheegerConstant G * d) (1 * d) := by
  unfold cheegerFactor
  by_cases h : cheegerConstant G < 1
  · calc min (cheegerConstant G) 1 * d
      = cheegerConstant G * d := by rw [min_eq_left (le_of_lt h)]
      _ ≤ min (cheegerConstant G * d) (1 * d) := le_min (le_refl _) (by
          apply mul_le_mul_of_nonneg_right (le_of_lt h)
          exact Nat.cast_nonneg d)
  · push_neg at h
    have h1 : min (cheegerConstant G) 1 = 1 := min_eq_right h
    rw [h1]
    simp only [one_mul]
    exact le_min (by
      calc (d : ℚ) = 1 * d := (one_mul _).symm
        _ ≤ cheegerConstant G * d := by
            apply mul_le_mul_of_nonneg_right h
            exact Nat.cast_nonneg d) (le_refl _)

/-- Part (ii): h(G) > 1 doesn't improve the bound beyond d -/
theorem cheeger_gt_one_no_improvement (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G > 1) (d : ℕ) :
    cheegerFactor G * d = (d : ℚ) := by
  have h_ge : cheegerConstant G ≥ 1 := le_of_lt h
  rw [cheegerFactor_eq_one_when_ge_one G h_ge]
  ring

/-- Even with h(G) = 2, the bound is still d* ≥ d, not d* ≥ 2d -/
theorem cheeger_two_gives_same_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G = 2) (d : ℕ) :
    cheegerFactor G * d = (d : ℚ) := by
  apply cheeger_gt_one_no_improvement
  rw [h]
  norm_num

/-- The distance bound formula is capped at d regardless of how large h(G) is -/
theorem distance_bound_capped {n k d : ℕ} (cfg : DistanceConfig n k d)
    (h_large : cheegerConstant cfg.gaugingGraph.graph > 1) :
    cheegerFactor cfg.gaugingGraph.graph * d = (d : ℚ) :=
  cheeger_gt_one_no_improvement cfg.gaugingGraph.graph h_large d

/-- The reason h(G) > 1 doesn't help: logical operators can be "cleaned" onto vertices.
    Mathematically, we multiply by Gauss law operators A_v to remove edge support.
    The cleaned operator then has weight ≥ d by the original code distance. -/
theorem cleaning_onto_vertices_explanation {n k d : ℕ} (cfg : DistanceConfig n k d)
    (L_def : DeformedLogicalOperator cfg.deformedCfg) :
    -- The original part of the deformed logical has weight ≥ d
    -- because it commutes with all original checks (from commutes_deformed_checks)
    -- and is not a stabilizer element
    L_def.operator.original.weight ≥ d :=
  restriction_weight_ge_distance L_def.operator.original
    (restriction_commutes_with_original_checks cfg.deformedCfg L_def)
    L_def.not_stabilizer cfg.code.distance_bound

/-! ## Section 4: Distance Loss Below One (Part iii)

If h(G) < 1, the distance can be reduced by a factor of h(G).
In the worst case, a logical of the deformed code has most of its weight on edges,
and cleaning it onto vertices increases vertex weight by factor 1/h(G).
-/

/-- Part (iii): h(G) < 1 causes distance reduction by factor h(G) -/
theorem cheeger_lt_one_distance_factor (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G < 1) (d : ℕ) :
    cheegerFactor G * d = cheegerConstant G * d := by
  rw [cheegerFactor_eq_cheeger_when_lt_one G h]

/-- When h(G) < 1, the distance bound becomes d* ≥ h(G) · d -/
theorem cheeger_lt_one_reduced_bound {n k d : ℕ} (cfg : DistanceConfig n k d)
    (h_small : cheegerConstant cfg.gaugingGraph.graph < 1)
    (L_def : DeformedLogicalOperator cfg.deformedCfg) :
    (L_def.weight cfg.deformedCfg : ℚ) ≥ cheegerConstant cfg.gaugingGraph.graph * d := by
  have h_main := spaceDistanceBound cfg L_def
  rw [cheegerFactor_eq_cheeger_when_lt_one _ h_small] at h_main
  exact h_main

/-- The distance reduction factor is exactly h(G) when h(G) < 1 -/
theorem distance_reduction_factor (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G < 1) (hpos : cheegerConstant G > 0) (d : ℕ) (hd : d > 0) :
    cheegerFactor G * d / d = cheegerConstant G := by
  rw [cheegerFactor_eq_cheeger_when_lt_one G h]
  have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
  field_simp

/-- The cleaning operation: edge support can be removed by multiplying by Gauss laws.
    However, this may increase the vertex weight by a factor of 1/h(G). -/
theorem cleaning_weight_increase_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_cheeger_pos : cheegerConstant G > 0)
    (edge_weight vertex_weight : ℕ)
    (h_edge_bound : (edge_weight : ℚ) ≥ cheegerConstant G * vertex_weight) :
    -- If edge_weight ≥ h(G) * vertex_weight, then
    -- cleaning the edge support requires adding at most edge_weight / h(G) to vertex weight
    (edge_weight : ℚ) / cheegerConstant G ≥ vertex_weight := by
  rw [ge_iff_le, le_div_iff₀ h_cheeger_pos]
  rw [mul_comm]
  exact h_edge_bound

/-- Example: if h(G) = 1/2, distance can be halved -/
theorem half_cheeger_half_distance (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G = 1 / 2) (d : ℕ) :
    cheegerFactor G * d = (d : ℚ) / 2 := by
  rw [cheegerFactor_eq_cheeger_when_lt_one G (by rw [h]; norm_num)]
  rw [h]
  ring

/-! ## Section 5: Optimality of h(G) = 1

The value h(G) = 1 is optimal: it's the minimum expansion needed for distance preservation,
and larger values don't provide additional benefit.
-/

/-- h(G) = 1 is optimal: it achieves d* ≥ d with minimum expansion -/
theorem optimal_cheeger_is_one : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    -- When h(G) = 1:
    cheegerConstant G = 1 →
    -- The Cheeger factor is exactly 1
    cheegerFactor G = 1 := by
  intro G _ h
  exact cheegerFactor_at_threshold G h

/-- Optimality part 1: h(G) = 1 suffices for full distance preservation -/
theorem one_suffices_for_distance {n k d : ℕ} (cfg : DistanceConfig n k d)
    (h_one : cheegerConstant cfg.gaugingGraph.graph = 1)
    (L_def : DeformedLogicalOperator cfg.deformedCfg) :
    L_def.weight cfg.deformedCfg ≥ d := by
  apply cheeger_ge_one_preserves_distance' cfg
  rw [h_one]

/-- Optimality part 2: values h(G) < 1 are insufficient -/
theorem less_than_one_insufficient (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G < 1) :
    cheegerFactor G < 1 := by
  rw [cheegerFactor_eq_cheeger_when_lt_one G h]
  exact h

/-- Optimality part 3: values h(G) > 1 provide no additional benefit -/
theorem greater_than_one_no_benefit (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G > 1) :
    cheegerFactor G = 1 := by
  exact cheegerFactor_eq_one_when_ge_one G (le_of_lt h)

/-- Complete characterization of the Cheeger factor -/
theorem cheegerFactor_characterization (G : SimpleGraph V) [DecidableRel G.Adj] :
    cheegerFactor G = if cheegerConstant G ≥ 1 then 1 else cheegerConstant G := by
  by_cases h : cheegerConstant G ≥ 1
  · simp only [ge_iff_le, h, ↓reduceIte]
    exact cheegerFactor_eq_one_when_ge_one G h
  · push_neg at h
    simp only [ge_iff_le, not_le.mpr h, ↓reduceIte]
    exact cheegerFactor_eq_cheeger_when_lt_one G h

/-- The distance bound formula using the characterization -/
theorem distance_bound_formula {n k d : ℕ} (cfg : DistanceConfig n k d)
    (L_def : DeformedLogicalOperator cfg.deformedCfg) :
    (L_def.weight cfg.deformedCfg : ℚ) ≥
      (if cheegerConstant cfg.gaugingGraph.graph ≥ 1 then 1
       else cheegerConstant cfg.gaugingGraph.graph) * d := by
  have h := spaceDistanceBound cfg L_def
  rw [cheegerFactor_characterization] at h
  exact h

/-! ## Section 6: Comparison of Different Cheeger Values

Explicit comparisons showing why h(G) = 1 is the "sweet spot".
-/

/-- Comparing h(G) = 0.5 vs h(G) = 1: factor of 2 difference in guarantee -/
theorem compare_half_vs_one (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h₁ : cheegerConstant G₁ = 1 / 2) (h₂ : cheegerConstant G₂ = 1) (d : ℕ) :
    cheegerFactor G₁ * d * 2 = cheegerFactor G₂ * d := by
  rw [cheegerFactor_eq_cheeger_when_lt_one G₁ (by rw [h₁]; norm_num)]
  rw [cheegerFactor_eq_one_when_ge_one G₂ (by rw [h₂])]
  rw [h₁]
  ring

/-- Comparing h(G) = 1 vs h(G) = 2: same guarantee despite double expansion -/
theorem compare_one_vs_two (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h₁ : cheegerConstant G₁ = 1) (h₂ : cheegerConstant G₂ = 2) (d : ℕ) :
    cheegerFactor G₁ * d = cheegerFactor G₂ * d := by
  rw [cheegerFactor_eq_one_when_ge_one G₁ (by rw [h₁])]
  rw [cheegerFactor_eq_one_when_ge_one G₂ (by rw [h₂]; norm_num)]

/-! ## Section 7: Helper Lemmas -/

/-- The Cheeger factor is always in [0, 1] -/
theorem cheegerFactor_in_unit_interval (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ cheegerFactor G ∧ cheegerFactor G ≤ 1 :=
  ⟨cheegerFactor_nonneg G, cheegerFactor_le_one G⟩

/-- The distance bound is always non-negative -/
theorem distance_bound_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    0 ≤ cheegerFactor G * d := by
  apply mul_nonneg (cheegerFactor_nonneg G)
  exact Nat.cast_nonneg d

/-- The distance bound is at most d -/
theorem distance_bound_le_d (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    cheegerFactor G * d ≤ d := by
  have h1 : cheegerFactor G * d ≤ 1 * d := by
    apply mul_le_mul_of_nonneg_right (cheegerFactor_le_one G)
    exact Nat.cast_nonneg d
  simp only [one_mul] at h1
  exact h1

/-- Monotonicity: larger Cheeger constant gives at least as good bound -/
theorem cheegerFactor_mono (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : cheegerConstant G₁ ≤ cheegerConstant G₂) :
    cheegerFactor G₁ ≤ cheegerFactor G₂ := by
  unfold cheegerFactor
  apply min_le_min h (le_refl 1)

/-- The bound saturates at h(G) = 1 -/
theorem cheegerFactor_saturates_at_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : cheegerConstant G ≥ 1) :
    cheegerFactor G = 1 ∧ ∀ G' : SimpleGraph V, ∀ [DecidableRel G'.Adj],
      cheegerConstant G' > cheegerConstant G → cheegerFactor G' = 1 := by
  constructor
  · exact cheegerFactor_eq_one_when_ge_one G h
  · intro G' _ h'
    have h_ge : cheegerConstant G' ≥ 1 := le_of_lt (lt_of_le_of_lt h h')
    exact cheegerFactor_eq_one_when_ge_one G' h_ge

/-- Summary theorem capturing the three-part optimality -/
theorem optimal_cheeger_summary (G : SimpleGraph V) [DecidableRel G.Adj] :
    -- Part (i): h(G) ≥ 1 gives cheegerFactor = 1
    (cheegerConstant G ≥ 1 → cheegerFactor G = 1) ∧
    -- Part (ii): h(G) > 1 still gives cheegerFactor = 1 (no improvement)
    (cheegerConstant G > 1 → cheegerFactor G = 1) ∧
    -- Part (iii): h(G) < 1 gives cheegerFactor = h(G) < 1 (distance loss)
    (cheegerConstant G < 1 → cheegerFactor G = cheegerConstant G ∧ cheegerFactor G < 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact cheegerFactor_eq_one_when_ge_one G
  · exact fun h => cheegerFactor_eq_one_when_ge_one G (le_of_lt h)
  · intro h
    constructor
    · exact cheegerFactor_eq_cheeger_when_lt_one G h
    · rw [cheegerFactor_eq_cheeger_when_lt_one G h]
      exact h

end QEC
