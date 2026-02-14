import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Remark 5: Exactness of Sequences

## Statement
For a graph G = (V, E) with a collection of cycles C (where each cycle c ∈ C is specified
by its edge set, and each vertex of G that appears in c is incident to exactly two edges of c),
the maps ∂₂ and ∂ satisfy the chain complex property ∂ ∘ ∂₂ = 0.

Similarly, δ₂ ∘ δ = 0 holds by transposition.

For a connected graph, ker(δ) = {0, 1} (constant functions), so the sequences are not
short exact since ker(δ) ≠ 0.

If C generates the cycle space (im(∂₂) = ker(∂)), then ker(∂) = im(∂₂).

## Main Results
- `boundary_comp_secondBoundary_eq_zero` : ∂ ∘ ∂₂ = 0 (chain complex property)
- `secondCoboundary_comp_coboundary_eq_zero` : δ₂ ∘ δ = 0 (by transposition)
- `range_secondBoundary_le_ker_boundary` : im(∂₂) ≤ ker(∂)
- `range_coboundary_le_ker_secondCoboundary` : im(δ) ≤ ker(δ₂)
- `allOnes_mem_ker_coboundary` : the all-ones vector is in ker(δ)
- `ker_coboundary_connected` : for connected G, ker(δ) = {0, 1}
- `ker_coboundary_ne_bot` : ker(δ) ≠ 0 (sequences are not short exact)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GraphMaps

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

variable {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]

/-! ## Chain Complex Property: ∂ ∘ ∂₂ = 0 -/

/-- Helper: if every cycle in the collection has the property that each vertex is incident
    to an even number of its edges, then the boundary of a single cycle indicator is zero. -/
theorem boundary_of_cycle_eq_zero [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (c : C) (v : V) :
    boundaryMap G (fun e => if e ∈ cycles c then 1 else 0) v = 0 := by
  simp only [boundaryMap_apply]
  conv_lhs => arg 2; ext e; rw [show (if v ∈ (e : Sym2 V) then
    (if e ∈ cycles c then 1 else 0 : ZMod 2) else 0) =
    (if (e ∈ cycles c ∧ v ∈ (e : Sym2 V)) then 1 else 0) from by split_ifs <;> tauto]
  rw [Finset.sum_boole]
  rw [ZMod.natCast_eq_zero_iff_even]
  exact hcyc c v

/-- ∂₂(1_c) applied through ∂ gives zero for each cycle c. -/
theorem boundaryMap_comp_secondBoundaryMap_single [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (c : C) (v : V) :
    boundaryMap G (secondBoundaryMap G cycles (Pi.single c 1)) v = 0 := by
  simp only [boundaryMap_apply, secondBoundaryMap_apply]
  have key : ∀ e : G.edgeSet,
      (∑ c' : C, if e ∈ cycles c' then Pi.single c (1 : ZMod 2) c' else 0) =
      if e ∈ cycles c then 1 else 0 := by
    intro e
    trans (∑ c' : C, if c' = c then (if e ∈ cycles c' then (1 : ZMod 2) else 0) else 0)
    · apply Finset.sum_congr rfl; intro c' _
      by_cases hc : e ∈ cycles c'
      · simp [hc, Pi.single_apply]
      · simp [hc]
    · simp [Finset.sum_ite_eq']
  conv_lhs =>
    arg 2; ext e
    rw [show (if v ∈ (e : Sym2 V) then
      ∑ c' : C, (if e ∈ cycles c' then Pi.single c (1 : ZMod 2) c' else 0) else 0) =
      (if v ∈ (e : Sym2 V) then (if e ∈ cycles c then (1 : ZMod 2) else 0) else 0) from by
        by_cases hv : v ∈ (e : Sym2 V)
        · simp only [hv, ite_true]; exact key e
        · simp [hv]]
  exact boundary_of_cycle_eq_zero G cycles hcyc c v

/-- **Chain complex property**: ∂ ∘ ∂₂ = 0, given that each cycle in the collection has the
    property that each vertex is incident to an even number of its edges. -/
theorem boundary_comp_secondBoundary_eq_zero [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card) :
    (boundaryMap G).comp (secondBoundaryMap G cycles) = 0 := by
  apply LinearMap.ext; intro σ; funext v
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  -- ∂(∂₂ σ)(v) = Σ_e [v ∈ e] (∂₂ σ)(e) = Σ_e [v ∈ e] Σ_c [e ∈ c] σ_c
  -- = Σ_c σ_c · Σ_e [v ∈ e, e ∈ c] 1 = Σ_c σ_c · (∂(1_c))(v) = 0
  -- We use the transpose identity directly
  simp only [boundaryMap_apply, secondBoundaryMap_apply]
  -- Goal: Σ_e [v ∈ e] (Σ_c [e ∈ c] σ_c) = 0
  -- Swap sums: = Σ_c σ_c · (Σ_e [v ∈ e, e ∈ c] 1) = Σ_c σ_c · 0 = 0
  conv_lhs =>
    arg 2; ext e; rw [show (if v ∈ (e : Sym2 V) then
      ∑ c : C, (if e ∈ cycles c then σ c else 0) else 0) =
      ∑ c : C, (if (e ∈ cycles c ∧ v ∈ (e : Sym2 V)) then σ c else 0) from by
        split_ifs with hv
        · congr 1; ext c; split_ifs <;> tauto
        · symm; apply Finset.sum_eq_zero; intro c _; simp [hv]]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  -- Inner sum: Σ_e [e ∈ c, v ∈ e] σ_c = σ_c · Σ_e [e ∈ c, v ∈ e] 1
  rw [show (∑ e : G.edgeSet, if (e ∈ cycles c ∧ v ∈ (e : Sym2 V)) then σ c else 0) =
      σ c * (∑ e : G.edgeSet, if (e ∈ cycles c ∧ v ∈ (e : Sym2 V)) then 1 else 0) from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _
        split_ifs <;> ring]
  -- The inner sum counts edges in c incident to v, which is even
  rw [Finset.sum_boole, ZMod.natCast_eq_zero_iff_even.mpr (hcyc c v), mul_zero]

/-- im(∂₂) ≤ ker(∂). -/
theorem range_secondBoundary_le_ker_boundary [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card) :
    LinearMap.range (secondBoundaryMap G cycles) ≤ LinearMap.ker (boundaryMap G) := by
  rw [LinearMap.range_le_ker_iff]
  exact boundary_comp_secondBoundary_eq_zero G cycles hcyc

/-! ## Coboundary Chain Complex: δ₂ ∘ δ = 0 -/

/-- **Coboundary chain complex property**: δ₂ ∘ δ = 0. By transposition from ∂ ∘ ∂₂ = 0. -/
theorem secondCoboundary_comp_coboundary_eq_zero [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card) :
    (secondCoboundaryMap G cycles).comp (coboundaryMap G) = 0 := by
  apply LinearMap.ext; intro f; funext c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    secondCoboundaryMap_apply, coboundaryMap_apply]
  -- Use transpose: ⟨δf, 1_c⟩_E = ⟨f, ∂(1_c)⟩_V = ⟨f, 0⟩ = 0
  let ind : G.edgeSet → ZMod 2 := fun e => if e ∈ cycles c then 1 else 0
  have h_tr : ∑ e : G.edgeSet, coboundaryMap G f e * ind e =
      ∑ v : V, f v * boundaryMap G ind v :=
    coboundaryMap_eq_transpose G f ind
  have h_bz : ∀ v, boundaryMap G ind v = 0 :=
    boundary_of_cycle_eq_zero G cycles hcyc c
  have h_lhs : ∑ e : G.edgeSet, coboundaryMap G f e * ind e =
      ∑ e : G.edgeSet, if e ∈ cycles c then coboundaryMap G f e else 0 := by
    apply Finset.sum_congr rfl; intro e _
    show coboundaryMap G f e * ind e = _
    simp only [ind]; split_ifs <;> ring
  have h_rhs : ∑ v : V, f v * boundaryMap G ind v = 0 := by
    apply Finset.sum_eq_zero; intro v _; rw [h_bz v]; ring
  -- Goal after simp: ∑ e, if e ∈ cycles c then (Sym2.lift ...) else 0 = 0
  have goal_eq : (∑ e : G.edgeSet,
      if e ∈ cycles c then Sym2.lift ⟨fun a b => f a + f b, fun a b => by ring⟩ ↑e else 0) =
      ∑ e : G.edgeSet, if e ∈ cycles c then coboundaryMap G f e else 0 := by
    apply Finset.sum_congr rfl; intro e _
    split_ifs <;> simp [coboundaryMap_apply]
  rw [goal_eq, ← h_lhs, h_tr, h_rhs]

/-- im(δ) ≤ ker(δ₂). -/
theorem range_coboundary_le_ker_secondCoboundary [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card) :
    LinearMap.range (coboundaryMap G) ≤ LinearMap.ker (secondCoboundaryMap G cycles) := by
  rw [LinearMap.range_le_ker_iff]
  exact secondCoboundary_comp_coboundary_eq_zero G cycles hcyc

/-! ## Kernel of the Coboundary Map -/

/-- The all-ones function 1 : V → ZMod 2. -/
def allOnes : V → ZMod 2 := fun _ => 1

/-- The all-ones vector is in ker(δ). -/
theorem allOnes_mem_ker_coboundary [Fintype G.edgeSet] :
    allOnes (V := V) ∈ LinearMap.ker (coboundaryMap G) := by
  rw [LinearMap.mem_ker]; ext ⟨e, he⟩
  induction e using Sym2.ind with
  | _ a b =>
    simp only [coboundaryMap_apply, Sym2.lift_mk, allOnes, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- Any constant function is in ker(δ). -/
theorem constant_mem_ker_coboundary [Fintype G.edgeSet] (a : ZMod 2) :
    (fun _ : V => a) ∈ LinearMap.ker (coboundaryMap G) := by
  rw [LinearMap.mem_ker]; ext ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
    simp only [coboundaryMap_apply, Sym2.lift_mk, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- f ∈ ker(δ) implies f(a) = f(b) for adjacent a, b. -/
theorem ker_coboundary_constant_on_adj [Fintype G.edgeSet]
    {f : V → ZMod 2} (hf : f ∈ LinearMap.ker (coboundaryMap G))
    {a b : V} (hab : G.Adj a b) : f a = f b := by
  rw [LinearMap.mem_ker] at hf
  have he : s(a, b) ∈ G.edgeSet := G.mem_edgeSet.mpr hab
  have h := congr_fun hf ⟨s(a, b), he⟩
  simp only [coboundaryMap_apply, Sym2.lift_mk, Pi.zero_apply] at h
  exact CharTwo.add_eq_zero.mp h

/-- f ∈ ker(δ) implies f is constant along walks. -/
theorem ker_coboundary_constant_on_walk [Fintype G.edgeSet]
    {f : V → ZMod 2} (hf : f ∈ LinearMap.ker (coboundaryMap G))
    {u w : V} (p : G.Walk u w) : f u = f w := by
  induction p with
  | nil => rfl
  | @cons u v w huv _ ih =>
    exact (ker_coboundary_constant_on_adj G hf huv).trans ih

/-- f ∈ ker(δ) implies f is constant on reachable vertices. -/
theorem ker_coboundary_constant_on_reachable [Fintype G.edgeSet]
    {f : V → ZMod 2} (hf : f ∈ LinearMap.ker (coboundaryMap G))
    {u w : V} (hr : G.Reachable u w) : f u = f w := by
  obtain ⟨p⟩ := hr
  exact ker_coboundary_constant_on_walk G hf p

/-- For a connected graph, f ∈ ker(δ) implies f is a constant function. -/
theorem ker_coboundary_is_constant [Fintype G.edgeSet]
    (hconn : G.Connected)
    {f : V → ZMod 2} (hf : f ∈ LinearMap.ker (coboundaryMap G)) :
    ∃ a : ZMod 2, f = fun _ => a := by
  obtain ⟨v₀⟩ := hconn.nonempty
  exact ⟨f v₀, funext fun w =>
    (ker_coboundary_constant_on_reachable G hf (hconn v₀ w)).symm⟩

/-- For a connected graph, ker(δ) consists exactly of the constant functions {0, 1}. -/
theorem ker_coboundary_connected [Fintype G.edgeSet]
    (hconn : G.Connected) :
    ∀ f : V → ZMod 2, f ∈ LinearMap.ker (coboundaryMap G) ↔
      (f = 0 ∨ f = allOnes (V := V)) := by
  intro f
  constructor
  · intro hf
    obtain ⟨a, ha⟩ := ker_coboundary_is_constant G hconn hf
    have : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases this with rfl | rfl
    · left; ext v; simp [ha]
    · right; ext v; simp [ha, allOnes]
  · rintro (rfl | rfl)
    · simp [LinearMap.mem_ker]
    · exact allOnes_mem_ker_coboundary G

/-- ker(δ) ≠ 0: the sequences are not short exact. -/
theorem ker_coboundary_ne_bot [Fintype G.edgeSet] [Nonempty V] :
    LinearMap.ker (coboundaryMap G) ≠ ⊥ := by
  intro h
  have h1 : allOnes (V := V) ∈ LinearMap.ker (coboundaryMap G) :=
    allOnes_mem_ker_coboundary G
  rw [h] at h1
  simp only [Submodule.mem_bot] at h1
  obtain ⟨v⟩ := ‹Nonempty V›
  have : allOnes (V := V) v = (0 : V → ZMod 2) v := congr_fun h1 v
  simp [allOnes] at this

/-! ## Corollaries -/

@[simp]
theorem zero_mem_ker_coboundary [Fintype G.edgeSet] :
    (0 : V → ZMod 2) ∈ LinearMap.ker (coboundaryMap G) :=
  Submodule.zero_mem _

/-- For any σ, ∂(∂₂ σ) = 0. -/
theorem boundary_secondBoundary_apply [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (σ : C → ZMod 2) :
    boundaryMap G (secondBoundaryMap G cycles σ) = 0 := by
  have h := boundary_comp_secondBoundary_eq_zero G cycles hcyc
  change ((boundaryMap G).comp (secondBoundaryMap G cycles)) σ = (0 : (C → ZMod 2) →ₗ[ZMod 2] _) σ
  rw [h]

/-- For any f, δ₂(δ f) = 0. -/
theorem secondCoboundary_coboundary_apply [Fintype G.edgeSet]
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (f : V → ZMod 2) :
    secondCoboundaryMap G cycles (coboundaryMap G f) = 0 := by
  have h := secondCoboundary_comp_coboundary_eq_zero G cycles hcyc
  change ((secondCoboundaryMap G cycles).comp (coboundaryMap G)) f =
    (0 : (V → ZMod 2) →ₗ[ZMod 2] _) f
  rw [h]

end GraphMaps
