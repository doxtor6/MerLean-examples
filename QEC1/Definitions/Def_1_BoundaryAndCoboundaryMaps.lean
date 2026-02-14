import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Definition 1: Boundary and Coboundary Maps

## Statement
Let G = (V, E) be a graph. We define ZMod 2-linear maps:
1. Boundary map ∂ : Z₂^E → Z₂^V with (∂ γ)_v = Σ_{e ∋ v} γ_e (mod 2)
2. Coboundary map δ : Z₂^V → Z₂^E defined as the transpose δ = ∂^T
3. Second boundary map ∂₂ : Z₂^C → Z₂^E with ∂₂(c) = Σ_{e ∈ c} e
4. Second coboundary map δ₂ : Z₂^E → Z₂^C defined as the transpose δ₂ = ∂₂^T

## Main Results
- `boundaryMap` : the boundary map ∂
- `coboundaryMap` : the coboundary map δ
- `coboundaryMap_eq_transpose` : δ is the transpose of ∂
- `secondBoundaryMap` : the second boundary map ∂₂
- `secondCoboundaryMap` : the second coboundary map δ₂
- `secondCoboundaryMap_eq_transpose` : δ₂ is the transpose of ∂₂
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GraphMaps

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Boundary Map -/

/-- The boundary map ∂ : Z₂^E → Z₂^V. For γ ∈ Z₂^E, (∂ γ)_v = Σ_{e ∋ v} γ_e (mod 2). -/
noncomputable def boundaryMap [Fintype G.edgeSet] :
    (G.edgeSet → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) where
  toFun γ v := ∑ e : G.edgeSet, if (v ∈ (e : Sym2 V)) then γ e else 0
  map_add' := by
    intro γ₁ γ₂; ext v; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]; congr 1; ext e
    split <;> simp
  map_smul' := by
    intro r γ; ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext e
    split <;> simp [mul_comm]

/-! ## Coboundary Map -/

/-- The coboundary map δ : Z₂^V → Z₂^E. For f ∈ Z₂^V and edge e = {a,b},
    (δ f)_e = f(a) + f(b) (mod 2). -/
noncomputable def coboundaryMap [Fintype G.edgeSet] :
    (V → ZMod 2) →ₗ[ZMod 2] (G.edgeSet → ZMod 2) where
  toFun f e := Sym2.lift ⟨fun a b => f a + f b, fun a b => by ring⟩ (e : Sym2 V)
  map_add' := by
    intro f₁ f₂; ext ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b => simp [Sym2.lift_mk, Pi.add_apply]; ring
  map_smul' := by
    intro r f; ext ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b => simp [Sym2.lift_mk, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add]

/-! ## Transpose Properties -/

/-- δ is the transpose of ∂: ⟨δ f, γ⟩_E = ⟨f, ∂ γ⟩_V for the standard Z₂ inner product. -/
theorem coboundaryMap_eq_transpose [Fintype G.edgeSet]
    (f : V → ZMod 2) (γ : G.edgeSet → ZMod 2) :
    ∑ e : G.edgeSet, coboundaryMap G f e * γ e =
    ∑ v : V, f v * boundaryMap G γ v := by
  simp only [coboundaryMap, boundaryMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ⟨e_val, he⟩ _
  induction e_val using Sym2.ind with
  | _ a b =>
    simp only [Sym2.lift_mk]
    have hab : a ≠ b := by
      intro h; subst h; exact G.loopless a (G.mem_edgeSet.mp he)
    rw [add_mul]
    have key : ∀ x : V, f x * (if (x ∈ s(a, b)) then γ ⟨s(a, b), he⟩ else 0) =
        if x = a then f a * γ ⟨s(a, b), he⟩ else
        if x = b then f b * γ ⟨s(a, b), he⟩ else 0 := by
      intro x
      by_cases hxa : x = a
      · subst hxa; simp [Sym2.mem_iff]
      · by_cases hxb : x = b
        · subst hxb; simp [Sym2.mem_iff, hxa]
        · have : x ∉ s(a, b) := by rw [Sym2.mem_iff]; push_neg; exact ⟨hxa, hxb⟩
          simp [this, hxa, hxb]
    simp_rw [key]
    have split_sum : ∀ x : V,
        (if x = a then f a * γ ⟨s(a, b), he⟩ else
         if x = b then f b * γ ⟨s(a, b), he⟩ else 0) =
        (if x = a then f a * γ ⟨s(a, b), he⟩ else 0) +
        (if x = b then f b * γ ⟨s(a, b), he⟩ else 0) := by
      intro x
      by_cases hxa : x = a
      · subst hxa; simp [hab]
      · simp [hxa]
    simp_rw [split_sum]
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']

variable {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]

/-! ## Second Boundary and Coboundary Maps -/

/-- The second boundary map ∂₂ : Z₂^C → Z₂^E. For σ ∈ Z₂^C,
    (∂₂ σ)_e = Σ_{c ∋ e} σ_c (mod 2). -/
noncomputable def secondBoundaryMap [Fintype G.edgeSet] :
    (C → ZMod 2) →ₗ[ZMod 2] (G.edgeSet → ZMod 2) where
  toFun σ e := ∑ c : C, if (e ∈ cycles c) then σ c else 0
  map_add' := by
    intro σ₁ σ₂; ext e; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]; congr 1; ext c
    split <;> simp
  map_smul' := by
    intro r σ; ext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext c
    split <;> simp [mul_comm]

/-- The second coboundary map δ₂ : Z₂^E → Z₂^C. For γ ∈ Z₂^E,
    (δ₂ γ)_c = Σ_{e ∈ c} γ_e (mod 2). -/
noncomputable def secondCoboundaryMap [Fintype G.edgeSet] :
    (G.edgeSet → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2) where
  toFun γ c := ∑ e : G.edgeSet, if (e ∈ cycles c) then γ e else 0
  map_add' := by
    intro γ₁ γ₂; ext c; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]; congr 1; ext e
    split <;> simp
  map_smul' := by
    intro r γ; ext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext e
    split <;> simp [mul_comm]

/-- δ₂ is the transpose of ∂₂: ⟨δ₂ γ, σ⟩_C = ⟨γ, ∂₂ σ⟩_E. -/
theorem secondCoboundaryMap_eq_transpose [Fintype G.edgeSet]
    (γ : G.edgeSet → ZMod 2) (σ : C → ZMod 2) :
    ∑ c : C, secondCoboundaryMap G cycles γ c * σ c =
    ∑ e : G.edgeSet, γ e * secondBoundaryMap G cycles σ e := by
  simp only [secondCoboundaryMap, secondBoundaryMap, LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS = Σ_c (Σ_e [e ∈ c] γ e) * σ c = Σ_c Σ_e [e ∈ c] γ e * σ c
  -- RHS = Σ_e γ e * (Σ_c [e ∈ c] σ c) = Σ_e Σ_c [e ∈ c] γ e * σ c
  conv_lhs =>
    arg 2; ext c
    rw [Finset.sum_mul]
  conv_rhs =>
    arg 2; ext e
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro c _
  split
  · next _h => ring
  · next _h => simp

/-! ## Evaluation Lemmas -/

@[simp]
theorem boundaryMap_apply [Fintype G.edgeSet]
    (γ : G.edgeSet → ZMod 2) (v : V) :
    boundaryMap G γ v = ∑ e : G.edgeSet, if (v ∈ (e : Sym2 V)) then γ e else 0 :=
  rfl

@[simp]
theorem coboundaryMap_apply [Fintype G.edgeSet]
    (f : V → ZMod 2) (e : G.edgeSet) :
    coboundaryMap G f e = Sym2.lift ⟨fun a b => f a + f b,
      fun a b => by ring⟩ (e : Sym2 V) :=
  rfl

@[simp]
theorem secondBoundaryMap_apply [Fintype G.edgeSet]
    (σ : C → ZMod 2) (e : G.edgeSet) :
    secondBoundaryMap G cycles σ e = ∑ c : C, if (e ∈ cycles c) then σ c else 0 :=
  rfl

@[simp]
theorem secondCoboundaryMap_apply [Fintype G.edgeSet]
    (γ : G.edgeSet → ZMod 2) (c : C) :
    secondCoboundaryMap G cycles γ c = ∑ e : G.edgeSet, if (e ∈ cycles c) then γ e else 0 :=
  rfl

/-! ## Basis Vector Evaluation -/

/-- The boundary of a single-edge indicator: (∂ 1_e)(v) = 1 iff v is an endpoint of e. -/
theorem boundaryMap_single [Fintype G.edgeSet]
    (e : G.edgeSet) (v : V) :
    boundaryMap G (Pi.single e 1) v =
    if (v ∈ (e : Sym2 V)) then 1 else 0 := by
  simp only [boundaryMap_apply]
  trans (∑ e' : G.edgeSet, if e' = e then (if (v ∈ (e' : Sym2 V)) then (1 : ZMod 2) else 0)
    else 0)
  · apply Finset.sum_congr rfl; intro e' _
    by_cases he : v ∈ (e' : Sym2 V)
    · simp [he, Pi.single_apply]
    · simp [he]
  · simp [Finset.sum_ite_eq']

/-- The coboundary of a single-vertex indicator: (δ 1_v)(e) = 1 iff v ∈ e. -/
theorem coboundaryMap_single [Fintype G.edgeSet]
    (v : V) (e : G.edgeSet) :
    coboundaryMap G (Pi.single v 1) e =
    if (v ∈ (e : Sym2 V)) then 1 else 0 := by
  simp only [coboundaryMap_apply]
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | _ a b =>
    simp only [Sym2.lift_mk]
    change _ = if v ∈ s(a, b) then 1 else 0
    have hab : a ≠ b := by
      intro h; subst h; exact G.loopless a (G.mem_edgeSet.mp he)
    by_cases hva : v = a
    · subst hva
      simp [Sym2.mem_iff, Pi.single_apply, hab]
    · by_cases hvb : v = b
      · subst hvb
        simp [Sym2.mem_iff, Pi.single_apply, Ne.symm hab]
      · have hv : v ∉ s(a, b) := by rw [Sym2.mem_iff]; push_neg; exact ⟨hva, hvb⟩
        rw [if_neg hv]
        simp [Pi.single_apply, hva, hvb]

/-- ∂₂ on a single cycle c: (∂₂ 1_c)(e) = 1 iff e ∈ c. -/
theorem secondBoundaryMap_single [Fintype G.edgeSet]
    (c : C) (e : G.edgeSet) :
    secondBoundaryMap G cycles (Pi.single c 1) e =
    if (e ∈ cycles c) then 1 else 0 := by
  simp only [secondBoundaryMap_apply]
  trans (∑ c' : C, if c' = c then (if (e ∈ cycles c') then (1 : ZMod 2) else 0) else 0)
  · apply Finset.sum_congr rfl; intro c' _
    by_cases hc : e ∈ cycles c'
    · simp [hc, Pi.single_apply]
    · simp [hc]
  · simp [Finset.sum_ite_eq']

/-- δ₂ on a single edge e: (δ₂ 1_e)(c) = 1 iff e ∈ c. -/
theorem secondCoboundaryMap_single [Fintype G.edgeSet]
    (e : G.edgeSet) (c : C) :
    secondCoboundaryMap G cycles (Pi.single e 1) c =
    if (e ∈ cycles c) then 1 else 0 := by
  simp only [secondCoboundaryMap_apply]
  trans (∑ e' : G.edgeSet, if e' = e then (if (e' ∈ cycles c) then (1 : ZMod 2) else 0) else 0)
  · apply Finset.sum_congr rfl; intro e' _
    by_cases he : e' ∈ cycles c
    · simp [he, Pi.single_apply]
    · simp [he]
  · simp [Finset.sum_ite_eq']

/-! ## Zero Properties -/

@[simp]
theorem boundaryMap_zero [Fintype G.edgeSet] (v : V) :
    boundaryMap G (0 : G.edgeSet → ZMod 2) v = 0 := by
  simp [boundaryMap_apply]

@[simp]
theorem coboundaryMap_zero [Fintype G.edgeSet] (e : G.edgeSet) :
    coboundaryMap G (0 : V → ZMod 2) e = 0 := by
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | _ a b => simp [coboundaryMap_apply, Sym2.lift_mk]

@[simp]
theorem secondBoundaryMap_zero [Fintype G.edgeSet] (e : G.edgeSet) :
    secondBoundaryMap G cycles (0 : C → ZMod 2) e = 0 := by
  simp [secondBoundaryMap_apply]

@[simp]
theorem secondCoboundaryMap_zero [Fintype G.edgeSet] (c : C) :
    secondCoboundaryMap G cycles (0 : G.edgeSet → ZMod 2) c = 0 := by
  simp [secondCoboundaryMap_apply]

end GraphMaps
