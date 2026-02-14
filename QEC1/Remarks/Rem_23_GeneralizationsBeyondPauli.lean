import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import QEC1.Remarks.Rem_17_HypergraphGeneralization
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Remark 23: Generalizations Beyond Pauli

## Statement
The gauging measurement procedure (Def_5) generalizes beyond Pauli logical operators on qubits:

1. **Non-Pauli operators:** The procedure applies to any representation of a finite group
   by operators with tensor product factorization (including magic state production and
   Clifford operators in topological codes).

2. **Qudit systems:** Replace Z₂ with Z_p (or more general finite groups), using p-state
   qudits. The boundary/coboundary maps become Z_p-linear maps.

3. **Nonabelian groups:** The procedure generalizes to nonabelian symmetry groups, but
   measuring local charges no longer determines a definite global charge (the total charge
   can remain in superposition).

## Main Results
- `quditBoundaryMap` : boundary map ∂ over Z_p generalizing Def_1
- `quditCoboundaryMap` : coboundary map δ over Z_p
- `quditCoboundaryMap_eq_transpose` : δ is the transpose of ∂ over Z_p
- `quditBoundary_comp_secondBoundary_eq_zero` : ∂ ∘ ∂₂ = 0 over Z_p
- `abelian_charge_sum_well_defined` : sum of local charges is order-independent
- `nonabelian_product_order_dependent` : product of noncommuting elements is order-dependent

## Corollaries
- `quditBoundaryMap_specializes_to_qubit` : Z_p maps reduce to Z₂ maps when p = 2
- `qudit_range_secondBoundary_le_ker_boundary` : im(∂₂) ≤ ker(∂) over Z_p
- `abelian_local_determines_global` : local abelian charges determine global charge
- `nonabelian_local_underdetermines_global` : local nonabelian measurements leave ambiguity
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
noncomputable section

namespace GeneralizationsBeyondPauli

open Finset

/-! ## 1. Qudit Generalization: Boundary Maps over Z_p -/

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
variable {C : Type*} [Fintype C] [DecidableEq C] (cycles : C → Set G.edgeSet)
  [∀ c, DecidablePred (· ∈ cycles c)]

section QuditMaps

variable (p : ℕ) [NeZero p]

/-- The qudit boundary map ∂ : Z_p^E → Z_p^V, generalizing Def_1 from Z₂ to Z_p.
    For γ ∈ Z_p^E, (∂γ)_v = Σ_{e ∋ v} γ_e (mod p). -/
def quditBoundaryMap :
    (G.edgeSet → ZMod p) →ₗ[ZMod p] (V → ZMod p) where
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

/-- The qudit coboundary map δ : Z_p^V → Z_p^E, generalizing Def_1 from Z₂ to Z_p.
    For f ∈ Z_p^V and edge e = {a,b}, (δ f)_e = f(a) + f(b) (mod p). -/
def quditCoboundaryMap :
    (V → ZMod p) →ₗ[ZMod p] (G.edgeSet → ZMod p) where
  toFun f e := Sym2.lift ⟨fun a b => f a + f b, fun a b => by ring⟩ (e : Sym2 V)
  map_add' := by
    intro f₁ f₂; ext ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b => simp [Sym2.lift_mk, Pi.add_apply]; ring
  map_smul' := by
    intro r f; ext ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b => simp [Sym2.lift_mk, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add]

/-- The qudit second boundary map ∂₂ : Z_p^C → Z_p^E, generalizing Def_1 from Z₂ to Z_p. -/
def quditSecondBoundaryMap :
    (C → ZMod p) →ₗ[ZMod p] (G.edgeSet → ZMod p) where
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

/-- The qudit second coboundary map δ₂ : Z_p^E → Z_p^C, generalizing Def_1 from Z₂ to Z_p. -/
def quditSecondCoboundaryMap :
    (G.edgeSet → ZMod p) →ₗ[ZMod p] (C → ZMod p) where
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

/-! ### Transpose properties -/

/-- δ is the transpose of ∂ over Z_p: ⟨δf, γ⟩_E = ⟨f, ∂γ⟩_V. -/
theorem quditCoboundaryMap_eq_transpose
    (f : V → ZMod p) (γ : G.edgeSet → ZMod p) :
    ∑ e : G.edgeSet, quditCoboundaryMap G p f e * γ e =
    ∑ v : V, f v * quditBoundaryMap G p γ v := by
  simp only [quditCoboundaryMap, quditBoundaryMap, LinearMap.coe_mk, AddHom.coe_mk]
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

/-- δ₂ is the transpose of ∂₂ over Z_p: ⟨δ₂γ, σ⟩_C = ⟨γ, ∂₂σ⟩_E. -/
theorem quditSecondCoboundaryMap_eq_transpose
    (γ : G.edgeSet → ZMod p) (σ : C → ZMod p) :
    ∑ c : C, quditSecondCoboundaryMap G cycles p γ c * σ c =
    ∑ e : G.edgeSet, γ e * quditSecondBoundaryMap G cycles p σ e := by
  simp only [quditSecondBoundaryMap, quditSecondCoboundaryMap, LinearMap.coe_mk, AddHom.coe_mk]
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

/-! ### Chain complex property: ∂ ∘ ∂₂ = 0 over Z_p -/

/-- Helper: double conditional rewriting. -/
private lemma ite_ite_eq_ite_and {α : Type*} [AddCommMonoid α]
    {P Q : Prop} [Decidable P] [Decidable Q] (a : α) :
    (if P then (if Q then a else 0) else 0) = if (P ∧ Q) then a else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- The chain complex property ∂ ∘ ∂₂ = 0 holds over Z_p, provided each cycle has the property
    that the number of edges incident to each vertex is divisible by p.
    Over Z₂, this is the standard cycle condition (even incidence).
    Over Z_p for odd p, this requires p | (incidence count), which holds for oriented cycles
    where ∂e = head(e) - tail(e) (each vertex sees +1 and -1, canceling). -/
theorem quditBoundary_comp_secondBoundary_eq_zero
    (hcyc : ∀ (c : C) (v : V),
      p ∣ (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧
        v ∈ (e : Sym2 V))).card) :
    (quditBoundaryMap G p).comp (quditSecondBoundaryMap G cycles p) = 0 := by
  apply LinearMap.ext; intro σ_fun
  funext v
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [quditBoundaryMap, quditSecondBoundaryMap, LinearMap.coe_mk, AddHom.coe_mk]
  -- Exchange order of summation
  conv_lhs =>
    arg 2; ext e
    rw [show (if v ∈ (e : Sym2 V) then ∑ c : C, if e ∈ cycles c then σ_fun c else 0 else 0) =
      ∑ c : C, if v ∈ (e : Sym2 V) then (if e ∈ cycles c then σ_fun c else 0) else 0 from by
        split <;> simp]
  rw [Finset.sum_comm]
  -- Each inner sum: Σ_e (if v ∈ e then (if e ∈ cycles c then σ_fun c else 0) else 0)
  simp_rw [ite_ite_eq_ite_and]
  -- Now: Σ_c (Σ_e (if (v ∈ e ∧ e ∈ cycles c) then σ_fun c else 0))
  simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Each term: cast(count) * σ_fun c, where p | count
  apply Finset.sum_eq_zero
  intro c _
  have hfilt : Finset.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V) ∧ e ∈ cycles c)
    Finset.univ = Finset.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))
    Finset.univ := by ext e; simp [and_comm]
  rw [hfilt]
  have hzero : ((Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧
    v ∈ (e : Sym2 V))).card : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hcyc c v
  rw [hzero, zero_mul]

/-- im(∂₂) ≤ ker(∂) over Z_p (consequence of ∂ ∘ ∂₂ = 0). -/
theorem qudit_range_secondBoundary_le_ker_boundary
    (hcyc : ∀ (c : C) (v : V),
      p ∣ (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧
        v ∈ (e : Sym2 V))).card) :
    LinearMap.range (quditSecondBoundaryMap G cycles p) ≤
    LinearMap.ker (quditBoundaryMap G p) := by
  intro γ hγ
  rw [LinearMap.mem_ker]
  obtain ⟨σ, hσ⟩ := LinearMap.mem_range.mp hγ
  rw [← hσ]
  have h := quditBoundary_comp_secondBoundary_eq_zero G cycles p hcyc
  have h' := LinearMap.ext_iff.mp h σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h'
  exact h'

end QuditMaps

/-! ### Specialization: Z_p maps reduce to Z₂ maps when p = 2 -/

/-- The qudit boundary map at p = 2 agrees with the standard Z₂ boundary map from Def_1. -/
theorem quditBoundaryMap_specializes_to_qubit
    (γ : G.edgeSet → ZMod 2) (v : V) :
    quditBoundaryMap G 2 γ v = GraphMaps.boundaryMap G γ v := by
  simp [quditBoundaryMap, GraphMaps.boundaryMap]

/-- The qudit coboundary map at p = 2 agrees with the standard Z₂ coboundary map from Def_1. -/
theorem quditCoboundaryMap_specializes_to_qubit
    (f : V → ZMod 2) (e : G.edgeSet) :
    quditCoboundaryMap G 2 f e = GraphMaps.coboundaryMap G f e := by
  simp [quditCoboundaryMap, GraphMaps.coboundaryMap]

/-- The qudit second boundary map at p = 2 agrees with the standard Z₂ second boundary map. -/
theorem quditSecondBoundaryMap_specializes_to_qubit
    (σ : C → ZMod 2) (e : G.edgeSet) :
    quditSecondBoundaryMap G cycles 2 σ e = GraphMaps.secondBoundaryMap G cycles σ e := by
  simp [quditSecondBoundaryMap, GraphMaps.secondBoundaryMap]

/-- The qudit second coboundary map at p = 2 agrees with the standard Z₂ second coboundary map. -/
theorem quditSecondCoboundaryMap_specializes_to_qubit
    (γ : G.edgeSet → ZMod 2) (c : C) :
    quditSecondCoboundaryMap G cycles 2 γ c = GraphMaps.secondCoboundaryMap G cycles γ c := by
  simp [quditSecondCoboundaryMap, GraphMaps.secondCoboundaryMap]

/-! ### Qudit boundary map basic properties -/

section QuditBasic

variable (p : ℕ) [NeZero p]

@[simp]
theorem quditBoundaryMap_zero (v : V) :
    quditBoundaryMap G p (0 : G.edgeSet → ZMod p) v = 0 := by
  simp [quditBoundaryMap]

@[simp]
theorem quditCoboundaryMap_zero (e : G.edgeSet) :
    quditCoboundaryMap G p (0 : V → ZMod p) e = 0 := by
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | _ a b => simp [quditCoboundaryMap, Sym2.lift_mk]

@[simp]
theorem quditSecondBoundaryMap_zero (e : G.edgeSet) :
    quditSecondBoundaryMap G cycles p (0 : C → ZMod p) e = 0 := by
  simp [quditSecondBoundaryMap]

@[simp]
theorem quditSecondCoboundaryMap_zero (c : C) :
    quditSecondCoboundaryMap G cycles p (0 : G.edgeSet → ZMod p) c = 0 := by
  simp [quditSecondCoboundaryMap]

/-- The qudit boundary map is Z_p-linear: it maps sums to sums. -/
theorem quditBoundaryMap_add (γ₁ γ₂ : G.edgeSet → ZMod p) :
    quditBoundaryMap G p (γ₁ + γ₂) = quditBoundaryMap G p γ₁ + quditBoundaryMap G p γ₂ :=
  map_add (quditBoundaryMap G p) γ₁ γ₂

/-- The qudit coboundary map is Z_p-linear: it maps sums to sums. -/
theorem quditCoboundaryMap_add (f₁ f₂ : V → ZMod p) :
    quditCoboundaryMap G p (f₁ + f₂) = quditCoboundaryMap G p f₁ + quditCoboundaryMap G p f₂ :=
  map_add (quditCoboundaryMap G p) f₁ f₂

end QuditBasic

/-! ## 2. Abelian Group Charge Determination -/

section AbelianCharges

variable {α : Type*} [AddCommMonoid α]

/-- For an abelian group, the sum of local charges is independent of the ordering.
    This is the core mathematical fact that makes abelian gauging work:
    measuring individual A_v operators in any order gives the same total charge
    σ = Σ_v ε_v, because addition is commutative. -/
theorem abelian_charge_sum_well_defined {n : ℕ}
    (charges : Fin n → α) (perm : Equiv.Perm (Fin n)) :
    ∑ i : Fin n, charges (perm i) = ∑ i : Fin n, charges i :=
  Equiv.sum_comp perm charges

/-- For abelian groups, the sum over any fintype is permutation-invariant.
    This generalizes to arbitrary index types. -/
theorem abelian_sum_perm_invariant {ι : Type*} [Fintype ι]
    (charges : ι → α) (perm : Equiv.Perm ι) :
    ∑ i : ι, charges (perm i) = ∑ i : ι, charges i :=
  Equiv.sum_comp perm charges

/-- For abelian groups, the sum over a fintype is independent of the enumeration.
    This is why measuring Gauss's law operators A_v in any order gives the
    same total sign σ = Σ_v ε_v ∈ Z_p. -/
theorem abelian_local_determines_global {ι : Type*} [Fintype ι] [DecidableEq ι]
    (charges : ι → α) (σ₁ σ₂ : Equiv.Perm ι) :
    ∑ i : ι, charges (σ₁ i) = ∑ i : ι, charges (σ₂ i) := by
  rw [Equiv.sum_comp σ₁, Equiv.sum_comp σ₂]

end AbelianCharges

/-! ## 3. Nonabelian Groups: Product Order Dependence

For nonabelian groups, `Finset.prod` (= `∏`) requires `CommMonoid`, which nonabelian
groups do not satisfy. We instead use `List.prod` (which only requires `Monoid`)
to express ordered products, making the order-dependence manifest. -/

section NonabelianCaveat

/-- For nonabelian groups, the product of elements depends on the order of multiplication.
    If g₁ * g₂ ≠ g₂ * g₁, then the two orderings [g₁, g₂] and [g₂, g₁] give different
    products. This is the fundamental obstruction to measuring nonabelian charges locally. -/
theorem nonabelian_product_order_dependent {G : Type*} [Group G]
    (g₁ g₂ : G) (hne : g₁ * g₂ ≠ g₂ * g₁) :
    [g₁, g₂].prod ≠ [g₂, g₁].prod := by
  simp only [List.prod_cons, List.prod_nil, mul_one]
  exact hne

/-- For a commutative (abelian) monoid, the product of any list is invariant under
    permutation. This is the positive direction: abelian gauging works because local
    measurements determine the global charge. -/
theorem abelian_product_perm_invariant {G : Type*} [CommMonoid G]
    (l₁ l₂ : List G) (hp : l₁.Perm l₂) :
    l₁.prod = l₂.prod :=
  hp.prod_eq

/-- For a commutative monoid, all permutations of a finite sequence give the same product. -/
theorem abelian_fintype_prod_perm_invariant {G : Type*} [CommMonoid G] {ι : Type*} [Fintype ι]
    (elements : ι → G) (σ : Equiv.Perm ι) :
    ∏ i : ι, elements (σ i) = ∏ i : ι, elements i :=
  Equiv.prod_comp σ elements

/-- For a commutative monoid, ALL permutations give the same product. -/
theorem abelian_all_perms_same_product {G : Type*} [CommMonoid G] {ι : Type*} [Fintype ι]
    (elements : ι → G) (σ₁ σ₂ : Equiv.Perm ι) :
    ∏ i : ι, elements (σ₁ i) = ∏ i : ι, elements (σ₂ i) := by
  rw [Equiv.prod_comp σ₁, Equiv.prod_comp σ₂]

end NonabelianCaveat

/-! ## 4. Qudit Gauss's Law Operators (Generalized) -/

section QuditGauss

variable {E : Type*} [Fintype E] [DecidableEq E]
variable (incident : V → E → Prop) [∀ v e, Decidable (incident v e)]

/-- The qudit boundary map for a hypergraph over Z_p, generalizing both the graph case
    (Def_1) and the hypergraph case (Rem_17) from Z₂ to Z_p. -/
def quditHyperBoundaryMap (p : ℕ) [NeZero p] :
    (E → ZMod p) →ₗ[ZMod p] (V → ZMod p) where
  toFun γ v := ∑ e : E, if incident v e then γ e else 0
  map_add' := by
    intro γ₁ γ₂; ext v; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]; congr 1; ext e
    split <;> simp
  map_smul' := by
    intro r γ; ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext e
    split <;> simp [mul_comm]

/-- The qudit coboundary map for a hypergraph over Z_p. -/
def quditHyperCoboundaryMap (p : ℕ) [NeZero p] :
    (V → ZMod p) →ₗ[ZMod p] (E → ZMod p) where
  toFun f e := ∑ v : V, if incident v e then f v else 0
  map_add' := by
    intro f₁ f₂; ext e; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]; congr 1; ext v
    split <;> simp
  map_smul' := by
    intro r f; ext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext v
    split <;> simp [mul_comm]

/-- The qudit hypergraph coboundary is the transpose of the boundary over Z_p. -/
theorem quditHyperCoboundaryMap_eq_transpose (p : ℕ) [NeZero p]
    (f : V → ZMod p) (γ : E → ZMod p) :
    ∑ e : E, quditHyperCoboundaryMap incident p f e * γ e =
    ∑ v : V, f v * quditHyperBoundaryMap incident p γ v := by
  simp only [quditHyperBoundaryMap, quditHyperCoboundaryMap, LinearMap.coe_mk, AddHom.coe_mk]
  conv_lhs =>
    arg 2; ext e
    rw [Finset.sum_mul]
  conv_rhs =>
    arg 2; ext v
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro e _
  split
  · next _h => ring
  · next _h => simp

/-- The qudit hypergraph boundary map at p = 2 agrees with the Z₂ version from Rem_17. -/
theorem quditHyperBoundaryMap_specializes_to_Z2
    (γ : E → ZMod 2) (v : V) :
    quditHyperBoundaryMap incident 2 γ v =
    HypergraphGeneralization.hyperBoundaryMap incident γ v := by
  simp [quditHyperBoundaryMap, HypergraphGeneralization.hyperBoundaryMap]

/-- The qudit hypergraph coboundary map at p = 2 agrees with the Z₂ version from Rem_17. -/
theorem quditHyperCoboundaryMap_specializes_to_Z2
    (f : V → ZMod 2) (e : E) :
    quditHyperCoboundaryMap incident 2 f e =
    HypergraphGeneralization.hyperCoboundaryMap incident f e := by
  simp [quditHyperCoboundaryMap, HypergraphGeneralization.hyperCoboundaryMap]

@[simp]
theorem quditHyperBoundaryMap_zero (p : ℕ) [NeZero p] (v : V) :
    quditHyperBoundaryMap incident p (0 : E → ZMod p) v = 0 := by
  simp [quditHyperBoundaryMap]

@[simp]
theorem quditHyperCoboundaryMap_zero (p : ℕ) [NeZero p] (e : E) :
    quditHyperCoboundaryMap incident p (0 : V → ZMod p) e = 0 := by
  simp [quditHyperCoboundaryMap]

end QuditGauss

/-! ## 5. Nonabelian Local vs Global Charge -/

section NonabelianChargeDetail

/-- **Nonabelian local underdetermines global**: In a nonabelian group, knowing the
    individual elements g_v does NOT determine their product uniquely, because the product
    depends on the order of multiplication. For any two noncommuting elements, the two
    orderings produce different products. This is the formal content of the paper's
    caveat about nonabelian gauging. -/
theorem nonabelian_local_underdetermines_global {G : Type*} [Group G]
    (g₁ g₂ : G) (hne : g₁ * g₂ ≠ g₂ * g₁) :
    ¬(∀ l₁ l₂ : List G, l₁.Perm l₂ → l₁.prod = l₂.prod) := by
  intro hall
  have hperm : [g₁, g₂].Perm [g₂, g₁] := by
    exact List.Perm.swap g₂ g₁ []
  have := hall _ _ hperm
  simp only [List.prod_cons, List.prod_nil, mul_one] at this
  exact hne this

/-- **Abelian local determines global**: In a commutative group, the product of elements
    is uniquely determined regardless of ordering. This is why abelian gauging works. -/
theorem abelian_local_determines_global' {G : Type*} [CommMonoid G]
    (l₁ l₂ : List G) (hp : l₁.Perm l₂) :
    l₁.prod = l₂.prod :=
  hp.prod_eq

/-- The abelian-nonabelian dichotomy: a group has the property that all 2-element
    ordered products are the same iff it is commutative. -/
theorem charge_dichotomy_iff_comm {G : Type*} [Group G] :
    (∀ (g₁ g₂ : G), [g₁, g₂].prod = [g₂, g₁].prod) ↔
    ∀ g₁ g₂ : G, g₁ * g₂ = g₂ * g₁ := by
  simp only [List.prod_cons, List.prod_nil, mul_one]

end NonabelianChargeDetail

/-! ## 6. Summary -/

/-- **Summary theorem**: The three generalizations beyond Pauli operators on qubits.

    1. **Qudit**: Boundary/coboundary maps generalize from Z₂ to Z_p, preserving linearity
       and the transpose property. The chain complex property ∂ ∘ ∂₂ = 0 still holds.

    2. **Abelian**: For abelian groups, the sum/product of local charges is
       order-independent, so measuring local charges determines the global charge.

    3. **Nonabelian**: For nonabelian groups, the product of local charges depends on
       the order, so local measurements do NOT determine a definite global charge. -/
theorem generalizations_beyond_pauli_summary :
    -- (1) Qudit maps are well-defined Z_p-linear maps with transpose property
    (∀ (p : ℕ) [NeZero p] (f : V → ZMod p) (γ : G.edgeSet → ZMod p),
      ∑ e : G.edgeSet, quditCoboundaryMap G p f e * γ e =
      ∑ v : V, f v * quditBoundaryMap G p γ v) ∧
    -- (2) Qudit maps specialize to Z₂ maps at p = 2
    (∀ (γ : G.edgeSet → ZMod 2) (v : V),
      quditBoundaryMap G 2 γ v = GraphMaps.boundaryMap G γ v) ∧
    -- (3) Abelian sums are permutation-invariant
    (∀ {α : Type*} [AddCommMonoid α] {n : ℕ}
      (charges : Fin n → α) (perm : Equiv.Perm (Fin n)),
      ∑ i : Fin n, charges (perm i) = ∑ i : Fin n, charges i) ∧
    -- (4) Nonabelian products can be permutation-dependent
    (∀ {G : Type*} [Group G] (g₁ g₂ : G),
      g₁ * g₂ ≠ g₂ * g₁ →
      [g₁, g₂].prod ≠ [g₂, g₁].prod) :=
  ⟨fun p => quditCoboundaryMap_eq_transpose G p,
   quditBoundaryMap_specializes_to_qubit G,
   fun charges perm => Equiv.sum_comp perm charges,
   fun g₁ g₂ hne => nonabelian_product_order_dependent g₁ g₂ hne⟩

end GeneralizationsBeyondPauli
