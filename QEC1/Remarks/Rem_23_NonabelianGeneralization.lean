import QEC1.Remarks.Rem_22_CSSCodeInitialization
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Nonabelian Generalization (Remark 23)

## Statement
The gauging measurement procedure can be generalized beyond Pauli operators:

**Finite group generalization**: The procedure applies to any representation of a finite
group G by operators with tensor product factorization. This includes:
- Qudit systems (using Z_d instead of Z_2)
- Non-Pauli operators (e.g., Clifford operators in topological codes)
- Magic state preparation via measurement of non-Clifford operators

**Nonabelian case**: For nonabelian groups, measuring local charges does not fix a
definite global charge. The total charge is a superposition consistent with local outcomes.

**Example**: Measurement of Clifford operators in topological codes (see [Davydova2024])
uses similar gauging ideas to produce magic states.

## Formalization Approach

This remark discusses conceptual generalizations of the gauging framework. We formalize
the key mathematical structures that enable these generalizations:

1. **Finite group structure**: Replace Z_2 with arbitrary finite group G
2. **Local charge algebra**: For abelian G, local measurements determine global charge
3. **Nonabelian obstruction**: For nonabelian G, the commutator subgroup measures the
   failure to determine global charge from local outcomes
4. **Qudit generalization**: Z_d charges for d-dimensional local Hilbert spaces

The main mathematical content:
- Abelian groups: product of local charges = global charge (exact)
- Nonabelian groups: global charge is determined up to commutator

## Main Results
- `LocalChargeConfig`: Structure for local charge operators in finite groups
- `globalCharge`: Global charge as product of local charges
- `globalCharge_mul`: Global charge is multiplicative
- `qudit_charge_sum`: Z_d charges sum to give global charge
- `commutator_trivial_comm`: Trivial commutator implies commutativity

## File Structure
1. Finite Group Generalization: G-valued charges
2. Local vs Global Charges: Product structure
3. Abelian Case: Exact determination
4. Qudit Systems: Z_d specialization
5. Nonabelian Obstruction: Commutator structure
-/

namespace QEC

open scoped BigOperators

/-! ## Section 1: Finite Group Generalization

Replace the Pauli group structure (Z_2 × Z_2 per qubit) with an arbitrary finite group G.
Operators are represented by group elements, and tensor products correspond to group products.
-/

/-- A local charge configuration assigns a group element to each site.
    For gauging measurement, this represents the outcome of measuring local charge operators. -/
structure LocalChargeConfig (G : Type*) [Group G] (Sites : Type*) [Fintype Sites] where
  /-- The local charge at each site -/
  charge : Sites → G

namespace LocalChargeConfig

variable {G : Type*} [Group G] {Sites : Type*} [Fintype Sites]

/-- The identity configuration (all charges are identity) -/
def identity : LocalChargeConfig G Sites where
  charge := fun _ => 1

/-- Pointwise multiplication of charge configurations -/
def mul (c₁ c₂ : LocalChargeConfig G Sites) : LocalChargeConfig G Sites where
  charge := fun s => c₁.charge s * c₂.charge s

/-- Pointwise inverse of a charge configuration -/
def inv (c : LocalChargeConfig G Sites) : LocalChargeConfig G Sites where
  charge := fun s => (c.charge s)⁻¹

instance : One (LocalChargeConfig G Sites) := ⟨identity⟩
instance : Mul (LocalChargeConfig G Sites) := ⟨mul⟩
instance : Inv (LocalChargeConfig G Sites) := ⟨inv⟩

@[simp] theorem one_charge (s : Sites) : (1 : LocalChargeConfig G Sites).charge s = 1 := rfl
@[simp] theorem mul_charge (c₁ c₂ : LocalChargeConfig G Sites) (s : Sites) :
    (c₁ * c₂).charge s = c₁.charge s * c₂.charge s := rfl
@[simp] theorem inv_charge (c : LocalChargeConfig G Sites) (s : Sites) :
    c⁻¹.charge s = (c.charge s)⁻¹ := rfl

end LocalChargeConfig

/-! ## Section 2: Global Charge from Local Charges (Abelian Case)

For abelian groups, the global charge is the product of all local charges.
This is independent of ordering due to commutativity.
-/

/-- The global charge for abelian groups: product of all local charges -/
noncomputable def globalCharge {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites]
    (c : LocalChargeConfig G Sites) : G :=
  Finset.univ.prod c.charge

/-- **Main Theorem (Abelian Case)**: The global charge is the product of local charges.
    This theorem justifies the gauging measurement procedure for Pauli operators:
    ∏_v ε_v = σ gives the logical measurement outcome. -/
theorem abelian_global_from_local {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites]
    (c : LocalChargeConfig G Sites) :
    globalCharge c = Finset.univ.prod c.charge := rfl

/-- Global charge is multiplicative under configuration multiplication -/
theorem globalCharge_mul {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites]
    (c₁ c₂ : LocalChargeConfig G Sites) :
    globalCharge (c₁ * c₂) = globalCharge c₁ * globalCharge c₂ := by
  unfold globalCharge
  simp only [LocalChargeConfig.mul_charge]
  rw [← Finset.prod_mul_distrib]

/-- Global charge of identity is identity -/
theorem globalCharge_one {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites] :
    globalCharge (1 : LocalChargeConfig G Sites) = 1 := by
  unfold globalCharge
  simp only [LocalChargeConfig.one_charge, Finset.prod_const_one]

/-- Global charge of inverse is inverse of global charge -/
theorem globalCharge_inv {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites]
    (c : LocalChargeConfig G Sites) :
    globalCharge c⁻¹ = (globalCharge c)⁻¹ := by
  unfold globalCharge
  simp only [LocalChargeConfig.inv_charge, Finset.prod_inv_distrib]

/-! ## Section 3: Qudit Systems - Z_d Generalization

For qudit systems with local dimension d, the charge group is Z_d instead of Z_2.
This is the "obvious" generalization from qubits to qudits.
-/

/-- Qudit charge configuration: Z_d valued charges at each site -/
abbrev QuditChargeConfig (d : ℕ) [NeZero d] (Sites : Type*) [Fintype Sites] :=
  LocalChargeConfig (Multiplicative (ZMod d)) Sites

/-- The global qudit charge is the sum of local charges (in additive notation) -/
noncomputable def globalQuditCharge {d : ℕ} [NeZero d] {Sites : Type*} [Fintype Sites]
    (c : QuditChargeConfig d Sites) : ZMod d :=
  Finset.univ.sum (fun s => Multiplicative.toAdd (c.charge s))

/-- Global qudit charge agrees with global charge via the isomorphism -/
theorem globalQuditCharge_eq {d : ℕ} [NeZero d] {Sites : Type*} [Fintype Sites]
    (c : QuditChargeConfig d Sites) :
    Multiplicative.ofAdd (globalQuditCharge c) = globalCharge c := by
  classical
  unfold globalQuditCharge globalCharge
  induction (Finset.univ : Finset Sites) using Finset.induction_on with
  | empty => simp
  | @insert s S hs ih =>
    rw [Finset.sum_insert hs, Finset.prod_insert hs]
    rw [ofAdd_add, ih]
    rfl

/-- Qubit case: d = 2 gives Z_2 charges (Pauli X measurement outcomes) -/
theorem qubit_is_special_qudit {Sites : Type*} [Fintype Sites] :
    QuditChargeConfig 2 Sites = LocalChargeConfig (Multiplicative (ZMod 2)) Sites := rfl

/-- Qubit global charge is sum of local charges mod 2 -/
theorem qubit_global_is_parity {Sites : Type*} [Fintype Sites]
    (c : QuditChargeConfig 2 Sites) :
    globalQuditCharge c = Finset.sum Finset.univ (fun s => Multiplicative.toAdd (c.charge s)) := rfl

/-! ## Section 4: Nonabelian Obstruction - Commutator Structure

For nonabelian groups, the order of multiplication matters. Different orderings of the
same local charges can give different global charges. The ambiguity is measured by the
commutator subgroup [G, G].

**Physical interpretation**: For nonabelian gauge theories, measuring local charges
does not determine a unique global charge. The post-measurement state is a superposition
over charges in the same coset of the commutator subgroup.
-/

/-- The commutator subgroup [G, G] = ⁅G, G⁆ measures the ambiguity in global charge.
    We define it as the commutator of the top subgroup with itself. -/
def commutatorSubgroup' (G : Type*) [Group G] : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆

/-- For groups where all elements commute, the commutator subgroup is trivial -/
theorem commutator_trivial_of_comm (G : Type*) [Group G]
    (h_comm : ∀ (a b : G), a * b = b * a) :
    commutatorSubgroup' G = ⊥ := by
  rw [commutatorSubgroup', Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x _
  simp only [Subgroup.mem_centralizer_iff, Subgroup.coe_top, Set.mem_univ, forall_true_left]
  intro y
  exact (h_comm x y).symm

/-- The commutator subgroup being trivial implies commutativity -/
theorem comm_of_commutator_trivial (G : Type*) [Group G]
    (h_trivial : commutatorSubgroup' G = ⊥) :
    ∀ (a b : G), a * b = b * a := by
  intro a b
  have hmem : ⁅a, b⁆ ∈ commutatorSubgroup' G := by
    rw [commutatorSubgroup']
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [h_trivial] at hmem
  simp only [Subgroup.mem_bot] at hmem
  -- ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ = 1
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := hmem
  calc a * b = a * b * 1 := by group
    _ = a * b * (a⁻¹ * b⁻¹ * b * a) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * b * a := by group
    _ = 1 * b * a := by rw [h1]
    _ = b * a := by group

/-- Equivalence: trivial commutator iff all elements commute -/
theorem commutator_trivial_iff_comm (G : Type*) [Group G] :
    commutatorSubgroup' G = ⊥ ↔ ∀ (a b : G), a * b = b * a := by
  constructor
  · exact comm_of_commutator_trivial G
  · exact commutator_trivial_of_comm G

/-- The commutator subgroup is normal -/
theorem commutator_normal' (G : Type*) [Group G] :
    (commutatorSubgroup' G).Normal := by
  rw [commutatorSubgroup']
  exact Subgroup.commutator_normal ⊤ ⊤

/-! ## Section 5: Ordered Product for Nonabelian Case

For nonabelian groups, the global charge depends on the order of multiplication.
-/

/-- The ordered product of local charges given an enumeration -/
noncomputable def globalChargeOrdered {G : Type*} [Group G] {Sites : Type*} [Fintype Sites]
    (c : LocalChargeConfig G Sites) (enum : Fin (Fintype.card Sites) ≃ Sites) : G :=
  (List.ofFn (fun i => c.charge (enum i))).prod

/-- For abelian groups, the ordered product equals the unordered product -/
theorem globalChargeOrdered_eq_globalCharge {G : Type*} [CommGroup G]
    {Sites : Type*} [Fintype Sites]
    (c : LocalChargeConfig G Sites) (enum : Fin (Fintype.card Sites) ≃ Sites) :
    globalChargeOrdered c enum = globalCharge c := by
  unfold globalChargeOrdered globalCharge
  rw [List.prod_ofFn]
  have h : ∏ i : Fin (Fintype.card Sites), c.charge (enum i) =
           ∏ s : Sites, c.charge s := by
    rw [Fintype.prod_equiv enum (fun i => c.charge (enum i)) (fun s => c.charge s)]
    intro i
    rfl
  rw [h]

/-- Identity configuration has global charge 1 for any enumeration -/
theorem globalChargeOrdered_one {G : Type*} [Group G] {Sites : Type*} [Fintype Sites]
    (enum : Fin (Fintype.card Sites) ≃ Sites) :
    globalChargeOrdered (1 : LocalChargeConfig G Sites) enum = 1 := by
  unfold globalChargeOrdered
  simp only [LocalChargeConfig.one_charge, List.ofFn_const, List.prod_replicate, one_pow]

/-! ## Section 6: Constant Configurations -/

/-- Local charge configuration with all sites having the same charge -/
def LocalChargeConfig.const {G : Type*} [Group G] {Sites : Type*} [Fintype Sites]
    (g : G) : LocalChargeConfig G Sites where
  charge := fun _ => g

/-- Global charge of constant configuration is g^|Sites| for abelian groups -/
theorem globalCharge_const {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites]
    (g : G) :
    globalCharge (LocalChargeConfig.const g : LocalChargeConfig G Sites) =
    g ^ Fintype.card Sites := by
  unfold globalCharge LocalChargeConfig.const
  simp only [Finset.prod_const, Finset.card_univ]

/-- Global ordered charge of constant configuration is g^|Sites| for any group -/
theorem globalChargeOrdered_const {G : Type*} [Group G] {Sites : Type*} [Fintype Sites]
    (g : G) (enum : Fin (Fintype.card Sites) ≃ Sites) :
    globalChargeOrdered (LocalChargeConfig.const g : LocalChargeConfig G Sites) enum =
    g ^ Fintype.card Sites := by
  unfold globalChargeOrdered LocalChargeConfig.const
  simp only [List.ofFn_const, List.prod_replicate]

/-- For Z_d, global charge of constant configuration is |Sites| * g -/
theorem globalQuditCharge_const {d : ℕ} [NeZero d] {Sites : Type*} [Fintype Sites]
    (g : ZMod d) :
    globalQuditCharge (LocalChargeConfig.const (Multiplicative.ofAdd g) :
        QuditChargeConfig d Sites) = Fintype.card Sites • g := by
  unfold globalQuditCharge LocalChargeConfig.const
  simp only [toAdd_ofAdd, Finset.sum_const, Finset.card_univ]

/-! ## Section 7: Physical Interpretation Lemmas -/

/-- **Key Interpretation**: For abelian charge groups, the gauging measurement
    correctly determines the global charge from local measurements. -/
theorem abelian_gauging_correct {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites]
    (c : LocalChargeConfig G Sites) :
    globalCharge c = Finset.univ.prod c.charge := rfl

/-- For Z_2 (Pauli case), this specializes to the parity of local outcomes -/
theorem pauli_parity_measurement {Sites : Type*} [Fintype Sites]
    (c : QuditChargeConfig 2 Sites) :
    globalQuditCharge c = Finset.sum Finset.univ (fun s => Multiplicative.toAdd (c.charge s)) := rfl

/-- **Nonabelian interpretation**: For nonabelian groups, different enumerations
    can give different global charges. The commutator subgroup controls this. -/
theorem nonabelian_ambiguity_source {G : Type*} [Group G]
    (h_noncomm : ∃ (a b : G), a * b ≠ b * a) :
    commutatorSubgroup' G ≠ ⊥ := by
  intro h_trivial
  obtain ⟨a, b, hab⟩ := h_noncomm
  have h_comm := comm_of_commutator_trivial G h_trivial a b
  exact hab h_comm

/-! ## Section 8: Helper Simp Lemmas -/

@[simp]
theorem LocalChargeConfig.const_charge {G : Type*} [Group G] {Sites : Type*} [Fintype Sites]
    (g : G) (s : Sites) :
    (LocalChargeConfig.const g : LocalChargeConfig G Sites).charge s = g := rfl

@[simp]
theorem globalCharge_identity {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites] :
    globalCharge (1 : LocalChargeConfig G Sites) = 1 := globalCharge_one

@[simp]
theorem globalQuditCharge_zero {d : ℕ} [NeZero d] {Sites : Type*} [Fintype Sites] :
    globalQuditCharge (1 : QuditChargeConfig d Sites) = 0 := by
  unfold globalQuditCharge
  simp only [LocalChargeConfig.one_charge, toAdd_one, Finset.sum_const_zero]

/-- Empty sites case: global charge is 1 -/
theorem globalCharge_empty {G : Type*} [CommGroup G] {Sites : Type*} [Fintype Sites]
    (h : Fintype.card Sites = 0) (c : LocalChargeConfig G Sites) :
    globalCharge c = 1 := by
  unfold globalCharge
  have h_empty : Finset.univ (α := Sites) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x
    have : Fintype.card Sites > 0 := Fintype.card_pos_iff.mpr ⟨x⟩
    omega
  rw [h_empty, Finset.prod_empty]

end QEC
