import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Algebra.Group.Indicator
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finset.SymmDiff

-- Disable linters about unused section variables and type-class hypotheses
-- These warnings arise from section variables that apply to multiple theorems but aren't needed by all
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Rem_3: Binary Vector Notation

## Statement
Throughout this work, we abuse notation by identifying a subset of vertices, edges, or cycles
with its characteristic binary vector over $\mathbb{Z}_2 = \mathbb{F}_2$. For a set $S$ of
vertices/edges/cycles, the corresponding binary vector has a 1 in position $i$ if and only if
element $i$ belongs to $S$. Addition of binary vectors corresponds to symmetric difference of sets.
This identification allows us to use linear algebra over $\mathbb{Z}_2$ to reason about
graph-theoretic properties.

## Main Definitions
- `BinaryVector` : The type of binary vectors over a finite index set, i.e., functions `α → ZMod 2`
- `characteristicVector` : Maps a subset `S` to its characteristic binary vector
- `fromBinaryVector` : Maps a binary vector back to the corresponding subset

## Key Properties
- `characteristicVector_mem_iff` : Position i is 1 iff element i belongs to S
- `characteristicVector_add` : Addition corresponds to symmetric difference
- `characteristicVector_injective` : The identification is injective (subsets uniquely determine vectors)
- `characteristicVector_bijective` : The identification is a bijection

## Corollaries
- This identification makes `Finset α` into a `ZMod 2`-vector space
- Linear algebra over `ZMod 2` can be applied to reason about set operations
-/

open scoped symmDiff

/-! ## Binary Vectors over ZMod 2 -/

/-- A binary vector over an index set α is a function to ZMod 2.
    This is the type of characteristic vectors. -/
abbrev BinaryVector (α : Type*) := α → ZMod 2

namespace BinaryVector

variable {α : Type*}

/-- The zero vector (all zeros) -/
def zero : BinaryVector α := fun _ => 0

/-- The all-ones vector -/
def ones : BinaryVector α := fun _ => 1

/-- Addition of binary vectors (componentwise in ZMod 2) -/
def add (v w : BinaryVector α) : BinaryVector α := fun i => v i + w i

instance : Zero (BinaryVector α) := ⟨zero⟩
instance : Add (BinaryVector α) := ⟨add⟩

@[simp] lemma zero_apply (i : α) : (0 : BinaryVector α) i = 0 := rfl
@[simp] lemma add_apply (v w : BinaryVector α) (i : α) : (v + w) i = v i + w i := rfl

/-- Binary vectors form an additive group (every element is its own inverse in ZMod 2) -/
instance : AddCommGroup (BinaryVector α) := Pi.addCommGroup

/-- Binary vectors form a ZMod 2 module (i.e., a vector space over F_2) -/
instance : Module (ZMod 2) (BinaryVector α) := Pi.module α (fun _ => ZMod 2) (ZMod 2)

end BinaryVector

/-! ## Characteristic Vector of a Set -/

section CharacteristicVector

variable {α : Type*} [DecidableEq α]

/-- The characteristic vector of a finset S: position i has value 1 iff i ∈ S. -/
def characteristicVector (S : Finset α) : BinaryVector α :=
  fun i => if i ∈ S then 1 else 0

/-- Alternative definition using Set.indicator -/
noncomputable def characteristicVector' (S : Finset α) : BinaryVector α :=
  Set.indicator (↑S) (fun _ => (1 : ZMod 2))

@[simp] lemma characteristicVector_apply_mem (S : Finset α) (i : α) (h : i ∈ S) :
    characteristicVector S i = 1 := by simp [characteristicVector, h]

@[simp] lemma characteristicVector_apply_not_mem (S : Finset α) (i : α) (h : i ∉ S) :
    characteristicVector S i = 0 := by simp [characteristicVector, h]

/-- Key characterization: position i is 1 iff element i belongs to S -/
theorem characteristicVector_mem_iff (S : Finset α) (i : α) :
    characteristicVector S i = 1 ↔ i ∈ S := by
  constructor
  · intro h
    simp only [characteristicVector] at h
    split_ifs at h with hm
    · exact hm
    · simp at h
  · intro h
    simp [h]

theorem characteristicVector_not_mem_iff (S : Finset α) (i : α) :
    characteristicVector S i = 0 ↔ i ∉ S := by
  constructor
  · intro h
    simp only [characteristicVector] at h
    split_ifs at h with hm
    · simp at h
    · exact hm
  · intro h
    simp [h]

/-- The characteristic vector of the empty set is zero -/
@[simp] lemma characteristicVector_empty :
    characteristicVector (∅ : Finset α) = 0 := by
  ext i
  simp [characteristicVector]

/-- The characteristic vector of the bottom element (used for symmDiff_self) -/
@[simp] lemma characteristicVector_bot :
    characteristicVector (⊥ : Finset α) = 0 := characteristicVector_empty

/-- The characteristic vector of a singleton -/
@[simp] lemma characteristicVector_singleton (a : α) :
    characteristicVector ({a} : Finset α) = fun i => if i = a then 1 else 0 := by
  ext i
  simp only [characteristicVector, Finset.mem_singleton]

end CharacteristicVector

/-! ## Symmetric Difference and Vector Addition -/

section SymmDiffAddition

variable {α : Type*} [DecidableEq α]

open scoped symmDiff

/-- Helper: 1 + 1 = 0 in ZMod 2 -/
private lemma one_add_one_ZMod2 : (1 : ZMod 2) + 1 = 0 := by decide

/-- Key theorem: Addition of characteristic vectors corresponds to symmetric difference.
    This is the fundamental property that allows linear algebra over Z_2 to encode set operations. -/
theorem characteristicVector_add (S T : Finset α) :
    characteristicVector S + characteristicVector T = characteristicVector (S ∆ T) := by
  ext i
  simp only [Pi.add_apply, characteristicVector, Finset.mem_symmDiff]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
  · simp [hS, hT, one_add_one_ZMod2]
  · simp [hS, hT]
  · simp [hS, hT]
  · simp [hS, hT]

/-- Symmetric difference is encoded as addition -/
theorem characteristicVector_symmDiff (S T : Finset α) :
    characteristicVector (S ∆ T) = characteristicVector S + characteristicVector T :=
  (characteristicVector_add S T).symm

/-- Self-symmetric difference is empty (S Δ S = ∅) -/
@[simp] lemma characteristicVector_self_add (S : Finset α) :
    characteristicVector S + characteristicVector S = 0 := by
  rw [characteristicVector_add, symmDiff_self, characteristicVector_bot]

/-- In ZMod 2, every element is its own additive inverse -/
theorem characteristicVector_neg_eq_self (S : Finset α) :
    -characteristicVector S = characteristicVector S := by
  ext i
  simp only [Pi.neg_apply, characteristicVector]
  split_ifs <;> decide

end SymmDiffAddition

/-! ## Inverse Map: From Binary Vector to Finset -/

section FromBinaryVector

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Convert a binary vector back to a finset (the support of the vector) -/
def fromBinaryVector (v : BinaryVector α) : Finset α :=
  Finset.univ.filter (fun i => v i = 1)

@[simp] lemma mem_fromBinaryVector (v : BinaryVector α) (i : α) :
    i ∈ fromBinaryVector v ↔ v i = 1 := by
  simp [fromBinaryVector]

/-- Round-trip: characteristic vector then back to finset gives the original finset -/
@[simp] theorem fromBinaryVector_characteristicVector (S : Finset α) :
    fromBinaryVector (characteristicVector S) = S := by
  ext i
  simp [fromBinaryVector, characteristicVector_mem_iff]

/-- In ZMod 2, every element is either 0 or 1 -/
private lemma ZMod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Round-trip: finset to vector then back gives the original vector
    (for vectors that only take values 0 and 1, which is automatic in ZMod 2) -/
@[simp] theorem characteristicVector_fromBinaryVector (v : BinaryVector α) :
    characteristicVector (fromBinaryVector v) = v := by
  ext i
  simp only [characteristicVector, fromBinaryVector, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases ZMod2_eq_zero_or_one (v i) with h | h <;> simp [h]

/-- The characteristic vector map is injective -/
theorem characteristicVector_injective :
    Function.Injective (characteristicVector (α := α)) := by
  intro S T heq
  ext i
  rw [← characteristicVector_mem_iff S i, ← characteristicVector_mem_iff T i, heq]

/-- The characteristic vector map is surjective -/
theorem characteristicVector_surjective :
    Function.Surjective (characteristicVector (α := α)) := by
  intro v
  use fromBinaryVector v
  simp

/-- The characteristic vector map is a bijection -/
theorem characteristicVector_bijective :
    Function.Bijective (characteristicVector (α := α)) :=
  ⟨characteristicVector_injective, characteristicVector_surjective⟩

/-- The characteristic vector map as an equivalence -/
def characteristicVectorEquiv : Finset α ≃ BinaryVector α where
  toFun := characteristicVector
  invFun := fromBinaryVector
  left_inv := fromBinaryVector_characteristicVector
  right_inv := characteristicVector_fromBinaryVector

end FromBinaryVector

/-! ## Algebraic Structure: Finsets as a Vector Space over ZMod 2 -/

section VectorSpaceStructure

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Addition on Finsets via symmetric difference -/
instance finsetAdd : Add (Finset α) := ⟨fun S T => S ∆ T⟩

/-- Zero element is the empty set -/
instance finsetZero : Zero (Finset α) := ⟨∅⟩

/-- Negation is identity (every element is its own inverse) -/
instance finsetNeg : Neg (Finset α) := ⟨id⟩

/-- Finsets form an additive commutative group with symmetric difference as addition -/
instance finsetAddCommGroup : AddCommGroup (Finset α) where
  add_assoc := symmDiff_assoc
  zero_add := bot_symmDiff
  add_zero := symmDiff_bot
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel S := symmDiff_self S
  add_comm := symmDiff_comm

/-- Scalar multiplication by ZMod 2: 0 * S = ∅, 1 * S = S -/
instance finsetSMul : SMul (ZMod 2) (Finset α) :=
  ⟨fun c S => if c = 0 then ∅ else S⟩

@[simp] lemma zero_smul_finset (S : Finset α) : (0 : ZMod 2) • S = ∅ := rfl

@[simp] lemma one_smul_finset (S : Finset α) : (1 : ZMod 2) • S = S := rfl

private lemma ZMod2_cases (P : ZMod 2 → Prop) (h0 : P 0) (h1 : P 1) : ∀ x, P x := by
  intro x
  fin_cases x <;> assumption

private lemma ZMod2_add_eq (a b : ZMod 2) :
    a + b = if a = 0 then b else if b = 0 then a else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

private lemma ZMod2_mul_eq (a b : ZMod 2) :
    a * b = if a = 0 then 0 else if b = 0 then 0 else 1 := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Helper lemma for mul_smul -/
private lemma finset_mul_smul_aux (a b : ZMod 2) (S : Finset α) :
    (if a * b = 0 then ∅ else S) = (if a = 0 then ∅ else if b = 0 then ∅ else S) := by
  rcases ZMod2_eq_zero_or_one a with ha | ha <;> rcases ZMod2_eq_zero_or_one b with hb | hb <;>
    simp [ha, hb]

/-- Helper lemma for smul_add -/
private lemma finset_smul_add_aux (a : ZMod 2) (S T : Finset α) :
    (if a = 0 then ∅ else S ∆ T) = (if a = 0 then ∅ else S) ∆ (if a = 0 then ∅ else T) := by
  rcases ZMod2_eq_zero_or_one a with ha | ha <;> simp [ha, bot_symmDiff]

/-- Helper lemma for add_smul -/
private lemma finset_add_smul_aux (a b : ZMod 2) (S : Finset α) :
    (if a + b = 0 then ∅ else S) = (if a = 0 then ∅ else S) ∆ (if b = 0 then ∅ else S) := by
  rcases ZMod2_eq_zero_or_one a with ha | ha <;> rcases ZMod2_eq_zero_or_one b with hb | hb
  · simp [ha, hb, symmDiff_self]
  · subst ha hb; simp only [zero_add, one_ne_zero, ↓reduceIte]; exact (bot_symmDiff S).symm
  · subst ha hb; simp only [add_zero, one_ne_zero, ↓reduceIte]; exact (symmDiff_bot S).symm
  · subst ha hb; simp only [show (1 : ZMod 2) + 1 = 0 by decide, ↓reduceIte, one_ne_zero, symmDiff_self]; rfl

/-- Finsets form a module (vector space) over ZMod 2 -/
instance finsetModule : Module (ZMod 2) (Finset α) where
  one_smul S := one_smul_finset S
  mul_smul a b S := by
    simp only [HSMul.hSMul, SMul.smul, finsetSMul]
    exact finset_mul_smul_aux a b S
  smul_zero a := by
    simp only [HSMul.hSMul, SMul.smul, finsetSMul]
    split_ifs <;> rfl
  smul_add a S T := by
    simp only [HSMul.hSMul, SMul.smul, finsetSMul, HAdd.hAdd, Add.add, finsetAdd]
    exact finset_smul_add_aux a S T
  add_smul a b S := by
    simp only [HSMul.hSMul, SMul.smul, finsetSMul, HAdd.hAdd, Add.add, finsetAdd]
    exact finset_add_smul_aux a b S
  zero_smul := zero_smul_finset

/-- The characteristic vector map is a linear map -/
theorem characteristicVector_add_eq (S T : Finset α) :
    characteristicVector (S + T) = characteristicVector S + characteristicVector T := by
  simp only [HAdd.hAdd, Add.add, finsetAdd]
  exact characteristicVector_symmDiff S T

/-- The characteristic vector map preserves scalar multiplication -/
theorem characteristicVector_smul (c : ZMod 2) (S : Finset α) :
    characteristicVector (c • S) = c • characteristicVector S := by
  rcases ZMod2_eq_zero_or_one c with hc | hc
  · subst hc
    simp only [HSMul.hSMul, SMul.smul, finsetSMul, ↓reduceIte, characteristicVector_empty]
    ext i
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    exact (zero_mul _).symm
  · subst hc
    simp only [HSMul.hSMul, SMul.smul, finsetSMul, one_ne_zero, ↓reduceIte]
    ext i
    exact (one_mul _).symm

/-- The characteristic vector map is a linear equivalence -/
def characteristicVectorLinearEquiv : Finset α ≃ₗ[ZMod 2] BinaryVector α where
  toFun := characteristicVector
  map_add' := characteristicVector_add_eq
  map_smul' := characteristicVector_smul
  invFun := fromBinaryVector
  left_inv := fromBinaryVector_characteristicVector
  right_inv := characteristicVector_fromBinaryVector

end VectorSpaceStructure

/-! ## Properties Useful for Graph Theory Applications -/

section GraphTheoryApplications

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The union of disjoint sets corresponds to addition (which is XOR/symmetric difference) -/
theorem characteristicVector_union_of_disjoint (S T : Finset α) (h : Disjoint S T) :
    characteristicVector (S ∪ T) = characteristicVector S + characteristicVector T := by
  rw [characteristicVector_add]
  congr 1
  exact (Disjoint.symmDiff_eq_sup h).symm

/-- Intersection can be expressed in terms of the algebraic structure -/
theorem characteristicVector_inter (S T : Finset α) :
    ∀ i, characteristicVector (S ∩ T) i = characteristicVector S i * characteristicVector T i := by
  intro i
  simp only [characteristicVector, Finset.mem_inter]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

/-- Complement relative to the universe -/
theorem characteristicVector_compl (S : Finset α) :
    characteristicVector Sᶜ = BinaryVector.ones + characteristicVector S := by
  ext i
  simp only [BinaryVector.ones, Pi.add_apply, characteristicVector, Finset.mem_compl]
  split_ifs with h
  · decide
  · decide

/-- The cardinality of a set can be recovered from its characteristic vector -/
theorem card_eq_sum_characteristicVector (S : Finset α) :
    S.card = ∑ i : α, (characteristicVector S i).val := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  have heq : Finset.univ.filter (· ∈ S) = S := by ext i; simp
  rw [heq]
  have h1 : ∑ x ∈ S, (characteristicVector S x).val = S.card := by
    conv_rhs => rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [characteristicVector, hi, ↓reduceIte, ZMod.val_one]
  have h2 : ∑ x ∈ Finset.univ.filter (· ∉ S), (characteristicVector S x).val = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [characteristicVector, hi, ↓reduceIte, ZMod.val_zero]
  omega

/-- Two sets are equal iff their characteristic vectors are equal -/
theorem finset_eq_iff_characteristicVector_eq (S T : Finset α) :
    S = T ↔ characteristicVector S = characteristicVector T :=
  ⟨fun h => by rw [h], fun h => characteristicVector_injective h⟩

/-- The symmetric difference has cardinality related to the original sets -/
theorem card_symmDiff_add_twice_inter (S T : Finset α) :
    (S ∆ T).card + 2 * (S ∩ T).card = S.card + T.card := by
  have hunion : (S ∪ T).card + (S ∩ T).card = S.card + T.card := Finset.card_union_add_card_inter S T
  have heq : S ∆ T = (S ∪ T) \ (S ∩ T) := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_union
  have hsd : (S ∆ T).card = (S ∪ T).card - (S ∩ T).card := by
    rw [heq]
    rw [Finset.card_sdiff_of_subset hsub]
  have hle : (S ∩ T).card ≤ (S ∪ T).card := Finset.card_le_card Finset.inter_subset_union
  omega

end GraphTheoryApplications

/-! ## Summary

The binary vector notation convention establishes:

1. **Identification**: A finset S ⊆ α corresponds to its characteristic vector χ_S : α → ZMod 2
   where χ_S(i) = 1 iff i ∈ S

2. **Addition = Symmetric Difference**: χ_{S Δ T} = χ_S + χ_T (componentwise in ZMod 2)

3. **Bijectivity**: This identification is a bijection, so sets and vectors can be used
   interchangeably

4. **Linear Structure**: Under this identification, Finset α becomes a ZMod 2-vector space
   where addition is symmetric difference

5. **Application**: This allows linear algebra techniques over F_2 to be applied to
   graph-theoretic problems involving sets of vertices, edges, or cycles.

The key insight is that XOR (symmetric difference) becomes ordinary addition in ZMod 2,
making linear algebraic techniques available for reasoning about graph properties.
-/
