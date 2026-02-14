import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.CharP.Two
import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.SymmDiff

/-!
# Notation: Binary Vectors

## Statement
Throughout this work we use binary vectors over ℤ₂ (equivalently 𝔽₂) to indicate collections of
vertices, edges, and cycles of a graph G. We identify the binary vector associated to a set of
vertices, edges, or cycles with the set itself. Addition of binary vectors corresponds to
symmetric difference of sets.

## Main Results
- `charVec`: characteristic vector of a set S over a type α as a function α → ZMod 2
- `charVec_mem`: `charVec S v = 1 ↔ v ∈ S`
- `charVec_symmDiff`: χ(S △ T) = χ(S) + χ(T), the key provable content

## Corollaries
- `charVec_symmDiff_self`: χ(S △ S) = 0
- `charVec_injective`: charVec is injective (distinct sets have distinct vectors)
-/

open scoped symmDiff

variable {α : Type*}

/-! ## Definition of characteristic vector -/

/-- The characteristic vector of a set `S` over a type `α`, taking values in `ZMod 2`.
  `charVec S v = 1` if `v ∈ S` and `charVec S v = 0` otherwise. -/
noncomputable def charVec (S : Set α) : α → ZMod 2 :=
  Set.indicator S 1

/-! ## Basic properties -/

theorem charVec_apply_of_mem {S : Set α} {v : α} (hv : v ∈ S) :
    charVec S v = 1 := by
  change Set.indicator S 1 v = 1
  exact Set.indicator_of_mem hv 1

theorem charVec_apply_of_not_mem {S : Set α} {v : α} (hv : v ∉ S) :
    charVec S v = 0 := by
  change Set.indicator S 1 v = 0
  exact Set.indicator_of_notMem hv 1

@[simp]
theorem charVec_mem {S : Set α} {v : α} :
    charVec S v = 1 ↔ v ∈ S := by
  constructor
  · intro h
    by_contra hv
    rw [charVec_apply_of_not_mem hv] at h
    exact absurd h (by decide)
  · exact charVec_apply_of_mem

@[simp]
theorem charVec_not_mem {S : Set α} {v : α} :
    charVec S v = 0 ↔ v ∉ S := by
  constructor
  · intro h hv
    rw [charVec_apply_of_mem hv] at h
    exact absurd h (by decide)
  · exact charVec_apply_of_not_mem

@[simp]
theorem charVec_empty : charVec (∅ : Set α) = 0 := by
  ext v
  simp only [Pi.zero_apply, charVec_not_mem, Set.mem_empty_iff_false, not_false_eq_true]

@[simp]
theorem charVec_univ : charVec (Set.univ : Set α) = 1 := by
  ext v
  simp only [Pi.one_apply, charVec_mem, Set.mem_univ]

/-! ## Main theorem: symmetric difference corresponds to addition -/

private lemma not_mem_symmDiff_of_mem_of_mem {S T : Set α} {v : α}
    (hS : v ∈ S) (hT : v ∈ T) : v ∉ S ∆ T := by
  rw [Set.mem_symmDiff]; push_neg; exact ⟨fun _ => hT, fun _ => hS⟩

private lemma not_mem_symmDiff_of_not_mem_of_not_mem {S T : Set α} {v : α}
    (hS : v ∉ S) (hT : v ∉ T) : v ∉ S ∆ T := by
  rw [Set.mem_symmDiff]; push_neg; exact ⟨fun h => absurd h hS, fun h => absurd h hT⟩

/-- The key provable content: the characteristic vector of the symmetric difference of two sets
equals the sum of their characteristic vectors in `ZMod 2`. This formalizes the identification
of binary vector addition with symmetric difference of sets. -/
theorem charVec_symmDiff (S T : Set α) :
    charVec (S ∆ T) = charVec S + charVec T := by
  ext v
  simp only [Pi.add_apply]
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T
  · rw [charVec_apply_of_not_mem (not_mem_symmDiff_of_mem_of_mem hS hT),
        charVec_apply_of_mem hS, charVec_apply_of_mem hT]
    decide
  · rw [charVec_apply_of_mem (Set.mem_symmDiff.mpr (Or.inl ⟨hS, hT⟩)),
        charVec_apply_of_mem hS, charVec_apply_of_not_mem hT]
    decide
  · rw [charVec_apply_of_mem (Set.mem_symmDiff.mpr (Or.inr ⟨hT, hS⟩)),
        charVec_apply_of_not_mem hS, charVec_apply_of_mem hT]
    decide
  · rw [charVec_apply_of_not_mem (not_mem_symmDiff_of_not_mem_of_not_mem hS hT),
        charVec_apply_of_not_mem hS, charVec_apply_of_not_mem hT]
    decide

/-! ## Corollaries and immediate consequences -/

@[simp]
theorem charVec_symmDiff_self (S : Set α) :
    charVec (S ∆ S) = 0 := by
  rw [symmDiff_self, Set.bot_eq_empty, charVec_empty]

theorem charVec_ext_iff (S T : Set α) :
    charVec S = charVec T ↔ S = T := by
  constructor
  · intro h
    ext v
    have hv := congr_fun h v
    constructor
    · intro hmem
      rwa [charVec_apply_of_mem hmem, eq_comm, charVec_mem] at hv
    · intro hmem
      rwa [charVec_apply_of_mem hmem, charVec_mem] at hv
  · rintro rfl; rfl

/-- `charVec` is injective: distinct sets have distinct characteristic vectors. -/
theorem charVec_injective : Function.Injective (charVec (α := α)) :=
  fun _ _ h => (charVec_ext_iff _ _).mp h

theorem charVec_subset_iff (S T : Set α) :
    (∀ v, charVec S v = 1 → charVec T v = 1) ↔ S ⊆ T := by
  constructor
  · intro h v hv
    have := h v (charVec_apply_of_mem hv)
    rwa [charVec_mem] at this
  · intro h v hv
    rw [charVec_mem] at hv ⊢
    exact h hv

@[simp]
theorem charVec_compl_add (S : Set α) (v : α) :
    charVec Sᶜ v + charVec S v = 1 := by
  by_cases hv : v ∈ S
  · have hvc : v ∉ Sᶜ := fun h => h hv
    rw [charVec_apply_of_not_mem hvc, charVec_apply_of_mem hv, zero_add]
  · rw [charVec_apply_of_mem ((Set.mem_compl_iff S v).mpr hv),
        charVec_apply_of_not_mem hv, add_zero]

theorem charVec_union (S T : Set α) :
    charVec (S ∪ T) = charVec S + charVec T + charVec (S ∩ T) := by
  ext v
  simp only [Pi.add_apply]
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T
  · rw [charVec_apply_of_mem (Set.mem_union_left T hS),
        charVec_apply_of_mem hS, charVec_apply_of_mem hT,
        charVec_apply_of_mem (Set.mem_inter hS hT)]
    decide
  · rw [charVec_apply_of_mem (Set.mem_union_left T hS),
        charVec_apply_of_mem hS, charVec_apply_of_not_mem hT,
        charVec_apply_of_not_mem (fun h => hT h.2)]
    decide
  · rw [charVec_apply_of_mem (Set.mem_union_right S hT),
        charVec_apply_of_not_mem hS, charVec_apply_of_mem hT,
        charVec_apply_of_not_mem (fun h => hS h.1)]
    decide
  · rw [charVec_apply_of_not_mem (fun h => h.elim hS hT),
        charVec_apply_of_not_mem hS, charVec_apply_of_not_mem hT,
        charVec_apply_of_not_mem (fun h => hS h.1)]
    decide

/-! ## SimpleGraph notation -/

/-- For a simple graph G on vertex type V, the vertex set is `Set.univ : Set V`. -/
abbrev vertexSetOf (V : Type*) : Set V := Set.univ

/-- For a simple graph G on vertex type V with edge type E, the edge set is `Set.univ : Set E`. -/
abbrev edgeSetOf (E : Type*) : Set E := Set.univ
