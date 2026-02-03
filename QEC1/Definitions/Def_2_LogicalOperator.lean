import QEC1.Definitions.Def_1_StabilizerCode

/-!
# Logical Operator (Definition 2)

## Statement
Let C be an [[n, k, d]] stabilizer code with check operators {s_i}.

A **logical operator** is a Pauli operator L such that:
(i) L commutes with all stabilizer checks: [L, s_i] = 0 for all i.
(ii) L is not a product of stabilizer checks: L ∉ ⟨s_1, ..., s_{n-k}⟩.

A **logical representative** is a specific choice of Pauli operator L representing a
logical operator. Two logical representatives L and L' are **equivalent** if
L' = L · ∏_{i ∈ T} s_i for some T ⊆ {1, ..., n-k}.

The **weight** of a logical operator is |L| = |S_X(L) ∪ S_Z(L)|, the number of qubits
on which L acts non-trivially.

The code distance satisfies d = min{|L| : L is a logical operator}.

By choosing an appropriate single-qubit basis for each physical qubit, any logical
operator can be assumed to be **X-type**, i.e., L = ∏_{v ∈ L} X_v for some
L ⊆ {1, ..., n}.

## Main Results
**Main Structure** (`LogicalOperator`): A Pauli operator that commutes with all checks
  but is not a stabilizer element
**Equivalence** (`LogicalEquiv`): Equivalence relation on logical representatives
**X-Type Form** (`XTypeLogical`): Logical operators consisting only of X-gates

## File Structure
1. Logical Operator: Definition as a commuting non-stabilizer Pauli
2. Logical Representative: Specific choice of representative
3. Equivalence: When two representatives are equivalent
4. Weight: Weight of logical operators
5. X-Type Operators: Special case of X-only logical operators
6. Helper Lemmas: Basic properties
-/

namespace QEC

/-! ## Section 1: Logical Operator Definition -/

/-- A logical operator for a stabilizer code: a Pauli operator that commutes with all
    checks but is not a product of stabilizer elements (not in the stabilizer group). -/
structure LogicalOperator {n k : ℕ} (C : StabilizerCode n k) where
  /-- The underlying Pauli operator (as a stabilizer check structure) -/
  operator : StabilizerCheck n
  /-- The operator commutes with all stabilizer checks -/
  commutes_with_checks : commuteWithCode C operator
  /-- The operator is not a stabilizer element (not a product of checks) -/
  not_stabilizer : ¬isStabilizerElement C operator

namespace LogicalOperator

variable {n k : ℕ} {C : StabilizerCode n k}

/-- The weight of a logical operator: |S_X(L) ∪ S_Z(L)| -/
def weight (L : LogicalOperator C) : ℕ := L.operator.weight

/-- The X-support of a logical operator -/
def supportX (L : LogicalOperator C) : Finset (Fin n) := L.operator.supportX

/-- The Z-support of a logical operator -/
def supportZ (L : LogicalOperator C) : Finset (Fin n) := L.operator.supportZ

/-- Convert to a Pauli string (ignoring phase) -/
def toPauliString (L : LogicalOperator C) : PauliString n := L.operator.toPauliString

/-- A logical operator has weight at least d when the code has distance d -/
theorem weight_ge_distance {d : ℕ} (L : LogicalOperator C)
    (hd : hasDistance C d) : L.weight ≥ d := by
  exact hd L.operator L.commutes_with_checks L.not_stabilizer

end LogicalOperator

/-! ## Section 2: Logical Representatives and Equivalence -/

/-- Two logical operators are equivalent if they differ by a stabilizer element.
    That is, L' = L · ∏_{i ∈ T} s_i for some T ⊆ {1, ..., n-k}. -/
def LogicalEquiv {n k : ℕ} (C : StabilizerCode n k)
    (L₁ L₂ : StabilizerCheck n) : Prop :=
  ∃ T : Finset (Fin (n - k)),
    StabilizerCheck.samePauliAction
      L₂
      (StabilizerCheck.mul L₁ (productOfChecks C.checks T))

/-- Logical equivalence is reflexive -/
theorem LogicalEquiv.refl {n k : ℕ} (C : StabilizerCode n k)
    (L : StabilizerCheck n) : LogicalEquiv C L L := by
  use ∅
  rw [productOfChecks_empty, StabilizerCheck.mul_identity]
  exact ⟨rfl, rfl⟩

/-- Helper: symmDiff with itself cancels to empty -/
theorem symmDiff_self_eq_empty {α : Type*} [DecidableEq α] (A : Finset α) :
    symmDiff A A = ∅ := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.notMem_empty, iff_false, not_or, not_and, not_not]
  constructor <;> intro h
  · exact h
  · exact h

/-- Helper: symmDiff with empty is identity -/
theorem symmDiff_empty_right {α : Type*} [DecidableEq α] (A : Finset α) :
    symmDiff A ∅ = A := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.notMem_empty]
  constructor
  · intro h
    cases h with
    | inl hl => exact hl.1
    | inr hr => exact hr.1.elim
  · intro h
    left
    exact ⟨h, fun h' => h'.elim⟩

/-- Helper: Mul supportX is symmDiff of supportX -/
theorem mul_supportX_eq_symmDiff {n : ℕ} (s₁ s₂ : StabilizerCheck n) :
    (StabilizerCheck.mul s₁ s₂).supportX = symmDiff s₁.supportX s₂.supportX := by
  rfl

/-- Helper: Mul supportZ is symmDiff of supportZ -/
theorem mul_supportZ_eq_symmDiff {n : ℕ} (s₁ s₂ : StabilizerCheck n) :
    (StabilizerCheck.mul s₁ s₂).supportZ = symmDiff s₁.supportZ s₂.supportZ := by
  rfl

/-! ## Section 3: X-Type Logical Operators -/

/-- An X-type Pauli string: only X operators on certain qubits, identity elsewhere.
    This represents L = ∏_{v ∈ support} X_v -/
def XTypePauli (n : ℕ) (support : Finset (Fin n)) : StabilizerCheck n where
  supportX := support
  supportZ := ∅
  phase := Phase.one

/-- The weight of an X-type operator equals the cardinality of its support -/
theorem XTypePauli_weight (n : ℕ) (support : Finset (Fin n)) :
    (XTypePauli n support).weight = support.card := by
  simp only [XTypePauli, StabilizerCheck.weight, Finset.union_empty]

/-- An X-type logical operator for a code -/
structure XTypeLogical {n k : ℕ} (C : StabilizerCode n k) where
  /-- The support set L ⊆ {1, ..., n} -/
  support : Finset (Fin n)
  /-- The X-type operator commutes with all checks -/
  commutes_with_checks : commuteWithCode C (XTypePauli n support)
  /-- The X-type operator is not a stabilizer element -/
  not_stabilizer : ¬isStabilizerElement C (XTypePauli n support)

namespace XTypeLogical

variable {n k : ℕ} {C : StabilizerCode n k}

/-- Convert an X-type logical to a general logical operator -/
def toLogicalOperator (L : XTypeLogical C) : LogicalOperator C where
  operator := XTypePauli n L.support
  commutes_with_checks := L.commutes_with_checks
  not_stabilizer := L.not_stabilizer

/-- The weight of an X-type logical operator -/
def weight (L : XTypeLogical C) : ℕ := L.support.card

/-- X-type logical weight equals general logical weight -/
theorem weight_eq_logical_weight (L : XTypeLogical C) :
    L.weight = L.toLogicalOperator.weight := by
  simp only [weight, LogicalOperator.weight, toLogicalOperator, XTypePauli_weight]

end XTypeLogical

/-! ## Section 4: Distance and Minimum Weight -/

/-- The distance of a code is the minimum weight of any logical operator -/
def isMinDistance {n k : ℕ} (C : StabilizerCode n k) (d : ℕ) : Prop :=
  hasDistance C d ∧
  ∃ L : LogicalOperator C, L.weight = d

/-- Distance lower bound: every logical operator has weight ≥ d -/
theorem distance_lower_bound {n k d : ℕ} (C : StabilizerCode n k)
    (hd : hasDistance C d) (L : LogicalOperator C) :
    L.weight ≥ d := by
  exact hd L.operator L.commutes_with_checks L.not_stabilizer

/-! ## Section 5: Commutation Lemmas -/

/-- Commutation with code is preserved if Pauli action is the same -/
theorem commuteWithCode_of_samePauliAction {n k : ℕ} (C : StabilizerCode n k)
    {L₁ L₂ : StabilizerCheck n}
    (hL₁ : commuteWithCode C L₁)
    (hsame : StabilizerCheck.samePauliAction L₁ L₂) :
    commuteWithCode C L₂ := by
  intro i
  have h1 := hL₁ i
  unfold StabilizerCheck.commutes at h1 ⊢
  unfold StabilizerCheck.samePauliAction at hsame
  rw [← hsame.1, ← hsame.2]
  exact h1

/-- If L₂ has same Pauli action as L₁ * S_T, and L₁ commutes with code, so does L₂ -/
theorem LogicalEquiv.commutes_of_equiv {n k : ℕ} (C : StabilizerCode n k)
    {L₁ L₂ : StabilizerCheck n}
    (h : LogicalEquiv C L₁ L₂)
    (hL₁ : commuteWithCode C L₁) :
    commuteWithCode C L₂ := by
  obtain ⟨T, hT⟩ := h
  -- L₂ has same Pauli action as L₁ · S_T
  -- L₁ commutes with code, S_T (stabilizer element) commutes with code
  -- So L₁ · S_T commutes with code
  -- Since L₂ has same Pauli action, L₂ commutes with code
  have hprod : commuteWithCode C (StabilizerCheck.mul L₁ (productOfChecks C.checks T)) := by
    intro j
    have h1 : StabilizerCheck.commutes L₁ (C.checks j) := hL₁ j
    have h2 : StabilizerCheck.commutes (productOfChecks C.checks T) (C.checks j) := by
      have hstab : isStabilizerElement C (productOfChecks C.checks T) := ⟨T, ⟨rfl, rfl⟩⟩
      exact stabilizer_commutes_with_code C (productOfChecks C.checks T) hstab j
    exact mul_commutes_of_commutes L₁ (productOfChecks C.checks T) (C.checks j) h1 h2
  -- L₂ has same Pauli action as L₁ * S_T
  -- Commutation only depends on Pauli action
  intro i
  have hprod_i := hprod i
  unfold StabilizerCheck.commutes at hprod_i ⊢
  unfold StabilizerCheck.samePauliAction at hT
  rw [hT.1, hT.2]
  exact hprod_i

/-! ## Section 6: Helper Lemmas -/

/-- X-type operators have empty Z-support -/
@[simp]
theorem XTypePauli_supportZ (n : ℕ) (support : Finset (Fin n)) :
    (XTypePauli n support).supportZ = ∅ := by
  rfl

/-- X-type operators have phase 1 -/
@[simp]
theorem XTypePauli_phase (n : ℕ) (support : Finset (Fin n)) :
    (XTypePauli n support).phase = Phase.one := by
  rfl

/-- Empty support gives identity -/
@[simp]
theorem XTypePauli_empty (n : ℕ) :
    XTypePauli n ∅ = StabilizerCheck.identity n := by
  simp only [XTypePauli, StabilizerCheck.identity]

/-- X-type operator on singleton has weight 1 -/
theorem XTypePauli_singleton_weight {n : ℕ} (v : Fin n) :
    (XTypePauli n {v}).weight = 1 := by
  simp only [XTypePauli_weight, Finset.card_singleton]

/-- Logical operator weight is always non-negative -/
theorem LogicalOperator.weight_nonneg {n k : ℕ} {C : StabilizerCode n k}
    (L : LogicalOperator C) : 0 ≤ L.weight :=
  Nat.zero_le _

/-- X-type operator supportX is exactly the support -/
@[simp]
theorem XTypePauli_supportX (n : ℕ) (support : Finset (Fin n)) :
    (XTypePauli n support).supportX = support := by
  rfl

/-- Product of X-type operators has symmDiff support -/
theorem XTypePauli_mul_supportX (n : ℕ) (s₁ s₂ : Finset (Fin n)) :
    (StabilizerCheck.mul (XTypePauli n s₁) (XTypePauli n s₂)).supportX =
    symmDiff s₁ s₂ := by
  simp only [mul_supportX_eq_symmDiff, XTypePauli_supportX]

/-- X-type operator commutes with a check iff Z-support overlap is even -/
theorem XTypePauli_commutes_iff {n : ℕ} (support : Finset (Fin n))
    (s : StabilizerCheck n) :
    StabilizerCheck.commutes (XTypePauli n support) s ↔
    (support ∩ s.supportZ).card % 2 = 0 := by
  unfold StabilizerCheck.commutes
  simp only [XTypePauli_supportZ, Finset.empty_inter, Finset.card_empty,
    Nat.add_zero, XTypePauli_supportX]

/-- Z-type Pauli: only Z operators on certain qubits -/
def ZTypePauli (n : ℕ) (support : Finset (Fin n)) : StabilizerCheck n where
  supportX := ∅
  supportZ := support
  phase := Phase.one

/-- Z-type operators have empty X-support -/
@[simp]
theorem ZTypePauli_supportX (n : ℕ) (support : Finset (Fin n)) :
    (ZTypePauli n support).supportX = ∅ := by
  rfl

/-- Z-type operators supportZ is exactly the support -/
@[simp]
theorem ZTypePauli_supportZ (n : ℕ) (support : Finset (Fin n)) :
    (ZTypePauli n support).supportZ = support := by
  rfl

/-- Z-type operator weight equals support cardinality -/
theorem ZTypePauli_weight (n : ℕ) (support : Finset (Fin n)) :
    (ZTypePauli n support).weight = support.card := by
  simp only [ZTypePauli, StabilizerCheck.weight, Finset.empty_union]

/-- Z-type operator commutes with a check iff X-support overlap is even -/
theorem ZTypePauli_commutes_iff {n : ℕ} (support : Finset (Fin n))
    (s : StabilizerCheck n) :
    StabilizerCheck.commutes (ZTypePauli n support) s ↔
    (support ∩ s.supportX).card % 2 = 0 := by
  unfold StabilizerCheck.commutes
  simp only [ZTypePauli_supportX, Finset.empty_inter, Finset.card_empty,
    Nat.zero_add, ZTypePauli_supportZ]

end QEC
