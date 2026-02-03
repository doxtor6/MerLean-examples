import QEC1.Remarks.Rem_1_NotationConventions

/-!
# Stabilizer Code (Definition 1)

## Statement
Let n, k, d ∈ ℕ with k < n. An [[n, k, d]] stabilizer code is specified by:
(i) Physical qubits: n qubits with Hilbert space H = (ℂ²)^⊗n
(ii) Check operators: n-k Pauli operators as stabilizer checks
(iii) Commutativity: Checks mutually commute
(iv) Independence: Checks are independent (no non-trivial product gives identity action)
(v) Code space: 2^k dimensional stabilized subspace
(vi) Distance: Minimum weight of non-check commuting Pauli operators ≥ d

## Main Results
**Main Structure** (`StabilizerCode`): Complete stabilizer code specification with k < n
- `checks`: The n-k stabilizer check operators
- `checks_commute`: All checks mutually commute
- `checks_independent`: No non-trivial product of checks has trivial Pauli action

## File Structure
1. Phase Type: Complex phase factors i^σ for σ ∈ {0,1,2,3}
2. Stabilizer Check: Full Pauli operator with phase
3. Stabilizer Code: Complete code specification with k < n constraint
4. LDPC Condition: Low-density parity-check property
5. Helper Lemmas: Basic properties of stabilizer codes

## Faithfulness Notes
- This is a combinatorial formalization focusing on the support structure
- The Hilbert space and eigenspace structure is not formalized (would require complex analysis)
- Phase tracking correctly handles Y = iXZ interactions via overlap counting
- Independence is checked on Pauli string equality (trivial action), not exact phase match
-/

namespace QEC

/-! ## Section 1: Phase Factors -/

/-- Phase factor i^σ where σ ∈ {0, 1, 2, 3} representing 1, i, -1, -i -/
abbrev Phase := Fin 4

namespace Phase

/-- The trivial phase (i^0 = 1) -/
def one : Phase := ⟨0, by omega⟩

/-- The imaginary unit phase (i^1 = i) -/
def imag : Phase := ⟨1, by omega⟩

/-- The negative phase (i^2 = -1) -/
def neg : Phase := ⟨2, by omega⟩

/-- The negative imaginary phase (i^3 = -i) -/
def negImag : Phase := ⟨3, by omega⟩

/-- Multiplication of phases: i^a · i^b = i^(a+b mod 4) -/
def mul (a b : Phase) : Phase := ⟨(a.val + b.val) % 4, Nat.mod_lt _ (by omega)⟩

/-- Phase multiplication is commutative -/
theorem mul_comm (a b : Phase) : mul a b = mul b a := by
  simp only [mul]
  congr 1
  omega

/-- The identity phase is left neutral -/
theorem one_mul (a : Phase) : mul one a = a := by
  simp only [mul, one, Nat.zero_add, Nat.mod_eq_of_lt a.isLt]

/-- The identity phase is right neutral -/
theorem mul_one (a : Phase) : mul a one = a := by
  rw [mul_comm, one_mul]

/-- Shift a phase by n units -/
def shift (p : Phase) (n : ℕ) : Phase := ⟨(p.val + n) % 4, Nat.mod_lt _ (by omega)⟩

end Phase

/-! ## Section 2: Stabilizer Check Operators -/

/-- A stabilizer check operator: i^σ · ∏_{v∈S_X} X_v · ∏_{v∈S_Z} Z_v
    We represent this by the X-support, Z-support, and phase.
    Note: When both X and Z act on a site, we get Y = iXZ. -/
@[ext]
structure StabilizerCheck (n : ℕ) where
  /-- X-type support: qubits where X or Y acts -/
  supportX : Finset (Fin n)
  /-- Z-type support: qubits where Z or Y acts -/
  supportZ : Finset (Fin n)
  /-- Phase factor σ ∈ {0,1,2,3} for i^σ -/
  phase : Phase
  deriving DecidableEq

namespace StabilizerCheck

variable {n : ℕ}

/-- The identity check operator -/
def identity (n : ℕ) : StabilizerCheck n where
  supportX := ∅
  supportZ := ∅
  phase := Phase.one

/-- Weight of a check: number of non-identity sites -/
def weight (s : StabilizerCheck n) : ℕ :=
  (s.supportX ∪ s.supportZ).card

/-- The underlying Pauli string (without phase) -/
def toPauliString (s : StabilizerCheck n) : PauliString n := fun i =>
  match s.supportX.decidableMem i, s.supportZ.decidableMem i with
  | isTrue _, isTrue _ => PauliOp.Y   -- Both X and Z → Y
  | isTrue _, isFalse _ => PauliOp.X  -- Only X
  | isFalse _, isTrue _ => PauliOp.Z  -- Only Z
  | isFalse _, isFalse _ => PauliOp.I -- Neither

/-- Check if two stabilizer checks have the same Pauli string (same action, ignoring phase) -/
def samePauliAction (s₁ s₂ : StabilizerCheck n) : Prop :=
  s₁.supportX = s₂.supportX ∧ s₁.supportZ = s₂.supportZ

/-- Check if a stabilizer check has trivial Pauli action (identity operator, any phase) -/
def hasTrivialAction (s : StabilizerCheck n) : Prop :=
  s.supportX = ∅ ∧ s.supportZ = ∅

instance : DecidablePred (@hasTrivialAction n) := fun s =>
  inferInstanceAs (Decidable (s.supportX = ∅ ∧ s.supportZ = ∅))

/-- Identity check has zero weight -/
theorem identity_weight : (identity n).weight = 0 := by
  simp only [identity, weight, Finset.empty_union, Finset.card_empty]

/-- Identity check maps to identity Pauli string -/
theorem identity_toPauliString :
    (identity n).toPauliString = PauliString.identity n := by
  funext i
  simp only [identity, toPauliString, PauliString.identity]
  rfl

/-- Identity has trivial action -/
theorem identity_hasTrivialAction : hasTrivialAction (identity n) :=
  ⟨rfl, rfl⟩

/-- Commutativity condition for two checks based on support overlap -/
def commutes (s₁ s₂ : StabilizerCheck n) : Prop :=
  ((s₁.supportX ∩ s₂.supportZ).card + (s₁.supportZ ∩ s₂.supportX).card) % 2 = 0

/-- Commutativity is symmetric -/
theorem commutes_symm (s₁ s₂ : StabilizerCheck n) :
    commutes s₁ s₂ ↔ commutes s₂ s₁ := by
  unfold commutes
  constructor <;> intro h
  · have : (s₁.supportX ∩ s₂.supportZ).card = (s₂.supportZ ∩ s₁.supportX).card := by
      rw [Finset.inter_comm]
    have h2 : (s₁.supportZ ∩ s₂.supportX).card = (s₂.supportX ∩ s₁.supportZ).card := by
      rw [Finset.inter_comm]
    rw [this, h2, Nat.add_comm] at h
    exact h
  · have : (s₂.supportX ∩ s₁.supportZ).card = (s₁.supportZ ∩ s₂.supportX).card := by
      rw [Finset.inter_comm]
    have h2 : (s₂.supportZ ∩ s₁.supportX).card = (s₁.supportX ∩ s₂.supportZ).card := by
      rw [Finset.inter_comm]
    rw [this, h2, Nat.add_comm] at h
    exact h

/-- Every check commutes with itself -/
theorem self_commutes (s : StabilizerCheck n) : commutes s s := by
  simp only [commutes]
  have h : (s.supportX ∩ s.supportZ).card + (s.supportZ ∩ s.supportX).card =
           2 * (s.supportX ∩ s.supportZ).card := by
    rw [Finset.inter_comm s.supportZ s.supportX]
    ring
  rw [h]
  exact Nat.mul_mod_right 2 _

/-- Identity commutes with everything -/
theorem identity_commutes_all (s : StabilizerCheck n) : commutes (identity n) s := by
  simp only [commutes, identity, Finset.empty_inter, Finset.card_empty, Nat.zero_add,
    Nat.zero_mod]

/-- Number of sites where both checks have overlapping X and Z (Y-interactions)
    When s₁ has X and s₂ has Z at the same site (or vice versa), phase factors arise.
    Specifically, XZ = iY and ZX = -iY, so the ordering matters. -/
def overlapXZ (s₁ s₂ : StabilizerCheck n) : ℕ :=
  (s₁.supportX ∩ s₂.supportZ).card

/-- Product of two check operators with correct phase handling.
    The phase accumulates contributions from:
    1. Original phases: s₁.phase + s₂.phase
    2. Y-interactions: When s₁ has X at site v and s₂ has Z at site v,
       we get XZ = iY, contributing +1 to the phase.
       When s₁ has Z at site v and s₂ has X at site v,
       we get ZX = -iY, contributing +3 (≡ -1) to the phase.
    Total extra phase = |s₁.X ∩ s₂.Z| - |s₁.Z ∩ s₂.X| mod 4 -/
def mul (s₁ s₂ : StabilizerCheck n) : StabilizerCheck n where
  supportX := symmDiff s₁.supportX s₂.supportX
  supportZ := symmDiff s₁.supportZ s₂.supportZ
  phase :=
    let basePhase := Phase.mul s₁.phase s₂.phase
    -- XZ = iY contributes +1, ZX = -iY contributes -1 = +3 mod 4
    -- Net contribution: |s₁.X ∩ s₂.Z| * 1 + |s₁.Z ∩ s₂.X| * 3 mod 4
    -- This equals |s₁.X ∩ s₂.Z| + 3 * |s₁.Z ∩ s₂.X| mod 4
    let xzOverlap := (s₁.supportX ∩ s₂.supportZ).card
    let zxOverlap := (s₁.supportZ ∩ s₂.supportX).card
    let extraPhase := (xzOverlap + 3 * zxOverlap) % 4
    Phase.shift basePhase extraPhase

/-- Identity is left neutral for multiplication (on Pauli action) -/
theorem identity_mul_samePauliAction (s : StabilizerCheck n) :
    samePauliAction (mul (identity n) s) s := by
  simp only [mul, identity, samePauliAction]
  constructor <;> simp [symmDiff]

/-- Identity is right neutral for multiplication (on Pauli action) -/
theorem mul_identity_samePauliAction (s : StabilizerCheck n) :
    samePauliAction (mul s (identity n)) s := by
  simp only [mul, identity, samePauliAction]
  constructor <;> simp [symmDiff]

/-- Identity is left neutral for multiplication -/
theorem identity_mul (s : StabilizerCheck n) : mul (identity n) s = s := by
  simp only [mul, identity, Phase.one_mul, Phase.shift]
  ext <;> simp [symmDiff]

/-- Identity is right neutral for multiplication -/
theorem mul_identity (s : StabilizerCheck n) : mul s (identity n) = s := by
  simp only [mul, identity, Phase.mul_one, Phase.shift]
  ext
  · simp [symmDiff]
  · simp [symmDiff]
  · simp only [Finset.inter_empty, Finset.card_empty, Nat.mul_zero, Nat.zero_mod,
               Nat.add_zero, Nat.mod_eq_of_lt s.phase.isLt]

end StabilizerCheck

/-! ## Section 3: Full Stabilizer Code -/

/-- Product of checks indexed by a Finset, using list fold -/
noncomputable def productOfChecks {n m : ℕ} (checks : Fin m → StabilizerCheck n)
    (T : Finset (Fin m)) : StabilizerCheck n :=
  T.val.toList.foldr (fun i acc => StabilizerCheck.mul (checks i) acc)
    (StabilizerCheck.identity n)

/-- An [[n, k, d]] stabilizer code with n physical qubits, k logical qubits.
    The code is specified by n-k independent, mutually commuting stabilizer checks.
    We require k < n as per the original mathematical definition. -/
structure StabilizerCode (n k : ℕ) where
  /-- k must be strictly less than n (logical qubits < physical qubits) -/
  k_lt_n : k < n
  /-- The n-k stabilizer check generators -/
  checks : Fin (n - k) → StabilizerCheck n
  /-- All checks mutually commute -/
  checks_commute : ∀ i j, StabilizerCheck.commutes (checks i) (checks j)
  /-- Checks are independent: only trivial product gives identity Pauli action
      (i.e., trivial supportX and supportZ - phase is ignored as it's a global phase) -/
  checks_independent : ∀ (T : Finset (Fin (n - k))),
    (productOfChecks checks T).hasTrivialAction → T = ∅

namespace StabilizerCode

variable {n k : ℕ}

/-- Number of stabilizer generators -/
def numGenerators (_C : StabilizerCode n k) : ℕ := n - k

/-- Symbolic dimension of code space is 2^k.
    Note: This is a combinatorial/symbolic definition. The actual Hilbert space
    structure (eigenspaces, etc.) is not formalized here. -/
def codeDimension (_C : StabilizerCode n k) : ℕ := 2 ^ k

/-- Number of physical qubits -/
def numPhysical (_C : StabilizerCode n k) : ℕ := n

/-- Number of logical qubits -/
def numLogical (_C : StabilizerCode n k) : ℕ := k

/-- Get the i-th check operator -/
def getCheck (C : StabilizerCode n k) (i : Fin (n - k)) : StabilizerCheck n :=
  C.checks i

/-- The k < n constraint -/
theorem logical_lt_physical (C : StabilizerCode n k) : k < n := C.k_lt_n

/-- All checks commute with themselves -/
theorem check_self_commutes (C : StabilizerCode n k) (i : Fin (n - k)) :
    StabilizerCheck.commutes (C.checks i) (C.checks i) :=
  StabilizerCheck.self_commutes _

/-- Commutativity is symmetric for checks -/
theorem check_commutes_symm (C : StabilizerCode n k) (i j : Fin (n - k)) :
    StabilizerCheck.commutes (C.checks i) (C.checks j) ↔
    StabilizerCheck.commutes (C.checks j) (C.checks i) :=
  StabilizerCheck.commutes_symm _ _

end StabilizerCode

/-! ## Section 4: LDPC Property -/

/-- Maximum weight of any check in a code -/
def maxCheckWeight {n k : ℕ} (C : StabilizerCode n k) : ℕ :=
  if h : n - k = 0 then 0
  else Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
         (fun i => (C.checks i).weight)

/-- Number of checks a qubit participates in -/
def qubitDegree {n k : ℕ} (C : StabilizerCode n k) (v : Fin n) : ℕ :=
  Finset.card (Finset.filter
    (fun i => v ∈ (C.checks i).supportX ∪ (C.checks i).supportZ) Finset.univ)

/-- Maximum qubit degree in a code -/
def maxQubitDegree {n k : ℕ} (C : StabilizerCode n k) : ℕ :=
  if h : n = 0 then 0
  else Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
         (fun v => qubitDegree C v)

/-- A stabilizer code is LDPC if check weights and qubit degrees are bounded -/
structure IsLDPC {n k : ℕ} (C : StabilizerCode n k) (w Δ : ℕ) : Prop where
  /-- Each check has weight at most w -/
  check_weight_bound : ∀ i, (C.checks i).weight ≤ w
  /-- Each qubit participates in at most Δ checks -/
  qubit_degree_bound : ∀ v, qubitDegree C v ≤ Δ

/-! ## Section 5: Distance -/

/-- A Pauli operator commutes with all checks of a code -/
def commuteWithCode {n k : ℕ} (C : StabilizerCode n k) (P : StabilizerCheck n) : Prop :=
  ∀ i, StabilizerCheck.commutes P (C.checks i)

/-- A Pauli operator is a product of checks (stabilizer element, up to Pauli action) -/
def isStabilizerElement {n k : ℕ} (C : StabilizerCode n k) (P : StabilizerCheck n) : Prop :=
  ∃ T : Finset (Fin (n - k)), StabilizerCheck.samePauliAction (productOfChecks C.checks T) P

/-- The distance condition: all commuting non-stabilizer operators have weight ≥ d -/
def hasDistance {n k : ℕ} (C : StabilizerCode n k) (d : ℕ) : Prop :=
  ∀ P : StabilizerCheck n,
    commuteWithCode C P → ¬isStabilizerElement C P → P.weight ≥ d

/-! ## Section 6: Full Stabilizer Code with Distance -/

/-- Complete [[n, k, d]] stabilizer code with explicit distance -/
structure StabilizerCodeWithDistance (n k d : ℕ) extends StabilizerCode n k where
  /-- The code has distance at least d -/
  distance_bound : hasDistance toStabilizerCode d

/-! ## Section 7: Helper Lemmas -/

/-- Product of empty set is identity -/
theorem productOfChecks_empty {n m : ℕ} (checks : Fin m → StabilizerCheck n) :
    productOfChecks checks ∅ = StabilizerCheck.identity n := by
  simp only [productOfChecks, Finset.empty_val, Multiset.toList_zero, List.foldr_nil]

/-- Product of empty set has trivial action -/
theorem productOfChecks_empty_hasTrivialAction {n m : ℕ} (checks : Fin m → StabilizerCheck n) :
    (productOfChecks checks ∅).hasTrivialAction := by
  rw [productOfChecks_empty]
  exact StabilizerCheck.identity_hasTrivialAction

/-- Identity check is in the stabilizer group -/
theorem identity_is_stabilizer {n k : ℕ} (C : StabilizerCode n k) :
    isStabilizerElement C (StabilizerCheck.identity n) := by
  use ∅
  rw [productOfChecks_empty]
  exact ⟨rfl, rfl⟩

/-- Key lemma: cardinality of symmDiff intersection mod 2
    equals sum of individual cardinalities mod 2 -/
theorem symmDiff_inter_card_mod2 {α : Type*} [DecidableEq α] (A B S : Finset α) :
    (symmDiff A B ∩ S).card % 2 = ((A ∩ S).card + (B ∩ S).card) % 2 := by
  -- symmDiff A B = (A \ B) ∪ (B \ A), disjoint union
  -- symmDiff A B ∩ S = ((A \ B) ∩ S) ∪ ((B \ A) ∩ S), also disjoint
  have h_disjoint : Disjoint ((A \ B) ∩ S) ((B \ A) ∩ S) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hx hy
    intro heq
    rw [heq] at hx
    exact hx.1.2 hy.1.1
  have h_eq : symmDiff A B ∩ S = ((A \ B) ∩ S) ∪ ((B \ A) ∩ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro ⟨hab, hs⟩
      cases hab with
      | inl h => left; exact ⟨h, hs⟩
      | inr h => right; exact ⟨h, hs⟩
    · intro h
      cases h with
      | inl h => exact ⟨Or.inl h.1, h.2⟩
      | inr h => exact ⟨Or.inr h.1, h.2⟩
  rw [h_eq, Finset.card_union_of_disjoint h_disjoint]
  -- Now: |(A \ B) ∩ S| + |(B \ A) ∩ S| mod 2 = |A ∩ S| + |B ∩ S| mod 2
  -- Use: |A ∩ S| = |(A \ B) ∩ S| + |A ∩ B ∩ S|
  -- Use: |B ∩ S| = |(B \ A) ∩ S| + |A ∩ B ∩ S|
  have hA : (A ∩ S).card = ((A \ B) ∩ S).card + (A ∩ B ∩ S).card := by
    have h_disjA : Disjoint ((A \ B) ∩ S) (A ∩ B ∩ S) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy heq
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx hy
      rw [heq] at hx
      exact hx.1.2 hy.1.2
    have h_eqA : A ∩ S = ((A \ B) ∩ S) ∪ (A ∩ B ∩ S) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro ⟨ha, hs⟩
        by_cases hb : x ∈ B
        · right; exact ⟨⟨ha, hb⟩, hs⟩
        · left; exact ⟨⟨ha, hb⟩, hs⟩
      · intro h
        cases h with
        | inl h => exact ⟨h.1.1, h.2⟩
        | inr h => exact ⟨h.1.1, h.2⟩
    rw [h_eqA, Finset.card_union_of_disjoint h_disjA]
  have hB : (B ∩ S).card = ((B \ A) ∩ S).card + (A ∩ B ∩ S).card := by
    have h_disjB : Disjoint ((B \ A) ∩ S) (A ∩ B ∩ S) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy heq
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx hy
      rw [heq] at hx
      exact hx.1.2 hy.1.1
    have h_eqB : B ∩ S = ((B \ A) ∩ S) ∪ (A ∩ B ∩ S) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro ⟨hb, hs⟩
        by_cases ha : x ∈ A
        · right; exact ⟨⟨ha, hb⟩, hs⟩
        · left; exact ⟨⟨hb, ha⟩, hs⟩
      · intro h
        cases h with
        | inl h => exact ⟨h.1.1, h.2⟩
        | inr h => exact ⟨h.1.2, h.2⟩
    rw [h_eqB, Finset.card_union_of_disjoint h_disjB]
  -- Now we have:
  -- |A ∩ S| + |B ∩ S| = |(A\B)∩S| + |A∩B∩S| + |(B\A)∩S| + |A∩B∩S|
  --                    = |(A\B)∩S| + |(B\A)∩S| + 2|A∩B∩S|
  omega

/-- Commutativity is preserved under multiplication: if A commutes with D and B commutes with D,
    then their product commutes with D. This uses the symplectic inner product structure.
    The proof uses that the symplectic form is additive in the first argument. -/
theorem mul_commutes_of_commutes {n : ℕ} (A B D : StabilizerCheck n)
    (hA : StabilizerCheck.commutes A D) (hB : StabilizerCheck.commutes B D) :
    StabilizerCheck.commutes (StabilizerCheck.mul A B) D := by
  unfold StabilizerCheck.commutes at *
  simp only [StabilizerCheck.mul]
  -- We need to prove:
  -- |symmDiff(A.sX, B.sX) ∩ D.sZ| + |symmDiff(A.sZ, B.sZ) ∩ D.sX| ≡ 0 (mod 2)
  -- Using the lemma about symmDiff intersection cardinality
  have h1 : (symmDiff A.supportX B.supportX ∩ D.supportZ).card % 2 =
            ((A.supportX ∩ D.supportZ).card + (B.supportX ∩ D.supportZ).card) % 2 :=
    symmDiff_inter_card_mod2 A.supportX B.supportX D.supportZ
  have h2 : (symmDiff A.supportZ B.supportZ ∩ D.supportX).card % 2 =
            ((A.supportZ ∩ D.supportX).card + (B.supportZ ∩ D.supportX).card) % 2 :=
    symmDiff_inter_card_mod2 A.supportZ B.supportZ D.supportX
  -- Now we have:
  -- (|A.sX ∩ D.sZ| + |B.sX ∩ D.sZ|) % 2 + (|A.sZ ∩ D.sX| + |B.sZ ∩ D.sX|) % 2 ≡ 0 mod 2
  -- Rearranging: (|A.sX ∩ D.sZ| + |A.sZ ∩ D.sX|) + (|B.sX ∩ D.sZ| + |B.sZ ∩ D.sX|) mod 2
  -- = hA + hB mod 2 = 0 + 0 = 0 mod 2
  omega

/-- Helper: list fold of checks commutes with any check -/
theorem list_fold_commutes {n k : ℕ} (C : StabilizerCode n k) (i : Fin (n - k))
    (L : List (Fin (n - k))) :
    StabilizerCheck.commutes
      (L.foldr (fun j acc => StabilizerCheck.mul (C.checks j) acc)
        (StabilizerCheck.identity n))
      (C.checks i) := by
  induction L with
  | nil =>
    simp only [List.foldr_nil]
    exact StabilizerCheck.identity_commutes_all _
  | cons x xs ih =>
    simp only [List.foldr_cons]
    apply mul_commutes_of_commutes
    · exact C.checks_commute x i
    · exact ih

/-- Stabilizer elements commute with all checks -/
theorem stabilizer_commutes_with_code {n k : ℕ} (C : StabilizerCode n k)
    (P : StabilizerCheck n) (hP : isStabilizerElement C P) :
    commuteWithCode C P := by
  intro i
  obtain ⟨T, hT⟩ := hP
  -- First show the product commutes
  have hprod : StabilizerCheck.commutes (productOfChecks C.checks T) (C.checks i) := by
    unfold productOfChecks
    exact list_fold_commutes C i T.val.toList
  -- Commutation only depends on Pauli action (supports), not phase
  unfold StabilizerCheck.commutes at hprod ⊢
  unfold StabilizerCheck.samePauliAction at hT
  rw [← hT.1, ← hT.2]
  exact hprod

/-- The weight of identity check is 0 -/
@[simp]
theorem identity_check_weight_zero (n : ℕ) :
    (StabilizerCheck.identity n).weight = 0 :=
  StabilizerCheck.identity_weight

/-- LDPC bounds are non-negative -/
theorem ldpc_bounds_nonneg {n k : ℕ} (_C : StabilizerCode n k) (w Δ : ℕ)
    (_h : IsLDPC _C w Δ) : 0 ≤ w ∧ 0 ≤ Δ := ⟨Nat.zero_le w, Nat.zero_le Δ⟩

/-- If a check has weight 0, it has trivial action -/
theorem weight_zero_trivial_action {n : ℕ} (s : StabilizerCheck n)
    (h : s.weight = 0) : s.hasTrivialAction := by
  simp only [StabilizerCheck.weight] at h
  rw [Finset.card_eq_zero] at h
  simp only [StabilizerCheck.hasTrivialAction]
  constructor
  · ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    have hmem : x ∈ s.supportX ∪ s.supportZ := Finset.mem_union_left _ hx
    rw [h] at hmem
    exact Finset.notMem_empty x hmem
  · ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    have hmem : x ∈ s.supportX ∪ s.supportZ := Finset.mem_union_right _ hx
    rw [h] at hmem
    exact Finset.notMem_empty x hmem

end QEC
