import QEC1.Definitions.Def_16_BivariateBicycleCode
import QEC1.Definitions.Def_2_LogicalOperator
import QEC1.Definitions.Def_3_GaugingGraph

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# BB Code Symmetry (Proposition 4)

## Statement
Bivariate Bicycle codes have a symmetry between left and right qubits that relates
X-type and Z-type logical operators:

If X̄ = X(p, q) is a logical X operator (acting on left qubits (p, L) and right qubits (q, R)),
then:
  Z̄ = Z(q^T, p^T)
is the corresponding logical Z operator, where p^T = p(x^{-1}, y^{-1}).

**Consequence for gauging**: A gauging graph construction for measuring X̄_α = X(αf, 0)
also works for measuring Z̄'_α = Z(0, αf^T) with the roles of left and right qubits swapped.

## Main Results
**Lemma** (`parity_check_symmetry`): If H_X · (p, q)^T = 0, then H_Z · (q^T, p^T)^T = 0
**Lemma** (`commutation_preserved`): Symplectic inner product preserved under transpose
**Main Theorem** (`logical_symmetry_XtoZ`): X(p,q) logical ↔ Z(q^T, p^T) logical
**Corollary** (`gauging_symmetry`): Gauging construction transfers between X and Z types

## File Structure
1. BB Logical Operator Supports: Support representation for logical operators
2. Overlap Computation: Computing overlaps for commutation conditions
3. Parity Check Symmetry: The key lemma about H_X and H_Z relationship
4. Commutation Preservation: Symplectic inner product invariance
5. Main Symmetry Theorem: X(p,q) corresponds to Z(q^T, p^T)
6. Gauging Symmetry: Application to gauging graphs
-/

namespace QEC

/-! ## Section 1: BB Code Logical Operator Supports -/

variable {ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-- Support representation for a logical operator on a BB code.
    A logical X operator X(p, q) acts on:
    - Left qubits at positions given by polynomial p
    - Right qubits at positions given by polynomial q

    We represent this as a pair of polynomial supports. -/
structure BBLogicalSupport (ℓ m : ℕ) [NeZero ℓ] [NeZero m] where
  /-- Left qubit support (polynomial p) -/
  leftSupport : BBPolynomial ℓ m
  /-- Right qubit support (polynomial q) -/
  rightSupport : BBPolynomial ℓ m
  deriving DecidableEq

namespace BBLogicalSupport

/-- The zero support (no qubits acted on) -/
def zero : BBLogicalSupport ℓ m where
  leftSupport := BBPolynomial.zero
  rightSupport := BBPolynomial.zero

/-- Support only on left qubits -/
def leftOnly (p : BBPolynomial ℓ m) : BBLogicalSupport ℓ m where
  leftSupport := p
  rightSupport := BBPolynomial.zero

/-- Support only on right qubits -/
def rightOnly (q : BBPolynomial ℓ m) : BBLogicalSupport ℓ m where
  leftSupport := BBPolynomial.zero
  rightSupport := q

/-- Total weight of the support -/
def weight (S : BBLogicalSupport ℓ m) : ℕ :=
  S.leftSupport.numTerms + S.rightSupport.numTerms

/-- The transpose operation: (p, q)^T = (q^T, p^T)
    This is the key symmetry operation for BB codes. -/
def transpose (S : BBLogicalSupport ℓ m) : BBLogicalSupport ℓ m where
  leftSupport := S.rightSupport.transpose
  rightSupport := S.leftSupport.transpose

/-- Double transpose returns the original support -/
theorem transpose_transpose (S : BBLogicalSupport ℓ m) :
    S.transpose.transpose = S := by
  simp only [transpose, BBPolynomial.transpose_transpose]

/-- Transpose of zero is zero -/
theorem transpose_zero : (zero : BBLogicalSupport ℓ m).transpose = zero := by
  simp only [transpose, zero, BBPolynomial.transpose_zero]

/-- Left-only support transposes to right-only -/
theorem transpose_leftOnly (p : BBPolynomial ℓ m) :
    (leftOnly p).transpose = rightOnly p.transpose := by
  simp only [transpose, leftOnly, rightOnly, BBPolynomial.transpose_zero]

/-- Right-only support transposes to left-only -/
theorem transpose_rightOnly (q : BBPolynomial ℓ m) :
    (rightOnly q).transpose = leftOnly q.transpose := by
  simp only [transpose, rightOnly, leftOnly, BBPolynomial.transpose_zero]

end BBLogicalSupport

/-! ## Section 2: Overlap Computation for Commutation -/

/-- Compute the overlap of support S with check polynomial P at check index α.
    This counts |{k : (α.1 + k.1, α.2 + k.2) ∈ P.support ∧ k ∈ S.support}|.

    In F_2 arithmetic, the commutation condition is that this count is even. -/
def bbOverlapCount (S P : BBPolynomial ℓ m) (α : Fin ℓ × Fin m) : ℕ :=
  (S.support.filter (fun k => (α.1 + k.1, α.2 + k.2) ∈ P.support)).card

/-- The transpose operation on indices: (a, b) ↦ (-a, -b) -/
def transposeIdx (α : Fin ℓ × Fin m) : Fin ℓ × Fin m := (-α.1, -α.2)

/-- Transpose index is an involution -/
theorem transposeIdx_involutive (α : Fin ℓ × Fin m) :
    transposeIdx (transposeIdx α) = α := by
  simp only [transposeIdx, neg_neg]

/-- Transpose index on zero is zero -/
@[simp]
theorem transposeIdx_zero : transposeIdx ((0, 0) : Fin ℓ × Fin m) = (0, 0) := by
  simp only [transposeIdx, neg_zero]

/-! ## Section 3: Parity Check Symmetry Lemma -/

/-- For a BB code with H_X = [A | B] and H_Z = [B^T | A^T]:

    The X commutation condition for support S = (p, q) at check index α is:
    overlap(p, A, α) + overlap(q, B, α) ≡ 0 (mod 2)

    The Z commutation condition for support S = (p, q) at check index β is:
    overlap(p, B^T, β) + overlap(q, A^T, β) ≡ 0 (mod 2) -/
def XCommutationAt (C : BivariateBicycleCode ℓ m) (S : BBLogicalSupport ℓ m)
    (α : Fin ℓ × Fin m) : Prop :=
  (bbOverlapCount S.leftSupport C.polyA α + bbOverlapCount S.rightSupport C.polyB α) % 2 = 0

def ZCommutationAt (C : BivariateBicycleCode ℓ m) (S : BBLogicalSupport ℓ m)
    (β : Fin ℓ × Fin m) : Prop :=
  (bbOverlapCount S.leftSupport C.polyB.transpose β +
   bbOverlapCount S.rightSupport C.polyA.transpose β) % 2 = 0

/-- The negation map on Fin ℓ × Fin m is injective -/
theorem neg_pair_injective : Function.Injective (fun (ab : Fin ℓ × Fin m) => (-ab.1, -ab.2)) := by
  intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
  simp only [Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

/-- Key helper: The overlap of p^T with Q^T at index β equals the overlap of p with Q at -β.

    This uses the fact that k ∈ p^T.support iff -k ∈ p.support,
    and (β + k) ∈ Q^T.support iff -(β + k) ∈ Q.support iff (-β - k) ∈ Q.support. -/
theorem overlap_transpose_eq (p Q : BBPolynomial ℓ m) (β : Fin ℓ × Fin m) :
    bbOverlapCount p.transpose Q.transpose β = bbOverlapCount p Q (transposeIdx β) := by
  simp only [bbOverlapCount, transposeIdx]
  -- We establish a bijection between the two filtered sets
  -- LHS filter: k in p^T.support and (β + k) in Q^T.support
  -- RHS filter: k' in p.support and (-β + k') in Q.support
  -- Bijection: k ↔ -k' (i.e., k' = -k)
  have h_eq : (p.transpose.support.filter (fun k => (β.1 + k.1, β.2 + k.2) ∈ Q.transpose.support)).card =
              (p.support.filter (fun k => (-β.1 + k.1, -β.2 + k.2) ∈ Q.support)).card := by
    apply Finset.card_bij (fun k _ => (-k.1, -k.2))
    · -- hi: Maps filtered elements to filtered elements
      intro k hk
      simp only [Finset.mem_filter, BBPolynomial.transpose, Finset.mem_image] at hk
      obtain ⟨⟨k', hk'_mem, hk'_eq⟩, hQ_mem⟩ := hk
      -- k ∈ p^T.support means ∃ k' ∈ p.support, (-k'.1, -k'.2) = k
      -- So k = (-k'.1, -k'.2), meaning -k = (k'.1, k'.2) = k'
      simp only [Finset.mem_filter]
      constructor
      · -- (-k.1, -k.2) ∈ p.support
        -- Since hk'_eq : (-k'.1, -k'.2) = k, we have -k = k'
        have : (-k.1, -k.2) = k' := by
          have := hk'_eq.symm
          ext
          · simp only; rw [this]; simp only [neg_neg]
          · simp only; rw [this]; simp only [neg_neg]
        rw [this]; exact hk'_mem
      · -- (-β.1 + (-k.1), -β.2 + (-k.2)) ∈ Q.support
        -- We have: (β.1 + k.1, β.2 + k.2) ∈ Q^T.support
        -- hQ_mem is of form ∃ x ∈ Q.support, (-x.1, -x.2) = (β.1 + k.1, β.2 + k.2)
        obtain ⟨⟨j1, j2⟩, hj_mem, hj_eq⟩ := hQ_mem
        -- hj_eq : (-j1, -j2) = (β.1 + k.1, β.2 + k.2)
        -- k = (-k'.1, -k'.2) from hk'_eq
        have hk_fst : k.1 = -k'.1 := by
          have := congrArg Prod.fst hk'_eq.symm
          simp only at this
          exact this
        have hk_snd : k.2 = -k'.2 := by
          have := congrArg Prod.snd hk'_eq.symm
          simp only at this
          exact this
        -- We need (j1, j2) ∈ Q.support and (j1, j2) = (-β.1 + k'.1, -β.2 + k'.2)
        -- From hj_eq: -j1 = β.1 + k.1 = β.1 - k'.1, so j1 = -β.1 + k'.1
        have hj_fst : -j1 = β.1 + k.1 := by
          have := congrArg Prod.fst hj_eq
          simp only at this
          exact this
        have hj_snd : -j2 = β.2 + k.2 := by
          have := congrArg Prod.snd hj_eq
          simp only at this
          exact this
        have hj1_eq : j1 = -β.1 + k'.1 := by
          have h1 : -j1 = β.1 + k.1 := hj_fst
          rw [hk_fst] at h1
          -- h1 : -j1 = β.1 + -k'.1
          have h2 : j1 = -(-j1) := (neg_neg j1).symm
          rw [h1] at h2
          simp only [neg_add, neg_neg] at h2
          exact h2
        have hj2_eq : j2 = -β.2 + k'.2 := by
          have h1 : -j2 = β.2 + k.2 := hj_snd
          rw [hk_snd] at h1
          -- h1 : -j2 = β.2 + -k'.2
          have h2 : j2 = -(-j2) := (neg_neg j2).symm
          rw [h1] at h2
          simp only [neg_add, neg_neg] at h2
          exact h2
        -- Result goal: (-β.1 + -k.1, -β.2 + -k.2) ∈ Q.support
        -- Since k = (-k'.1, -k'.2), -k.1 = k'.1 and -k.2 = k'.2
        have h_neg_k1 : -k.1 = k'.1 := by rw [hk_fst]; exact neg_neg k'.1
        have h_neg_k2 : -k.2 = k'.2 := by rw [hk_snd]; exact neg_neg k'.2
        rw [h_neg_k1, h_neg_k2]
        -- Now need: (-β.1 + k'.1, -β.2 + k'.2) ∈ Q.support
        rw [← hj1_eq, ← hj2_eq]
        exact hj_mem
    · -- Injective
      intro k₁ _ k₂ _ heq
      simp only [Prod.mk.injEq, neg_inj] at heq
      exact Prod.ext heq.1 heq.2
    · -- Surjective
      intro k' hk'
      simp only [Finset.mem_filter] at hk'
      use (-k'.1, -k'.2)
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_filter, BBPolynomial.transpose, Finset.mem_image]
        constructor
        · -- (-k'.1, -k'.2) ∈ p^T.support
          exact ⟨k', hk'.1, rfl⟩
        · -- (β.1 + -k'.1, β.2 + -k'.2) ∈ Q^T.support
          have h := hk'.2
          -- h : (-β.1 + k'.1, -β.2 + k'.2) ∈ Q.support
          exact ⟨(-β.1 + k'.1, -β.2 + k'.2), h, by simp only [neg_add, neg_neg]⟩
      · ext <;> simp only [neg_neg]
  exact h_eq

/-- **Parity Check Symmetry Lemma (parity_check_symmetry)**

    For a BB code with H_X = [A | B] and H_Z = [B^T | A^T]:

    If support S = (p, q) commutes with all X-checks (meaning H_X · (p,q)^T = 0),
    then the transposed support S^T = (q^T, p^T) commutes with all Z-checks
    (meaning H_Z · (q^T, p^T)^T = 0).

    **Proof**: For Z-check at index β, the commutation condition is:
    overlap(q^T, B^T, β) + overlap(p^T, A^T, β) = overlap(q, B, -β) + overlap(p, A, -β)
                                                = X-commutation at -β = 0 (mod 2)
-/
theorem parity_check_symmetry (C : BivariateBicycleCode ℓ m) (S : BBLogicalSupport ℓ m)
    (hX : ∀ α, XCommutationAt C S α) :
    ∀ β, ZCommutationAt C S.transpose β := by
  intro β
  simp only [ZCommutationAt, BBLogicalSupport.transpose]
  -- The left support of S^T is S.rightSupport^T
  -- The right support of S^T is S.leftSupport^T
  -- Z commutation: overlap(q^T, B^T, β) + overlap(p^T, A^T, β) ≡ 0
  -- Using overlap_transpose_eq: = overlap(q, B, -β) + overlap(p, A, -β)
  have h1 := overlap_transpose_eq S.rightSupport C.polyB β
  have h2 := overlap_transpose_eq S.leftSupport C.polyA β
  simp only [bbOverlapCount, transposeIdx] at h1 h2 ⊢
  rw [h1, h2]
  -- Now we need: overlap(S.right, B, -β) + overlap(S.left, A, -β) ≡ 0
  -- This is exactly X commutation at -β with swapped order
  specialize hX (-β.1, -β.2)
  simp only [XCommutationAt, bbOverlapCount] at hX
  -- hX says: overlap(left, A, -β) + overlap(right, B, -β) ≡ 0
  -- We need: overlap(right, B, -β) + overlap(left, A, -β) ≡ 0
  -- These are equal by commutativity of addition
  omega

/-- **Converse direction**: If S^T commutes with all Z-checks, then S commutes with all X-checks -/
theorem parity_check_symmetry_converse (C : BivariateBicycleCode ℓ m) (S : BBLogicalSupport ℓ m)
    (hZ : ∀ β, ZCommutationAt C S.transpose β) :
    ∀ α, XCommutationAt C S α := by
  intro α
  specialize hZ (-α.1, -α.2)
  simp only [ZCommutationAt, BBLogicalSupport.transpose, bbOverlapCount] at hZ
  have h1 := overlap_transpose_eq S.rightSupport C.polyB (-α.1, -α.2)
  have h2 := overlap_transpose_eq S.leftSupport C.polyA (-α.1, -α.2)
  simp only [transposeIdx, neg_neg, bbOverlapCount] at h1 h2
  rw [h1, h2] at hZ
  simp only [XCommutationAt, bbOverlapCount]
  omega

/-! ## Section 4: Commutation Preservation (Symplectic Inner Product) -/

/-- The symplectic inner product in F_2:
    ⟨X(p,q), Z(r,s)⟩ = (p · r + q · s) mod 2

    For BB codes, this computes whether an X-type and Z-type operator anticommute. -/
def bbSymplecticInnerProduct (SX SZ : BBLogicalSupport ℓ m) : ℕ :=
  (SX.leftSupport.support ∩ SZ.leftSupport.support).card +
  (SX.rightSupport.support ∩ SZ.rightSupport.support).card

/-- **Commutation Preservation Lemma (commutation_preserved)**

    The symplectic inner product is preserved under the transpose symmetry:
    ⟨X(p,q), Z(r,s)⟩ = ⟨X(s^T, r^T), Z(q^T, p^T)⟩

    **Proof**: Both evaluate to |p ∩ r| + |q ∩ s| (mod 2).

    For the transposed operators:
    - X(s^T, r^T) has left=s^T, right=r^T
    - Z(q^T, p^T) has left=q^T, right=p^T

    ⟨X(s^T, r^T), Z(q^T, p^T)⟩ = |s^T ∩ q^T| + |r^T ∩ p^T|

    Since transpose is a bijection: |s^T ∩ q^T| = |s ∩ q| = |q ∩ s|
    and |r^T ∩ p^T| = |r ∩ p| = |p ∩ r|
-/
theorem bbCommutation_preserved (SX SZ : BBLogicalSupport ℓ m) :
    bbSymplecticInnerProduct SX SZ % 2 =
    bbSymplecticInnerProduct
      ⟨SZ.rightSupport.transpose, SZ.leftSupport.transpose⟩
      SX.transpose % 2 := by
  simp only [bbSymplecticInnerProduct, BBLogicalSupport.transpose]
  -- LHS: |SX.left ∩ SZ.left| + |SX.right ∩ SZ.right|
  -- RHS: |SZ.right^T ∩ SX.right^T| + |SZ.left^T ∩ SX.left^T|
  -- For intersections: |A^T ∩ B^T| = |A ∩ B| since transpose is a bijection
  have h_inter_transpose : ∀ (A B : BBPolynomial ℓ m),
      (A.transpose.support ∩ B.transpose.support).card =
      (A.support ∩ B.support).card := by
    intros A B
    simp only [BBPolynomial.transpose]
    -- A^T ∩ B^T = image(neg, A ∩ B) by bijectivity
    have h_eq : (A.support.image (fun ab => (-ab.1, -ab.2))) ∩
                (B.support.image (fun ab => (-ab.1, -ab.2))) =
                (A.support ∩ B.support).image (fun ab => (-ab.1, -ab.2)) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a1, ha1, ha1_eq⟩, ⟨a2, ha2, ha2_eq⟩⟩
        have heq : a1 = a2 := by
          have : (-a1.1, -a1.2) = (-a2.1, -a2.2) := by rw [ha1_eq, ha2_eq]
          simp only [Prod.mk.injEq, neg_inj] at this
          exact Prod.ext this.1 this.2
        subst heq
        exact ⟨a1, ⟨ha1, ha2⟩, ha1_eq⟩
      · rintro ⟨a, ⟨ha1, ha2⟩, ha_eq⟩
        exact ⟨⟨a, ha1, ha_eq⟩, ⟨a, ha2, ha_eq⟩⟩
    rw [h_eq]
    exact Finset.card_image_of_injective _ neg_pair_injective
  rw [h_inter_transpose SZ.rightSupport SX.rightSupport,
      h_inter_transpose SZ.leftSupport SX.leftSupport]
  -- Now: |SX.left ∩ SZ.left| + |SX.right ∩ SZ.right| vs
  --      |SZ.right ∩ SX.right| + |SZ.left ∩ SX.left|
  have h1 : (SX.leftSupport.support ∩ SZ.leftSupport.support).card =
            (SZ.leftSupport.support ∩ SX.leftSupport.support).card := by
    rw [Finset.inter_comm]
  have h2 : (SX.rightSupport.support ∩ SZ.rightSupport.support).card =
            (SZ.rightSupport.support ∩ SX.rightSupport.support).card := by
    rw [Finset.inter_comm]
  omega

/-! ## Section 5: Main Symmetry Theorem -/

/-- A valid logical X operator for a BB code: commutes with all stabilizers -/
structure ValidLogicalXOp (C : BivariateBicycleCode ℓ m) where
  support : BBLogicalSupport ℓ m
  commutes_X : ∀ α, XCommutationAt C support α
  commutes_Z : ∀ β, ZCommutationAt C support β

/-- A valid logical Z operator for a BB code: commutes with all stabilizers -/
structure ValidLogicalZOp (C : BivariateBicycleCode ℓ m) where
  support : BBLogicalSupport ℓ m
  commutes_X : ∀ α, XCommutationAt C support α
  commutes_Z : ∀ β, ZCommutationAt C support β

/-- **Main Symmetry Theorem (logical_symmetry_XtoZ)**

    For a BB code C with H_X = [A | B] and H_Z = [B^T | A^T]:

    If X(p, q) is a valid logical X operator (commutes with all stabilizers),
    then Z(q^T, p^T) is a valid logical Z operator.

    This is the core content of Proposition 4: the symmetry (p,q) ↦ (q^T, p^T)
    maps logical X operators to corresponding logical Z operators.
-/
def logical_symmetry_XtoZ (C : BivariateBicycleCode ℓ m)
    (opX : ValidLogicalXOp C) : ValidLogicalZOp C where
  support := opX.support.transpose
  commutes_X := by
    -- Need to show S^T commutes with X-checks
    -- S^T.transpose = S commutes with Z-checks (opX.commutes_Z)
    -- By parity_check_symmetry_converse applied to S^T:
    -- if S^T^T commutes with Z-checks, then S^T commutes with X-checks
    apply parity_check_symmetry_converse C opX.support.transpose
    intro β
    simp only [BBLogicalSupport.transpose_transpose]
    exact opX.commutes_Z β
  commutes_Z := by
    -- Need to show S^T commutes with Z-checks
    -- S commutes with X-checks (opX.commutes_X)
    -- By parity_check_symmetry applied to S:
    -- if S commutes with X-checks, then S^T commutes with Z-checks
    have h : ∀ α, XCommutationAt C opX.support α := opX.commutes_X
    exact parity_check_symmetry C opX.support h

/-- **Converse**: If Z(q^T, p^T) is valid, then X(p, q) is valid -/
def logical_symmetry_ZtoX (C : BivariateBicycleCode ℓ m)
    (opZ : ValidLogicalZOp C) : ValidLogicalXOp C where
  support := opZ.support.transpose
  commutes_X := by
    apply parity_check_symmetry_converse C opZ.support.transpose
    intro β
    simp only [BBLogicalSupport.transpose_transpose]
    exact opZ.commutes_Z β
  commutes_Z := by
    have h : ∀ α, XCommutationAt C opZ.support α := opZ.commutes_X
    exact parity_check_symmetry C opZ.support h

/-- The symmetry is an involution: applying it twice returns the original operator -/
theorem logical_symmetry_involution (C : BivariateBicycleCode ℓ m)
    (opX : ValidLogicalXOp C) :
    (logical_symmetry_ZtoX C (logical_symmetry_XtoZ C opX)).support = opX.support := by
  simp only [logical_symmetry_ZtoX, logical_symmetry_XtoZ, BBLogicalSupport.transpose_transpose]

/-- The symmetry preserves weight -/
theorem logical_symmetry_preserves_weight (C : BivariateBicycleCode ℓ m)
    (opX : ValidLogicalXOp C) :
    (logical_symmetry_XtoZ C opX).support.weight = opX.support.weight := by
  simp only [logical_symmetry_XtoZ, BBLogicalSupport.weight, BBLogicalSupport.transpose]
  simp only [BBPolynomial.numTerms, BBPolynomial.transpose]
  rw [Finset.card_image_of_injective _ neg_pair_injective,
      Finset.card_image_of_injective _ neg_pair_injective]
  ring

/-- The transpose map on supports is a bijection -/
theorem support_transpose_bijective :
    Function.Bijective (BBLogicalSupport.transpose : BBLogicalSupport ℓ m → BBLogicalSupport ℓ m) := by
  constructor
  · -- Injective
    intro S₁ S₂ h
    have h' := congrArg BBLogicalSupport.transpose h
    simp only [BBLogicalSupport.transpose_transpose] at h'
    exact h'
  · -- Surjective
    intro S
    use S.transpose
    exact BBLogicalSupport.transpose_transpose S

/-! ## Section 6: Gauging Symmetry -/

/-- The type of a gauging measurement target: X-type or Z-type -/
inductive GaugingTargetType where
  | X : GaugingTargetType
  | Z : GaugingTargetType
  deriving DecidableEq

/-- A gauging target specifies what logical operator to measure -/
structure GaugingTarget (ℓ m : ℕ) [NeZero ℓ] [NeZero m] where
  support : BBLogicalSupport ℓ m
  targetType : GaugingTargetType
  deriving DecidableEq

/-- The transposed gauging target: swap X↔Z and transpose support -/
def GaugingTarget.transpose (T : GaugingTarget ℓ m) : GaugingTarget ℓ m where
  support := T.support.transpose
  targetType := match T.targetType with
    | GaugingTargetType.X => GaugingTargetType.Z
    | GaugingTargetType.Z => GaugingTargetType.X

/-- Double transpose returns the original target -/
theorem GaugingTarget.transpose_transpose (T : GaugingTarget ℓ m) :
    T.transpose.transpose = T := by
  cases T with
  | mk s t =>
    simp only [transpose, BBLogicalSupport.transpose_transpose]
    cases t <;> rfl

/-- **Gauging Symmetry Theorem**

    A gauging graph construction for measuring X̄_α = X(αf, 0) can be adapted to
    measure Z̄'_α = Z(0, αf^T) by swapping left and right qubits.

    More precisely: if T is a gauging target with X-type and left-only support,
    then T^T is a gauging target with Z-type and right-only support. -/
theorem gauging_symmetry (_C : BivariateBicycleCode ℓ m) (f : BBPolynomial ℓ m)
    (α : Fin ℓ × Fin m) :
    let target_X := GaugingTarget.mk (BBLogicalSupport.leftOnly (f.mulByMonomial α))
                                     GaugingTargetType.X
    let target_Z := target_X.transpose
    target_Z.support = BBLogicalSupport.rightOnly ((f.mulByMonomial α).transpose) ∧
    target_Z.targetType = GaugingTargetType.Z := by
  constructor
  · simp only [GaugingTarget.transpose, BBLogicalSupport.transpose_leftOnly]
  · rfl

/-- The transposed target has swapped type -/
theorem GaugingTarget.transpose_swaps_type (T : GaugingTarget ℓ m) :
    (T.transpose.targetType = GaugingTargetType.X ↔ T.targetType = GaugingTargetType.Z) ∧
    (T.transpose.targetType = GaugingTargetType.Z ↔ T.targetType = GaugingTargetType.X) := by
  constructor <;> (simp only [transpose]; cases T.targetType <;> simp)

/-! ## Section 7: Additional Properties -/

/-- The weight of a support is preserved under transpose -/
theorem support_weight_transpose (S : BBLogicalSupport ℓ m) :
    S.transpose.weight = S.weight := by
  simp only [BBLogicalSupport.weight, BBLogicalSupport.transpose, BBPolynomial.numTerms]
  simp only [BBPolynomial.transpose]
  rw [Finset.card_image_of_injective _ neg_pair_injective,
      Finset.card_image_of_injective _ neg_pair_injective]
  ring

/-- Zero support has zero weight -/
@[simp]
theorem zero_weight : (BBLogicalSupport.zero : BBLogicalSupport ℓ m).weight = 0 := by
  simp only [BBLogicalSupport.weight, BBLogicalSupport.zero, BBPolynomial.numTerms,
             BBPolynomial.zero, Finset.card_empty, add_zero]

/-- Left-only support has weight equal to polynomial terms -/
theorem leftOnly_weight (p : BBPolynomial ℓ m) :
    (BBLogicalSupport.leftOnly p).weight = p.numTerms := by
  simp only [BBLogicalSupport.weight, BBLogicalSupport.leftOnly, BBPolynomial.numTerms,
             BBPolynomial.zero, Finset.card_empty, add_zero]

/-- Right-only support has weight equal to polynomial terms -/
theorem rightOnly_weight (q : BBPolynomial ℓ m) :
    (BBLogicalSupport.rightOnly q).weight = q.numTerms := by
  simp only [BBLogicalSupport.weight, BBLogicalSupport.rightOnly, BBPolynomial.numTerms,
             BBPolynomial.zero, Finset.card_empty, zero_add]

end QEC
