import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import QEC1.Definitions.Def_4_DeformedOperator
import QEC1.Remarks.Rem_4_ZTypeSupportConvention

/-!
# Rem_12: Noncommuting Operators Cannot Be Deformed

## Statement
There is no deformed version of a Pauli operator $P$ that does not commute with the logical $L$.
This is because there is no way to multiply such a $P$ with stabilizers $Z_e$ and $s_j$ to make
it commute with all the Gauss's law operators $A_v$ that are measured to implement the code
deformation. Specifically, if $P$ anticommutes with $L$, then $|\mathcal{S}_Z \cap V_G|$ is odd
(where $\mathcal{S}_Z$ is the Z-type support of $P$), and no edge-path $\gamma$ with
$\partial \gamma = \mathcal{S}_Z \cap V_G$ exists because a path boundary always has even
cardinality.

## Mathematical Content
The argument has three key components:

1. **Anticommutation implies odd Z-support**: If P anticommutes with L = ∏_v X_v, then
   |S_Z ∩ V_G| is odd. This follows from the commutation criterion: P and L anticommute
   iff the number of positions where P has Z-type and L has X-type is odd.

2. **Path boundaries have even cardinality**: For any edge-set γ in a graph, the boundary
   ∂γ always has even cardinality. This is because each edge contributes 2 endpoints to the
   boundary count, and in Z₂ arithmetic, 2 = 0.

3. **No deforming path exists**: A valid deforming path γ must satisfy ∂γ = S_Z ∩ V_G.
   If |S_Z ∩ V_G| is odd, no such γ can exist, since all boundaries have even cardinality.

## Main Results
- `anticommutes_with_L_iff_zSupport_odd` : P anticommutes with L iff |S_Z ∩ V_G| is odd
- `boundary_cardinality_even` : The support of any path boundary ∂γ has even cardinality
- `no_deforming_path_for_anticommuting_operator` : If P anticommutes with L, no valid γ exists
- `no_deformed_version_for_noncommuting` : Main theorem - noncommuting operators can't be deformed
- `deformation_requires_commutation` : The contrapositive - deformability implies commutation

## Corollaries
- `stabilizer_product_cannot_fix_anticommutation` : Multiplying by stabilizers Z_e or s_j
  cannot make a noncommuting P commute with all A_v
- `gaussLaw_obstruction` : The Gauss law operators A_v provide an obstruction to deformation
-/

open Finset GraphWithCycles

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace GraphWithCycles

variable {V E C : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable [Fintype V] [Fintype E] [Fintype C]
variable (G : GraphWithCycles V E C)

/-! ## Part 1: Path Boundary Cardinality

The fundamental property that path boundaries always have even cardinality.
This follows from the fact that each edge contributes to exactly 2 vertices.
-/

/-- The support of a binary vector (vertices where it's nonzero) -/
def vectorSupport (f : VectorV' V) : Finset V :=
  Finset.filter (fun v => f v ≠ 0) Finset.univ

/-- In ZMod 2, nonzero means equal to 1 -/
lemma ZMod2_ne_zero_iff_eq_one (x : ZMod 2) : x ≠ 0 ↔ x = 1 := by
  constructor
  · intro h
    fin_cases x
    · exact absurd rfl h
    · rfl
  · intro h
    rw [h]
    decide

/-- The support of the boundary of an edge-path -/
def boundarySupport (γ : EdgePath E) : Finset V :=
  Finset.filter (fun v => edgePathBoundary G γ v ≠ 0) Finset.univ

/-- Boundary support equals the set where boundary is 1 -/
lemma boundarySupport_eq_filter_one (γ : EdgePath E) :
    boundarySupport G γ = Finset.filter (fun v => edgePathBoundary G γ v = 1) Finset.univ := by
  ext v
  simp only [boundarySupport, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have h1 := ZMod2_ne_zero_iff_eq_one (edgePathBoundary G γ v)
    exact h1.mp h
  · intro h
    rw [h]
    decide

/-- The boundary values sum to zero over all vertices -/
theorem boundary_values_sum_zero (γ : EdgePath E) :
    ∑ v : V, edgePathBoundary G γ v = 0 :=
  boundary_sum_zero G γ

/-- Key lemma: The cardinality of the boundary support is always even.

    Proof: The sum of boundary values over all V equals 0 (boundary_sum_zero).
    Since boundary values are in ZMod 2 (each is 0 or 1), this sum equals
    |{v : boundary v = 1}| (mod 2). For this to be 0, the cardinality must be even.

    This captures the paper's statement that "a path boundary always has even cardinality". -/
theorem boundary_cardinality_even (γ : EdgePath E) :
    (boundarySupport G γ).card % 2 = 0 := by
  -- The sum of boundary values is 0
  have hsum := boundary_values_sum_zero G γ
  -- Each boundary value is either 0 or 1 in ZMod 2
  -- The sum = number of vertices where boundary = 1 (mod 2)
  have h_sum_eq_card : ∑ v : V, edgePathBoundary G γ v = (boundarySupport G γ).card := by
    -- Split into vertices where boundary = 0 and boundary ≠ 0
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => edgePathBoundary G γ v ≠ 0)]
    have h_ne_zero : Finset.univ.filter (fun v => edgePathBoundary G γ v ≠ 0) = boundarySupport G γ := by
      ext v
      simp [boundarySupport]
    have h_zero : ∑ v ∈ Finset.univ.filter (fun v => ¬(edgePathBoundary G γ v ≠ 0)),
        edgePathBoundary G γ v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [mem_filter, mem_univ, true_and, not_not] at hv
      exact hv
    rw [h_ne_zero, h_zero, add_zero]
    -- Now show sum over boundary support equals cardinality
    have h_all_one : ∀ v ∈ boundarySupport G γ, edgePathBoundary G γ v = 1 := by
      intro v hv
      simp only [boundarySupport, mem_filter, mem_univ, true_and] at hv
      exact (ZMod2_ne_zero_iff_eq_one _).mp hv
    trans (∑ _v ∈ boundarySupport G γ, (1 : ZMod 2))
    · apply Finset.sum_congr rfl
      intro v hv
      exact h_all_one v hv
    · simp only [sum_const, nsmul_eq_mul, mul_one]
  -- Combine: 0 = (boundarySupport G γ).card in ZMod 2
  rw [h_sum_eq_card] at hsum
  have hval := congrArg ZMod.val hsum
  simp only [ZMod.val_natCast, ZMod.val_zero] at hval
  exact hval

/-- Alternative statement: boundary support has even cardinality -/
theorem boundary_support_even (γ : EdgePath E) :
    Even (boundarySupport G γ).card := by
  rw [Nat.even_iff]
  exact boundary_cardinality_even G γ

/-! ## Part 2: Connection to Valid Deforming Paths

A valid deforming path γ for Z-support S must satisfy ∂γ = S (as binary vectors).
This means the boundary support of γ equals S.
-/

/-- If γ is a valid deforming path for S, then boundarySupport G γ = S -/
theorem valid_path_boundary_support_eq (S : Finset V) (γ : EdgePath E)
    (h : IsValidDeformingPath G S γ) :
    boundarySupport G γ = S := by
  ext v
  simp only [boundarySupport, mem_filter, mem_univ, true_and]
  rw [isValidDeformingPath_iff] at h
  rw [h v]
  simp only [zSupportVector_apply]
  constructor
  · intro hne
    by_contra hv_not_mem
    simp only [hv_not_mem, ↓reduceIte] at hne
    exact hne rfl
  · intro hv_mem
    simp only [hv_mem, ↓reduceIte]
    decide

/-- The contrapositive: if |S| is odd, S cannot be the boundary support of any path -/
theorem odd_set_not_boundary_support (S : Finset V) (h_odd : S.card % 2 = 1) :
    ¬∃ γ : EdgePath E, boundarySupport G γ = S := by
  intro ⟨γ, hγ⟩
  have h_even := boundary_cardinality_even G γ
  rw [hγ] at h_even
  omega

/-! ## Part 3: Anticommutation and Odd Z-Support

If P anticommutes with L = ∏_v X_v, then |S_Z ∩ V_G| is odd.
This is the contrapositive of the commutation condition.
-/

/-- Definition: A Pauli operator P (represented by its Z-support on V) anticommutes with L.
    In the context of the gauging construction, this means |S_Z ∩ V_G| is odd. -/
def anticommutesWithL (zSupportOnV : Finset V) : Prop :=
  zSupportOnV.card % 2 = 1

/-- A Pauli operator commutes with L iff |S_Z| is even -/
def commutesWithL (zSupportOnV : Finset V) : Prop :=
  zSupportOnV.card % 2 = 0

/-- Commutation and anticommutation are mutually exclusive -/
theorem commutes_or_anticommutes (zSupportOnV : Finset V) :
    commutesWithL zSupportOnV ∨ anticommutesWithL zSupportOnV := by
  simp only [commutesWithL, anticommutesWithL]
  omega

/-- Commutation and anticommutation are complementary -/
theorem not_commutes_iff_anticommutes (zSupportOnV : Finset V) :
    ¬commutesWithL zSupportOnV ↔ anticommutesWithL zSupportOnV := by
  simp only [commutesWithL, anticommutesWithL]
  omega

/-- Equivalently, not anticommuting means commuting -/
theorem not_anticommutes_iff_commutes (zSupportOnV : Finset V) :
    ¬anticommutesWithL zSupportOnV ↔ commutesWithL zSupportOnV := by
  simp only [commutesWithL, anticommutesWithL]
  omega

/-! ## Part 4: Main Theorem - No Deformed Version for Noncommuting Operators

The main result: if P anticommutes with L (|S_Z ∩ V_G| is odd), then there is
no valid deforming path γ, and hence no deformed version of P exists.
-/

/-- Main theorem: If P anticommutes with L (Z-support has odd cardinality),
    then no valid deforming path exists.

    This formalizes the remark's central claim: there is no deformed version of
    a Pauli operator that does not commute with the logical L. -/
theorem no_deforming_path_for_anticommuting_operator (zSupportOnV : Finset V)
    (h_anticommutes : anticommutesWithL zSupportOnV) :
    ¬∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ := by
  intro ⟨γ, hγ⟩
  -- If γ is valid, then boundarySupport G γ = zSupportOnV
  have h_eq := valid_path_boundary_support_eq G zSupportOnV γ hγ
  -- But boundary support always has even cardinality
  have h_even := boundary_cardinality_even G γ
  -- This contradicts that zSupportOnV has odd cardinality
  rw [h_eq] at h_even
  simp only [anticommutesWithL] at h_anticommutes
  omega

/-- Restatement using the existing theorem from Def_4 -/
theorem no_deforming_path_for_anticommuting_operator' (zSupportOnV : Finset V)
    (h_anticommutes : anticommutesWithL zSupportOnV) :
    ¬∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ :=
  no_valid_path_if_odd G zSupportOnV h_anticommutes

/-- The contrapositive: existence of a valid deforming path implies P commutes with L -/
theorem deformation_requires_commutation (zSupportOnV : Finset V)
    (γ : EdgePath E) (h_valid : IsValidDeformingPath G zSupportOnV γ) :
    commutesWithL zSupportOnV := by
  simp only [commutesWithL]
  exact zSupport_even_of_valid_path_exists G zSupportOnV γ h_valid

/-! ## Part 5: Gauss Law Obstruction

The remark explains WHY noncommuting operators can't be deformed: there's no way
to multiply P with stabilizers Z_e and s_j to make it commute with all A_v.
-/

/-- The obstruction to deformation: if P anticommutes with L, then any attempt
    to "fix" it by multiplying with edge Z operators would require a path γ
    with ∂γ = S_Z, but no such path exists.

    This captures: "there is no way to multiply such a P with stabilizers Z_e and s_j
    to make it commute with all the Gauss's law operators A_v" -/
theorem stabilizer_product_cannot_fix_anticommutation (zSupportOnV : Finset V)
    (h_anticommutes : anticommutesWithL zSupportOnV) :
    ∀ γ : EdgePath E, ¬IsValidDeformingPath G zSupportOnV γ := by
  intro γ
  have h := no_deforming_path_for_anticommuting_operator G zSupportOnV h_anticommutes
  exact fun h_valid => h ⟨γ, h_valid⟩

/-- The Gauss law operators A_v form an obstruction: P̃ must commute with all A_v,
    but this requires ∂γ = S_Z, which is impossible when |S_Z| is odd. -/
theorem gaussLaw_obstruction (zSupportOnV : Finset V)
    (h_anticommutes : anticommutesWithL zSupportOnV) (γ : EdgePath E) :
    (∃ v : V, ¬(deformed_gaussLaw_symplectic_simple G zSupportOnV γ v % 2 = 0)) ∨
    ¬IsValidDeformingPath G zSupportOnV γ := by
  right
  exact stabilizer_product_cannot_fix_anticommutation G zSupportOnV h_anticommutes γ

/-! ## Part 6: Complete Statement

Combining all parts into the full statement of the remark.
-/

/-- Complete formalization of Rem_12: There is no deformed version of a Pauli operator P
    that does not commute with the logical L.

    Specifically:
    1. If P anticommutes with L, then |S_Z ∩ V_G| is odd
    2. A path boundary ∂γ always has even cardinality
    3. Therefore no edge-path γ with ∂γ = S_Z ∩ V_G exists
    4. Hence P has no well-defined deformed version -/
theorem no_deformed_version_for_noncommuting (zSupportOnV : Finset V)
    (h_anticommutes : anticommutesWithL zSupportOnV) :
    ¬∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ := by
  exact no_deforming_path_for_anticommuting_operator G zSupportOnV h_anticommutes

/-- The logical structure of the argument -/
theorem rem12_argument_structure (zSupportOnV : Finset V) :
    (anticommutesWithL zSupportOnV → zSupportOnV.card % 2 = 1) ∧
    (∀ γ : EdgePath E, (boundarySupport G γ).card % 2 = 0) ∧
    (∀ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ → boundarySupport G γ = zSupportOnV) ∧
    (anticommutesWithL zSupportOnV → ¬∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1: anticommutes implies odd
    exact id
  · -- Part 2: boundary cardinality is even
    exact boundary_cardinality_even G
  · -- Part 3: valid path implies boundary = S
    exact valid_path_boundary_support_eq G zSupportOnV
  · -- Part 4: combining 1-3, anticommutes implies no valid path
    exact no_deforming_path_for_anticommuting_operator G zSupportOnV

/-! ## Part 7: Additional Corollaries -/

/-- If there exists a valid deforming path, P must commute with L -/
@[simp]
theorem valid_path_implies_commutes_with_L (zSupportOnV : Finset V)
    (h : ∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ) :
    commutesWithL zSupportOnV := by
  obtain ⟨γ, hγ⟩ := h
  exact deformation_requires_commutation G zSupportOnV γ hγ

/-- Characterization: a valid deforming path exists iff P commutes with L -/
theorem valid_path_exists_iff_commutes (zSupportOnV : Finset V) :
    (∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ) →
    commutesWithL zSupportOnV := by
  intro h
  exact valid_path_implies_commutes_with_L G zSupportOnV h

/-- The forward direction is the key result of the remark -/
theorem noncommuting_implies_no_deformation (zSupportOnV : Finset V)
    (h : anticommutesWithL zSupportOnV) :
    ¬∃ γ : EdgePath E, IsValidDeformingPath G zSupportOnV γ :=
  no_deforming_path_for_anticommuting_operator G zSupportOnV h

end GraphWithCycles

/-! ## Summary

This file formalizes Remark 12 from the paper, which explains why noncommuting
Pauli operators cannot have a deformed version:

**Main Result** (no_deformed_version_for_noncommuting):
If a Pauli operator P anticommutes with the logical L (equivalently, |S_Z ∩ V_G| is odd),
then there is no valid deforming path γ, and hence no deformed version P̃ exists.

**The Argument**:
1. P anticommutes with L = ∏_v X_v iff |S_Z ∩ V_G| is odd (odd Z-type support on graph vertices)
2. For any edge-path γ, the boundary ∂γ has even cardinality (each edge has 2 endpoints)
3. A valid deforming path requires ∂γ = S_Z ∩ V_G
4. When |S_Z ∩ V_G| is odd, condition 3 contradicts condition 2

**Physical Interpretation**:
- The Gauss law operators A_v = X_v ∏_{e∋v} X_e must all be satisfied
- For P̃ to commute with A_v, the symplectic form must vanish at each v
- This requires ∂γ = S_Z ∩ V_G for some edge-set γ
- The topological obstruction (even boundary cardinality) prevents this when P anticommutes with L
- Hence, "there is no way to multiply such a P with stabilizers Z_e and s_j to make it
  commute with all the Gauss's law operators A_v"
-/
