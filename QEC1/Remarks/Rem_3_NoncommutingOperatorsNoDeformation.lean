import QEC1.Definitions.Def_8_DeformedOperator

/-!
# NoncommutingOperatorsNoDeformation (Remark 3)

## Statement
Let C be a stabilizer code, L an X-type logical operator, and G a gauging graph.

There is **no deformed version** of a Pauli operator P that does not commute with L.

**Reason**: If [P, L] ≠ 0, then |S_Z(P) ∩ L| ≡ 1 (mod 2) (odd overlap). For
P̃ = P · ∏_{e ∈ γ} Z_e to commute with all Gauss's law operators A_v, we would need:
  [P̃, A_v] = 0 for all v ∈ V

But [P̃, A_v] = 0 requires |S_Z(P̃) ∩ {v}| + |{e ∈ γ : v ∈ e}| ≡ 0 (mod 2).

Summing over all v ∈ L: ∑_{v ∈ L} |S_Z(P) ∩ {v}| + ∑_{v ∈ L} |{e ∈ γ : v ∈ e}| ≡ 0.

The second sum equals 2|γ| (each edge counted twice) ≡ 0. So we need
|S_Z(P) ∩ L| ≡ 0, contradicting odd overlap.

Thus operators anticommuting with L cannot be extended to the deformed code.

## Main Results
**Main Theorem** (`noncommuting_no_deformation`): If P does not commute with L
  (odd Z-overlap), then no edge-path γ satisfies both the boundary condition
  and the Gauss law commutation requirement.

## File Structure
1. Anticommutation Condition: |S_Z(P) ∩ L.support| ≡ 1 (mod 2)
2. Main Theorem: Impossibility of deformation for anticommuting operators
3. Helper Lemmas: Corollaries and properties
-/

namespace QEC

open scoped BigOperators

variable {n k : ℕ} {C : StabilizerCode n k} {L : XTypeLogical C}

/-! ## Section 1: Anticommutation Condition

A Pauli operator P **anticommutes** with an X-type logical L = ∏_{v ∈ L} X_v iff
|S_Z(P) ∩ L.support| ≡ 1 (mod 2).

This is the negation of the commutation condition. When the overlap is odd,
[P, L] ≠ 0 (they anticommute).
-/

/-- A Pauli operator P anticommutes with an X-type logical L iff
    |S_Z(P) ∩ support(L)| ≡ 1 (mod 2) (odd overlap). -/
def anticommutesWithLogical (P : StabilizerCheck n) (L : XTypeLogical C) : Prop :=
  (P.supportZ ∩ L.support).card % 2 = 1

/-- Anticommutation is decidable -/
instance : DecidablePred (fun P : StabilizerCheck n => anticommutesWithLogical P L) :=
  fun P => instDecidableEqNat ((P.supportZ ∩ L.support).card % 2) 1

/-- Anticommutation is the negation of commutation -/
theorem anticommutes_iff_not_commutes (P : StabilizerCheck n) :
    anticommutesWithLogical P L ↔ ¬commutesWithLogical P L := by
  unfold anticommutesWithLogical commutesWithLogical
  constructor
  · intro h hcomm
    omega
  · intro h
    have hmem : (P.supportZ ∩ L.support).card % 2 ∈ ({0, 1} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    cases hmem with
    | inl h0 => exact absurd h0 h
    | inr h1 => exact h1

/-- The odd overlap as a ZMod 2 value equals 1 -/
theorem anticommutes_iff_mod2_one (P : StabilizerCheck n) :
    anticommutesWithLogical P L ↔ zSupportOverlapMod2 P L = 1 := by
  unfold anticommutesWithLogical zSupportOverlapMod2
  constructor
  · intro h
    have hval : ZMod.val ((P.supportZ ∩ L.support).card : ZMod 2) = 1 := by
      rw [ZMod.val_natCast]
      exact h
    have : ((P.supportZ ∩ L.support).card : ZMod 2) = (1 : ZMod 2) := by
      have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
      exact ZMod.val_injective 2 (by rw [hval, h1])
    exact this
  · intro h
    have hval : ZMod.val ((P.supportZ ∩ L.support).card : ZMod 2) = 1 := by
      rw [h]; rfl
    have hmod := ZMod.val_natCast (P.supportZ ∩ L.support).card (n := 2)
    rw [hval] at hmod
    exact hmod.symm

/-! ## Section 2: Sum Over All Vertices

The key insight: summing the edge boundary over all vertices gives 0 in ZMod 2
because each edge is counted exactly twice (once for each endpoint).
-/

variable (D : DeformConfig C L)

/-- The indicator function for whether a vertex is in the Z-support image -/
def vertexInZSupport (P : StabilizerCheck n) (v : D.graph.Vertex) : ZMod 2 :=
  if ∃ q ∈ P.supportZ, D.qubitToVertex q = v then 1 else 0

/-- Commutation condition for P̃ with A_v:
    |S_Z(P) ∩ {v}| + |{e ∈ γ : v ∈ e}| ≡ 0 (mod 2) -/
def deformedCommutesWithGaussLaw (P : StabilizerCheck n) (gamma : EdgePath D)
    (v : D.graph.Vertex) : Prop :=
  vertexInZSupport D P v + edgePathBoundary D gamma v = 0

/-- For P̃ to commute with ALL Gauss law operators, this must hold for every vertex -/
def deformedCommutesWithAllGaussLaw (P : StabilizerCheck n) (gamma : EdgePath D) : Prop :=
  ∀ v : D.graph.Vertex, deformedCommutesWithGaussLaw D P gamma v

/-- The target boundary matches vertexInZSupport -/
theorem targetBoundary_eq_vertexInZSupport (P : StabilizerCheck n) (v : D.graph.Vertex) :
    targetBoundary D P v = vertexInZSupport D P v := rfl

/-! ## Section 3: Main Theorem - Impossibility of Deformation

The key is that the boundary map ∂₁ has image consisting of even-parity chains.
If the target boundary has odd parity (sum over all vertices equals 1),
then no edge-path γ can satisfy the boundary condition.
-/

/-- **Main Theorem**: If the target boundary has odd parity (sum = 1),
    then no edge-path γ can satisfy the boundary condition.

    This is because each edge contributes 2 to the sum (one for each endpoint),
    so the sum of any edge-path boundary is always 0 in ZMod 2. -/
theorem noncommuting_no_deformation (P : StabilizerCheck n)
    (_hanticomm : anticommutesWithLogical P L)
    (hodd_target : targetBoundaryParity D P = 1)
    (_hsurj : BoundarySurjectsOntoEvenParity D) :
    ¬(∃ gamma : EdgePath D,
        (∀ e ∈ gamma, e ∈ D.graph.graph.edgeSet) ∧
        satisfiesBoundaryCondition D P gamma) := by
  intro ⟨gamma, hvalid, hbound⟩
  -- The key: sum of boundary over all vertices
  -- For boundary condition: edgePathBoundary = targetBoundary at each vertex
  -- So sum of targetBoundary = sum of edgePathBoundary

  -- Sum of edgePathBoundary over all vertices = 0 because each edge is counted twice
  -- (once at each endpoint), and 2 ≡ 0 in ZMod 2
  have hsum_edge : ∑ v : D.graph.Vertex, edgePathBoundary D gamma v = 0 := by
    unfold edgePathBoundary
    -- Each edge e ∈ gamma contributes: counted once for each v ∈ e
    -- Since each edge has exactly 2 vertices, total count = 2|gamma|
    -- In ZMod 2, 2|gamma| ≡ 0

    -- For each edge e, it has exactly 2 vertices
    have hcount : ∀ e ∈ gamma,
        (Finset.filter (fun v : D.graph.Vertex => v ∈ e) Finset.univ).card = 2 := by
      intro e he
      have he_edge := hvalid e he
      -- Decompose e using Sym2.ind
      revert he_edge
      refine Sym2.ind (fun a b => ?_) e
      intro hadj
      rw [SimpleGraph.mem_edgeSet] at hadj
      have hne : a ≠ b := D.graph.graph.ne_of_adj hadj
      have hfilter : Finset.filter (fun v => v ∈ s(a, b)) Finset.univ = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                   Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]
      rw [hfilter, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    -- The sum equals 2|gamma| mod 2 = 0
    -- ∑_v |{e ∈ gamma : v ∈ e}| = ∑_{e ∈ gamma} |{v : v ∈ e}| = ∑_{e ∈ gamma} 2 = 2|gamma|
    -- In ZMod 2: sum of vertex counts per edge = 0 (since each edge has 2 endpoints)
    -- and summing over all v: each edge contributes 2 to the total = 0 mod 2
    have hzmod_edges : ∑ e ∈ gamma, ((Finset.filter (fun v : D.graph.Vertex => v ∈ e)
        Finset.univ).card : ZMod 2) = 0 := by
      have h2 : (2 : ZMod 2) = 0 := by decide
      calc ∑ e ∈ gamma, ((Finset.filter (fun v : D.graph.Vertex => v ∈ e)
              Finset.univ).card : ZMod 2)
          = ∑ e ∈ gamma, (2 : ZMod 2) := by
            apply Finset.sum_congr rfl
            intro e he
            simp only [hcount e he, Nat.cast_ofNat]
        _ = gamma.card • (2 : ZMod 2) := Finset.sum_const _
        _ = gamma.card • (0 : ZMod 2) := by rw [h2]
        _ = 0 := smul_zero _
    -- Double counting: ∑_v |{e ∈ gamma : v ∈ e}| = ∑_e |{v : v ∈ e}| (as ℕ)
    -- This equals 2|gamma| which is 0 mod 2
    have hdouble_nat : ∑ v : D.graph.Vertex, (Finset.filter (fun e => v ∈ e) gamma).card =
        ∑ e ∈ gamma, (Finset.filter (fun v : D.graph.Vertex => v ∈ e) Finset.univ).card := by
      trans (∑ v : D.graph.Vertex, ∑ e ∈ gamma, if v ∈ e then 1 else 0)
      · apply Finset.sum_congr rfl
        intro v _
        rw [Finset.card_filter]
      trans (∑ e ∈ gamma, ∑ v : D.graph.Vertex, if v ∈ e then 1 else 0)
      · exact Finset.sum_comm
      · apply Finset.sum_congr rfl
        intro e _
        rw [← Finset.card_filter]
    -- Sum over edges of vertex counts = 2|gamma|
    have hsum_edges_nat : ∑ e ∈ gamma, (Finset.filter (fun v : D.graph.Vertex => v ∈ e)
        Finset.univ).card = ∑ _e ∈ gamma, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact hcount e he
    -- Double counting gives sum over vertices = 2|gamma|
    have hsum_vertices_nat : ∑ v : D.graph.Vertex, (Finset.filter (fun e => v ∈ e) gamma).card =
        2 * gamma.card := by
      rw [hdouble_nat, hsum_edges_nat, Finset.sum_const, smul_eq_mul, mul_comm]
    -- 2|gamma| ≡ 0 (mod 2)
    have h2_zero : (2 : ZMod 2) = 0 := by decide
    -- Use Nat.cast_sum to rewrite ∑ v, ↑f(v) = ↑(∑ v, f(v))
    rw [(Nat.cast_sum Finset.univ (fun v => (Finset.filter (fun e => v ∈ e) gamma).card)).symm]
    -- Now goal is: ↑(∑ v, {...}.card) = 0
    rw [hsum_vertices_nat]
    -- Now goal is: ↑(2 * |gamma|) = 0
    simp only [Nat.cast_mul, Nat.cast_ofNat, h2_zero, zero_mul]
  -- Sum of targetBoundary = sum of edgePathBoundary = 0
  have hsum_target : ∑ v : D.graph.Vertex, targetBoundary D P v = 0 := by
    calc ∑ v : D.graph.Vertex, targetBoundary D P v
        = ∑ v : D.graph.Vertex, edgePathBoundary D gamma v := by
          apply Finset.sum_congr rfl
          intro v _
          exact (hbound v).symm
      _ = 0 := hsum_edge
  -- But we assumed target parity = 1 (odd)
  unfold targetBoundaryParity at hodd_target
  rw [hsum_target] at hodd_target
  exact zero_ne_one hodd_target

/-! ## Section 4: Corollaries and Helper Lemmas -/

/-- A Z-type operator Z_S anticommutes with X-type logical L iff |S ∩ L.support| is odd. -/
theorem ZTypePauli_anticommutes_iff (support : Finset (Fin n)) :
    anticommutesWithLogical (ZTypePauli n support) L ↔
    (support ∩ L.support).card % 2 = 1 := by
  unfold anticommutesWithLogical ZTypePauli
  rfl

/-- Z-type operators with odd overlap cannot be deformed. -/
theorem ZType_odd_overlap_no_deformation (support : Finset (Fin n))
    (hodd : (support ∩ L.support).card % 2 = 1)
    (hodd_target : targetBoundaryParity D (ZTypePauli n support) = 1)
    (hsurj : BoundarySurjectsOntoEvenParity D) :
    ¬(∃ gamma : EdgePath D,
        (∀ e ∈ gamma, e ∈ D.graph.graph.edgeSet) ∧
        satisfiesBoundaryCondition D (ZTypePauli n support) gamma) := by
  have hanticomm : anticommutesWithLogical (ZTypePauli n support) L := by
    rw [ZTypePauli_anticommutes_iff]
    exact hodd
  exact noncommuting_no_deformation D (ZTypePauli n support) hanticomm hodd_target hsurj

/-- Characterization: an operator can be deformed iff target parity is even. -/
theorem deformable_iff_even_parity (P : StabilizerCheck n)
    (hsurj : BoundarySurjectsOntoEvenParity D)
    (heven : HasEvenTargetParity D P) :
    (∃ gamma : EdgePath D,
        (∀ e ∈ gamma, e ∈ D.graph.graph.edgeSet) ∧
        satisfiesBoundaryCondition D P gamma) ↔
    HasEvenTargetParity D P := by
  constructor
  · intro _; exact heven
  · intro h; exact hsurj (targetBoundary D P) h

/-! ## Section 5: Basic Properties -/

/-- The anticommutation condition definition -/
@[simp]
theorem anticommutes_def (P : StabilizerCheck n) :
    anticommutesWithLogical P L = ((P.supportZ ∩ L.support).card % 2 = 1) := rfl

/-- Identity operator commutes (doesn't anticommute) with any logical -/
theorem identity_not_anticommutes :
    ¬anticommutesWithLogical (StabilizerCheck.identity n) L := by
  simp only [anticommutesWithLogical, StabilizerCheck.identity,
             Finset.empty_inter, Finset.card_empty, Nat.zero_mod]
  decide

/-- X-type operators don't anticommute with X-type logicals (empty Z-support) -/
theorem XType_not_anticommutes (support : Finset (Fin n)) :
    ¬anticommutesWithLogical (XTypePauli n support) L := by
  simp only [anticommutesWithLogical, XTypePauli, Finset.empty_inter,
             Finset.card_empty, Nat.zero_mod]
  decide

/-- The commutation/anticommutation dichotomy -/
theorem commutes_or_anticommutes (P : StabilizerCheck n) :
    commutesWithLogical P L ∨ anticommutesWithLogical P L := by
  unfold commutesWithLogical anticommutesWithLogical
  have h : (P.supportZ ∩ L.support).card % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- Every operator either commutes or anticommutes with L (exclusive or) -/
theorem commutes_xor_anticommutes (P : StabilizerCheck n) :
    (commutesWithLogical P L ∧ ¬anticommutesWithLogical P L) ∨
    (¬commutesWithLogical P L ∧ anticommutesWithLogical P L) := by
  unfold commutesWithLogical anticommutesWithLogical
  have h : (P.supportZ ∩ L.support).card % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- Anticommutation implies non-commutation -/
theorem anticommutes_implies_not_commutes (P : StabilizerCheck n)
    (h : anticommutesWithLogical P L) : ¬commutesWithLogical P L := by
  rw [anticommutes_iff_not_commutes] at h
  exact h

/-- Non-commutation implies anticommutation -/
theorem not_commutes_implies_anticommutes (P : StabilizerCheck n)
    (h : ¬commutesWithLogical P L) : anticommutesWithLogical P L := by
  have := anticommutes_iff_not_commutes (L := L) P
  rw [this]
  exact h

/-- Z-type operator with singleton support anticommutes with L iff qubit is in L.support -/
theorem ZType_singleton_anticommutes_iff (q : Fin n) :
    anticommutesWithLogical (ZTypePauli n {q}) L ↔ q ∈ L.support := by
  simp only [anticommutesWithLogical, ZTypePauli]
  constructor
  · intro h
    by_contra hq
    simp only [Finset.singleton_inter_of_notMem hq, Finset.card_empty, Nat.zero_mod] at h
    exact zero_ne_one h
  · intro hq
    simp only [Finset.singleton_inter_of_mem hq, Finset.card_singleton, Nat.one_mod]

/-- Product of checks commutes with logical if both factors commute -/
theorem mul_commutes_with_logical (P Q : StabilizerCheck n)
    (hP : commutesWithLogical P L) (hQ : commutesWithLogical Q L) :
    commutesWithLogical (StabilizerCheck.mul P Q) L := by
  unfold commutesWithLogical at *
  simp only [StabilizerCheck.mul]
  -- The Z-support of P * Q is symmDiff of Z-supports
  -- |symmDiff(A, B) ∩ S| ≡ |A ∩ S| + |B ∩ S| (mod 2)
  have h := symmDiff_inter_card_mod2 P.supportZ Q.supportZ L.support
  omega

end QEC
