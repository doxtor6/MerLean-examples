import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import QEC1.Remarks.Rem_2_NotationPauliOperators
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Tactic

/-!
# Definition 2: Gauss's Law and Flux Operators

## Statement
Given a graph G = (V, E) and a collection of cycles C, we define Pauli operators on the
extended qubit system V ⊕ E (vertex qubits + edge qubits):

1. **Gauss's law operator** A_v = X_v ∏_{e ∋ v} X_e for each vertex v ∈ V
2. **Flux operator** B_p = ∏_{e ∈ p} Z_e for each cycle p ∈ C

## Main Results
- `gaussLawOp` : the Gauss's law operator A_v
- `fluxOp` : the flux operator B_p
- `gaussLawOp_is_pure_X` : A_v is pure X-type (zVec = 0)
- `fluxOp_is_pure_Z` : B_p is pure Z-type (xVec = 0)
- `gaussLaw_commute` : [A_v, A_v'] = 0
- `flux_commute` : [B_p, B_p'] = 0
- `gauss_flux_commute` : [A_v, B_p] = 0
- `gaussLaw_product` : ∏_v A_v = L = ∏_{v ∈ V} X_v (the logical operator)

## Corollaries
- Support characterization lemmas
- X-support and Z-support computations
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GaussFlux

open Finset PauliOp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## Extended qubit type: V ⊕ G.edgeSet -/

/-- The extended qubit type: vertex qubits (Sum.inl v) and edge qubits (Sum.inr e). -/
abbrev ExtQubit := V ⊕ G.edgeSet

instance : Fintype (ExtQubit G) := inferInstanceAs (Fintype (V ⊕ G.edgeSet))
instance : DecidableEq (ExtQubit G) := inferInstanceAs (DecidableEq (V ⊕ G.edgeSet))

/-! ## Incident edges -/

/-- The finset of edges incident to vertex v. -/
noncomputable def incidentEdges (v : V) : Finset G.edgeSet :=
  Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))

@[simp]
theorem mem_incidentEdges (v : V) (e : G.edgeSet) :
    e ∈ incidentEdges G v ↔ v ∈ (e : Sym2 V) := by
  simp [incidentEdges]

/-! ## Gauss's Law Operator -/

/-- The Gauss's law operator A_v on the extended system V ⊕ E.
    A_v = X_v ∏_{e ∋ v} X_e: acts with X on vertex qubit v and all incident edge qubits. -/
def gaussLawOp (v : V) : PauliOp (ExtQubit G) where
  xVec := fun q => match q with
    | Sum.inl w => if w = v then 1 else 0
    | Sum.inr e => if v ∈ (e : Sym2 V) then 1 else 0
  zVec := 0

/-- A_v is pure X-type: its Z-vector is identically zero. -/
@[simp]
theorem gaussLawOp_zVec (v : V) : (gaussLawOp G v).zVec = 0 := rfl

/-! ## Flux Operator -/

variable {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]

/-- The flux operator B_p on the extended system V ⊕ E.
    B_p = ∏_{e ∈ p} Z_e: acts with Z on all edge qubits in cycle p. -/
def fluxOp (p : C) : PauliOp (ExtQubit G) where
  xVec := 0
  zVec := fun q => match q with
    | Sum.inl _ => 0
    | Sum.inr e => if e ∈ cycles p then 1 else 0

/-- B_p is pure Z-type: its X-vector is identically zero. -/
@[simp]
theorem fluxOp_xVec (p : C) : (fluxOp G cycles p).xVec = 0 := rfl

/-! ## Pure X-type / Z-type Properties -/

/-- A_v is pure X-type: it has no Z support. -/
theorem gaussLawOp_is_pure_X (v : V) :
    (gaussLawOp G v).supportZ = ∅ := by
  ext q; simp [supportZ, gaussLawOp]

/-- B_p is pure Z-type: it has no X support. -/
theorem fluxOp_is_pure_Z (p : C) :
    (fluxOp G cycles p).supportX = ∅ := by
  ext q; simp [supportX, fluxOp]

/-! ## Commutation: Gauss operators mutually commute -/

/-- All Gauss's law operators mutually commute: [A_v, A_w] = 0.
    This holds because they are all pure X-type. -/
theorem gaussLaw_commute (v w : V) :
    PauliCommute (gaussLawOp G v) (gaussLawOp G w) := by
  simp only [PauliCommute, symplecticInner]
  apply Finset.sum_eq_zero
  intro q _
  simp [gaussLawOp]

/-! ## Commutation: Flux operators mutually commute -/

/-- All flux operators mutually commute: [B_p, B_q] = 0.
    This holds because they are all pure Z-type. -/
theorem flux_commute (p q : C) :
    PauliCommute (fluxOp G cycles p) (fluxOp G cycles q) := by
  simp only [PauliCommute, symplecticInner]
  apply Finset.sum_eq_zero
  intro r _
  simp [fluxOp]

/-! ## Commutation: Gauss and flux operators commute -/

/-- The number of edges in cycle p that are incident to vertex v.
    For a cycle, this is always even (0 or 2). -/
noncomputable def cycleIncidentCount (v : V) (p : C) : ℕ :=
  (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles p ∧ v ∈ (e : Sym2 V))).card

/-- Gauss's law operators commute with flux operators: [A_v, B_p] = 0.
    This holds because the symplectic inner product counts the overlap of
    X-support(A_v) with Z-support(B_p), which equals the number of edges
    in p incident to v. For a valid cycle, this is always even. -/
theorem gauss_flux_commute
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (v : V) (p : C) :
    PauliCommute (gaussLawOp G v) (fluxOp G cycles p) := by
  simp only [PauliCommute, symplecticInner]
  -- The symplectic inner product Σ_q (Av.x_q * Bp.z_q + Av.z_q * Bp.x_q)
  -- Since A_v is pure X-type (z=0) and B_p is pure Z-type (x=0):
  -- = Σ_q Av.x_q * Bp.z_q
  have h_sum : ∑ q : ExtQubit G,
      ((gaussLawOp G v).xVec q * (fluxOp G cycles p).zVec q +
       (gaussLawOp G v).zVec q * (fluxOp G cycles p).xVec q) =
      ∑ q : ExtQubit G, (gaussLawOp G v).xVec q * (fluxOp G cycles p).zVec q := by
    congr 1; ext q; simp [gaussLawOp, fluxOp]
  rw [h_sum]
  -- Split the sum over V ⊕ E into vertex and edge parts
  rw [Fintype.sum_sum_type]
  -- The vertex part is 0 (B_p has z=0 on vertices)
  have h_vertex : ∑ w : V,
      (gaussLawOp G v).xVec (Sum.inl w) * (fluxOp G cycles p).zVec (Sum.inl w) = 0 := by
    apply Finset.sum_eq_zero; intro w _; simp [gaussLawOp, fluxOp]
  rw [h_vertex, zero_add]
  -- The edge part: Σ_e [v ∈ e] * [e ∈ p]
  -- = Σ_e [e ∈ p ∧ v ∈ e]  (product of indicators)
  have h_edge : ∑ e : G.edgeSet,
      (gaussLawOp G v).xVec (Sum.inr e) * (fluxOp G cycles p).zVec (Sum.inr e) =
      ∑ e : G.edgeSet, if (e ∈ cycles p ∧ v ∈ (e : Sym2 V)) then 1 else 0 := by
    congr 1; ext e; simp only [gaussLawOp, fluxOp]
    by_cases h1 : v ∈ (e : Sym2 V) <;> by_cases h2 : e ∈ cycles p <;> simp [h1, h2]
  rw [h_edge]
  rw [Finset.sum_boole]
  rw [ZMod.natCast_eq_zero_iff_even]
  exact hcyc p v

/-! ## X-support characterization -/

/-- The X-support of A_v on vertex qubits is {v}. -/
theorem gaussLawOp_supportX_vertex (v : V) :
    ∀ w : V, (Sum.inl w : ExtQubit G) ∈ (gaussLawOp G v).supportX ↔ w = v := by
  intro w
  simp [supportX, gaussLawOp]

/-- The X-support of A_v on edge qubits is the set of incident edges. -/
theorem gaussLawOp_supportX_edge (v : V) :
    ∀ e : G.edgeSet, (Sum.inr e : ExtQubit G) ∈ (gaussLawOp G v).supportX ↔
      v ∈ (e : Sym2 V) := by
  intro e
  simp [supportX, gaussLawOp]

/-- The Z-support of B_p on edge qubits is the set of edges in the cycle. -/
theorem fluxOp_supportZ_edge (p : C) :
    ∀ e : G.edgeSet, (Sum.inr e : ExtQubit G) ∈ (fluxOp G cycles p).supportZ ↔
      e ∈ cycles p := by
  intro e
  simp [supportZ, fluxOp]

/-- The Z-support of B_p on vertex qubits is empty. -/
theorem fluxOp_supportZ_vertex (p : C) :
    ∀ w : V, (Sum.inl w : ExtQubit G) ∉ (fluxOp G cycles p).supportZ := by
  intro w
  simp [supportZ, fluxOp]

/-! ## Gauss Product Property -/

/-- The logical operator L = ∏_{v ∈ V} X_v on the extended system:
    acts X on all vertex qubits and I on all edge qubits. -/
def logicalOp : PauliOp (ExtQubit G) where
  xVec := fun q => match q with
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  zVec := 0

/-- Helper: The product of Gauss's law operators is computed pointwise as
    the sum of their x-vectors in ZMod 2. On vertex qubits, each vertex v
    contributes 1 exactly once (from A_v). On edge qubits, each edge e = {a,b}
    contributes 1 from A_a and 1 from A_b, so the sum is 0 (mod 2). -/
theorem gaussLaw_product_xVec_inl (v : V) :
    ∑ w : V, (gaussLawOp G w).xVec (Sum.inl v) = 1 := by
  simp [gaussLawOp]

theorem gaussLaw_product_xVec_inr (e : G.edgeSet) :
    ∑ v : V, (gaussLawOp G v).xVec (Sum.inr e) = 0 := by
  simp only [gaussLawOp]
  -- Sum over v of [v ∈ e] = number of endpoints of e, which is 2
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      intro h; subst h; exact G.loopless a (G.mem_edgeSet.mp he)
    -- The sum is over all v : V, with indicator 1 if v ∈ {a, b}
    have : ∑ v : V, (if v ∈ (⟨s(a, b), he⟩ : G.edgeSet).val then (1 : ZMod 2) else 0) =
        ∑ v : V, (if v ∈ s(a, b) then (1 : ZMod 2) else 0) := by
      rfl
    rw [this]
    have h_eq : ∀ v : V, (if v ∈ s(a, b) then (1 : ZMod 2) else 0) =
        (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
      intro v
      by_cases hva : v = a
      · subst hva; simp [Sym2.mem_iff, hab]
      · by_cases hvb : v = b
        · subst hvb; simp [Sym2.mem_iff, hva]
        · have : v ∉ s(a, b) := by rw [Sym2.mem_iff]; push_neg; exact ⟨hva, hvb⟩
          simp [this, hva, hvb]
    simp_rw [h_eq]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact CharTwo.add_self_eq_zero (1 : ZMod 2)

-- Since PauliOp is an abelian group with xVec (P*Q) = P.xVec + Q.xVec and
-- zVec (P*Q) = P.zVec + Q.zVec, the product ∏ v, A_v has:
-- xVec = Σ v, (A_v).xVec  and  zVec = Σ v, (A_v).zVec  (in ZMod 2)

private lemma prod_pauliOp_xVec {α : Type*} [DecidableEq α]
    {W : Type*} [Fintype W] [DecidableEq W]
    (S : Finset α) (f : α → PauliOp W) (q : W) :
    (∏ a ∈ S, f a).xVec q = ∑ a ∈ S, (f a).xVec q := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    simp only [mul_xVec, Pi.add_apply]
    rw [ih]

private lemma prod_pauliOp_zVec {α : Type*} [DecidableEq α]
    {W : Type*} [Fintype W] [DecidableEq W]
    (S : Finset α) (f : α → PauliOp W) (q : W) :
    (∏ a ∈ S, f a).zVec q = ∑ a ∈ S, (f a).zVec q := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    simp only [mul_zVec, Pi.add_apply]
    rw [ih]

/-- **Gauss product property** (clean version):
    ∏_{v ∈ V} A_v = L, the logical X operator on all vertices.
    Each vertex gets X exactly once; each edge gets X² = I. -/
theorem gaussLaw_product :
    (∏ v : V, gaussLawOp G v) = logicalOp G := by
  ext q
  · -- xVec
    rw [show (∏ v : V, gaussLawOp G v).xVec q =
        (∏ v ∈ Finset.univ, gaussLawOp G v).xVec q by simp]
    rw [prod_pauliOp_xVec]
    cases q with
    | inl w =>
      simp only [gaussLawOp, logicalOp, eq_comm (a := w)]
      rw [Finset.sum_ite_eq']
      simp
    | inr e =>
      simp only [gaussLawOp, logicalOp]
      exact gaussLaw_product_xVec_inr G e
  · -- zVec
    rw [show (∏ v : V, gaussLawOp G v).zVec q =
        (∏ v ∈ Finset.univ, gaussLawOp G v).zVec q by simp]
    rw [prod_pauliOp_zVec]
    simp [gaussLawOp, logicalOp]

/-! ## Logical operator is pure X-type -/

/-- The logical operator L is pure X-type. -/
@[simp]
theorem logicalOp_is_pure_X :
    (logicalOp G).supportZ = ∅ := by
  ext q; simp [supportZ, logicalOp]

/-! ## Commutation of logical with flux -/

/-- The logical operator commutes with all flux operators. -/
theorem logical_flux_commute (p : C) :
    PauliCommute (logicalOp G) (fluxOp G cycles p) := by
  simp only [PauliCommute, symplecticInner]
  apply Finset.sum_eq_zero
  intro q _
  cases q with
  | inl w => simp [logicalOp, fluxOp]
  | inr e => simp [logicalOp, fluxOp]

/-! ## Summary: All Commutation Relations -/

/-- All three commutation relations hold simultaneously:
    (i)   [A_v, A_w] = 0 for all v, w ∈ V
    (ii)  [B_p, B_q] = 0 for all p, q ∈ C
    (iii) [A_v, B_p] = 0 for all v ∈ V, p ∈ C -/
theorem all_commutation_relations
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card) :
    (∀ v w : V, PauliCommute (gaussLawOp G v) (gaussLawOp G w)) ∧
    (∀ p q : C, PauliCommute (fluxOp G cycles p) (fluxOp G cycles q)) ∧
    (∀ v : V, ∀ p : C, PauliCommute (gaussLawOp G v) (fluxOp G cycles p)) :=
  ⟨fun v w => gaussLaw_commute G v w,
   fun p q => flux_commute G cycles p q,
   fun v p => gauss_flux_commute G cycles hcyc v p⟩

/-! ## Relationship to Boundary Maps -/

/-- The Gauss's law operator A_v has X-support related to the coboundary map:
    the X-support on edges is exactly the set of edges incident to v,
    which is described by δ(1_v) in the boundary map formalism. -/
theorem gaussLawOp_xVec_edge_eq_coboundary (v : V) (e : G.edgeSet) :
    (gaussLawOp G v).xVec (Sum.inr e) =
    GraphMaps.coboundaryMap G (Pi.single v 1) e := by
  simp only [gaussLawOp]
  rw [GraphMaps.coboundaryMap_single]

/-- The flux operator B_p has Z-support related to the second boundary map:
    the Z-support on edges is exactly the set of edges in cycle p,
    which is described by ∂₂(1_p) in the boundary map formalism. -/
theorem fluxOp_zVec_edge_eq_secondBoundary (p : C) (e : G.edgeSet) :
    (fluxOp G cycles p).zVec (Sum.inr e) =
    GraphMaps.secondBoundaryMap G cycles (Pi.single p 1) e := by
  simp only [fluxOp]
  rw [GraphMaps.secondBoundaryMap_single]

end GaussFlux
