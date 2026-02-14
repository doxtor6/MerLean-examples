import QEC1.Definitions.Def_4_DeformedCode
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import Mathlib.Tactic

/-!
# Lemma 1: Deformed Code Checks

## Statement
The operators listed in Definition 4 (Deformed Code) form a valid generating set of
commuting checks for a stabilizer code (or subsystem code).

Specifically:
1. All A_v operators commute with each other.
2. All B_p operators commute with each other.
3. All s̃_j operators commute with each other.
4. The A_v operators commute with the B_p operators.
5. The A_v operators commute with the s̃_j operators.
6. The B_p operators commute with the s̃_j operators.

## Main Results
- `deformedStabilizerCode` : the deformed code as a StabilizerCode
- `gaussLaw_gaussLaw_commute` : [A_v, A_w] = 0
- `flux_flux_commute` : [B_p, B_q] = 0
- `deformed_deformed_commute` : [s̃_i, s̃_j] = 0
- `gaussLaw_flux_commute` : [A_v, B_p] = 0
- `gaussLaw_deformed_commute` : [A_v, s̃_j] = 0
- `flux_deformed_commute` : [B_p, s̃_j] = 0
- `deformedCodeChecks_allCommute` : all checks pairwise commute
- `deformedCodeChecks_allSelfInverse` : all checks are self-inverse

## Corollaries
- `deformedStabilizerCode_check_eq` : check of the stabilizer code equals deformedCodeChecks
- `deformedStabilizerCode_numQubits` : number of physical qubits
- `deformedStabilizerCode_numChecks` : number of stabilizer checks
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace DeformedCodeChecks

open Finset PauliOp GaussFlux DeformedOperator DeformedCode

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-! ## The Six Commutation Relations -/

/-- (1) All Gauss's law operators commute with each other:
    A_v and A_w are both pure X-type, so they commute. -/
theorem gaussLaw_gaussLaw_commute (v w : V) :
    PauliCommute (gaussLawChecks G v) (gaussLawChecks G w) :=
  allChecks_pairwise_commute_gaussLaw_gaussLaw G v w

/-- (2) All flux operators commute with each other:
    B_p and B_q are both pure Z-type, so they commute. -/
theorem flux_flux_commute (p q : C) :
    PauliCommute (fluxChecks G cycles p) (fluxChecks G cycles q) :=
  allChecks_pairwise_commute_flux_flux G cycles p q

/-- (3) All deformed checks commute with each other:
    On edges both are pure Z-type; on vertices commutation is inherited
    from the original checks. -/
theorem deformed_deformed_commute
    (data : DeformedCodeData G checks)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (i j : J) :
    PauliCommute (deformedOriginalChecks G checks data i)
                 (deformedOriginalChecks G checks data j) :=
  allChecks_pairwise_commute_deformed_deformed G checks data hcomm i j

/-- (4) Gauss's law operators commute with flux operators:
    The symplectic inner product counts the overlap of X-support(A_v) with
    Z-support(B_p), which is the number of edges in p incident to v. For a
    valid cycle, this is always even (0 or 2). -/
theorem gaussLaw_flux_commute
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (v : V) (p : C) :
    PauliCommute (gaussLawChecks G v) (fluxChecks G cycles p) :=
  allChecks_pairwise_commute_gaussLaw_flux G cycles hcyc v p

/-- (5) Gauss's law operators commute with deformed checks:
    The boundary condition ensures the anticommutation signs cancel. -/
theorem gaussLaw_deformed_commute
    (data : DeformedCodeData G checks) (v : V) (j : J) :
    PauliCommute (gaussLawChecks G v) (deformedOriginalChecks G checks data j) :=
  allChecks_pairwise_commute_gaussLaw_deformed G checks data v j

/-- (6) Flux operators commute with deformed checks:
    B_p is pure Z-type and acts only on edges; s̃_j has no X-support on edges.
    Since Z commutes with Z and B_p doesn't act on vertex qubits, they commute. -/
theorem flux_deformed_commute
    (data : DeformedCodeData G checks) (p : C) (j : J) :
    PauliCommute (fluxChecks G cycles p) (deformedOriginalChecks G checks data j) := by
  rw [PauliOp.pauliCommute_comm]
  exact allChecks_pairwise_commute_deformed_flux G cycles checks data j p

/-! ## Combined Commutation and Self-Inverse -/

/-- All deformed code checks pairwise commute. -/
theorem deformedCodeChecks_allCommute
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (a b : CheckIndex V C J) :
    PauliCommute (deformedCodeChecks G cycles checks data a)
                 (deformedCodeChecks G cycles checks data b) :=
  allChecks_commute G cycles checks data hcyc hcomm a b

/-- All deformed code checks are self-inverse. -/
theorem deformedCodeChecks_allSelfInverse
    (data : DeformedCodeData G checks) (a : CheckIndex V C J) :
    deformedCodeChecks G cycles checks data a *
    deformedCodeChecks G cycles checks data a = 1 :=
  allChecks_self_inverse G cycles checks data a

/-! ## The Deformed Code as a StabilizerCode -/

/-- The deformed code forms a valid stabilizer code on the extended qubit system V ⊕ E(G).
    The check index type is CheckIndex V C J = V ⊕ C ⊕ J, and the checks are the
    deformed code checks from Definition 4. -/
def deformedStabilizerCode
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    StabilizerCode (ExtQubit G) where
  I := CheckIndex V C J
  check := deformedCodeChecks G cycles checks data
  checks_commute := allChecks_commute G cycles checks data hcyc hcomm

/-! ## Properties of the Deformed Stabilizer Code -/

@[simp]
theorem deformedStabilizerCode_check_eq
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (a : CheckIndex V C J) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).check a =
    deformedCodeChecks G cycles checks data a := rfl

/-- The number of physical qubits in the deformed code is |V| + |E|. -/
theorem deformedStabilizerCode_numQubits
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numQubits =
    Fintype.card V + Fintype.card G.edgeSet := by
  simp [StabilizerCode.numQubits, Fintype.card_sum]

/-- The number of checks in the deformed code is |V| + |C| + |J|. -/
theorem deformedStabilizerCode_numChecks
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numChecks =
    Fintype.card V + Fintype.card C + Fintype.card J := by
  simp only [StabilizerCode.numChecks]
  -- The check index type is CheckIndex V C J ≃ V ⊕ C ⊕ J
  have : Fintype.card (CheckIndex V C J) = Fintype.card V + Fintype.card C + Fintype.card J := by
    have h : Fintype.card (CheckIndex V C J) = Fintype.card (V ⊕ C ⊕ J) := by
      apply Fintype.card_congr
      exact {
        toFun := fun i => match i with
          | .gaussLaw v => Sum.inl v
          | .flux p => Sum.inr (Sum.inl p)
          | .deformed j => Sum.inr (Sum.inr j)
        invFun := fun s => match s with
          | Sum.inl v => .gaussLaw v
          | Sum.inr (Sum.inl p) => .flux p
          | Sum.inr (Sum.inr j) => .deformed j
        left_inv := fun i => by cases i <;> rfl
        right_inv := fun s => by rcases s with v | p | j <;> rfl
      }
    rw [h, Fintype.card_sum, Fintype.card_sum, add_assoc]
  exact this

/-! ## Gauss's Law Checks in the Stabilizer Code -/

/-- Gauss's law checks are in the stabilizer group. -/
theorem gaussLaw_mem_stabilizerGroup
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (v : V) :
    gaussLawChecks G v ∈
    (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
  have : gaussLawChecks G v =
    (deformedStabilizerCode G cycles checks data hcyc hcomm).check (.gaussLaw v) := rfl
  rw [this]
  exact StabilizerCode.check_mem_stabilizerGroup _ _

/-- Flux checks are in the stabilizer group. -/
theorem flux_mem_stabilizerGroup
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (p : C) :
    fluxChecks G cycles p ∈
    (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
  have : fluxChecks G cycles p =
    (deformedStabilizerCode G cycles checks data hcyc hcomm).check (.flux p) := rfl
  rw [this]
  exact StabilizerCode.check_mem_stabilizerGroup _ _

/-- Deformed original checks are in the stabilizer group. -/
theorem deformed_mem_stabilizerGroup
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (j : J) :
    deformedOriginalChecks G checks data j ∈
    (deformedStabilizerCode G cycles checks data hcyc hcomm).stabilizerGroup := by
  have : deformedOriginalChecks G checks data j =
    (deformedStabilizerCode G cycles checks data hcyc hcomm).check (.deformed j) := rfl
  rw [this]
  exact StabilizerCode.check_mem_stabilizerGroup _ _

/-! ## Centralizer Properties -/

/-- Gauss's law checks are in the centralizer of the deformed code. -/
theorem gaussLaw_inCentralizer
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (v : V) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer
      (gaussLawChecks G v) := by
  intro a
  have : gaussLawChecks G v =
    (deformedStabilizerCode G cycles checks data hcyc hcomm).check (.gaussLaw v) := rfl
  rw [this]
  exact (deformedStabilizerCode G cycles checks data hcyc hcomm).checks_commute _ _

/-- Flux checks are in the centralizer of the deformed code. -/
theorem flux_inCentralizer
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (p : C) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer
      (fluxChecks G cycles p) := by
  intro a
  have : fluxChecks G cycles p =
    (deformedStabilizerCode G cycles checks data hcyc hcomm).check (.flux p) := rfl
  rw [this]
  exact (deformedStabilizerCode G cycles checks data hcyc hcomm).checks_commute _ _

/-- Deformed checks are in the centralizer of the deformed code. -/
theorem deformed_inCentralizer
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (j : J) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).inCentralizer
      (deformedOriginalChecks G checks data j) := by
  intro a
  have : deformedOriginalChecks G checks data j =
    (deformedStabilizerCode G cycles checks data hcyc hcomm).check (.deformed j) := rfl
  rw [this]
  exact (deformedStabilizerCode G cycles checks data hcyc hcomm).checks_commute _ _

/-! ## Type Classification in the Stabilizer Code -/

/-- Gauss's law checks in the deformed stabilizer code are pure X-type. -/
theorem deformedStabilizerCode_gaussLaw_pure_X
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (v : V) :
    ((deformedStabilizerCode G cycles checks data hcyc hcomm).check (.gaussLaw v)).zVec = 0 :=
  gaussLawChecks_pure_X G v

/-- Flux checks in the deformed stabilizer code are pure Z-type. -/
theorem deformedStabilizerCode_flux_pure_Z
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (p : C) :
    ((deformedStabilizerCode G cycles checks data hcyc hcomm).check (.flux p)).xVec = 0 :=
  fluxChecks_pure_Z G cycles p

/-- Deformed checks in the deformed stabilizer code have no X-support on edge qubits. -/
theorem deformedStabilizerCode_deformed_noXOnEdges
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (j : J) (e : G.edgeSet) :
    ((deformedStabilizerCode G cycles checks data hcyc hcomm).check (.deformed j)).xVec
      (Sum.inr e) = 0 :=
  deformedOriginalChecks_no_xSupport_on_edges G checks data j e

/-! ## The Logical Operator and the Stabilizer Code -/

/-- The product of all Gauss's law checks in the deformed stabilizer code
    equals the logical operator L = ∏_{v ∈ V} X_v. -/
theorem deformedStabilizerCode_gaussLaw_product
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    (∏ v : V, (deformedStabilizerCode G cycles checks data hcyc hcomm).check (.gaussLaw v)) =
    logicalOp G := by
  convert gaussLawChecks_product_eq_logical G using 1

end DeformedCodeChecks
