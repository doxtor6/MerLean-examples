import QEC1.Lemmas.Lem_1_DeformedCodeChecks
import Mathlib.Tactic

/-!
# Remark 7: Codespace Dimension After Gauging

## Statement
The deformed code on the extended qubit system V ⊕ E(G) has parameters that differ
from the original code. If the original code has parameters [[n, k, d]] with J checks,
and the gauging graph G = (V, E) has a cycle collection C that generates the full
cycle space (so |C| = |E| - |V| + 1 for a connected graph), then the deformed code
has n + |E| physical qubits and |V| + |C| + |J| checks, giving:

  k_new = (n + |E|) - (|V| + |C| + |J|) = k - 1

The gauging measurement consumes exactly one logical qubit.

## Main Results
- `codespace_dimension_change_after_gauging`: The nominal parameter count k drops by 1
- `deformed_numQubits_eq`: numQubits of deformed code = n + |E|
- `deformed_numChecks_eq`: numChecks of deformed code = |V| + |C| + |J|
- `cycle_rank_property`: The relation |C| = |E| - |V| + 1 for a complete cycle basis
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodespaceDimension

open Finset PauliOp GaussFlux DeformedOperator DeformedCode DeformedCodeChecks

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
  {C : Type*} [Fintype C] [DecidableEq C]
  (cycles : C → Set G.edgeSet) [∀ c, DecidablePred (· ∈ cycles c)]
  {J : Type*} [Fintype J] [DecidableEq J]
  (checks : J → PauliOp V)

/-! ## Restatement of basic parameter counts -/

/-- The number of physical qubits in the deformed code equals |V| + |E|. -/
theorem deformed_numQubits_eq
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numQubits =
    Fintype.card V + Fintype.card G.edgeSet :=
  deformedStabilizerCode_numQubits G cycles checks data hcyc hcomm

/-- The number of checks in the deformed code equals |V| + |C| + |J|. -/
theorem deformed_numChecks_eq
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numChecks =
    Fintype.card V + Fintype.card C + Fintype.card J :=
  deformedStabilizerCode_numChecks G cycles checks data hcyc hcomm

/-! ## Cycle rank property

For a connected graph G with a complete cycle basis C (meaning the cycles in C
generate all cycles), we have |C| = |E| - |V| + 1. This is the cycle rank
(first Betti number) of the graph. -/

/-- The cycle rank property: |C| = |E| - |V| + 1, stated as
    |C| + |V| = |E| + 1. This holds when C is a complete cycle basis for a
    connected graph G. We state it as an equation on natural numbers, avoiding
    subtraction issues. -/
def CycleRankProperty : Prop :=
  Fintype.card C + Fintype.card V = Fintype.card G.edgeSet + 1

/-! ## Main theorem: codespace dimension changes by 1 -/

/-- **Codespace dimension after gauging**: If the original code on n qubits with J checks
    has nominal parameter k = n - J, and the gauging graph G has a cycle collection C
    satisfying the cycle rank property |C| + |V| = |E| + 1, then the deformed code
    has nominal parameter k_new = (n + |E|) - (|V| + |C| + |J|) = k - 1.

    Stated without subtraction: if n = k + J and |C| + |V| = |E| + 1,
    then (n + |E|) = (k - 1) + (|V| + |C| + |J|) when k ≥ 1.

    We state this as: the deformed code's numQubits - numChecks equals the original
    code's (numQubits - numChecks) minus 1. -/
theorem codespace_dimension_change_after_gauging
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (n k : ℕ)
    (hn : Fintype.card V = n)
    (hk : n - Fintype.card J = k)
    (hk_pos : k ≥ 1)
    (hcr : CycleRankProperty G (C := C)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numQubits -
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numChecks = k - 1 := by
  rw [deformed_numQubits_eq, deformed_numChecks_eq]
  unfold CycleRankProperty at hcr
  -- We need: (|V| + |E|) - (|V| + |C| + |J|) = k - 1
  -- where k = n - |J|, n = |V|, |C| + |V| = |E| + 1
  -- From hcr: |C| + |V| = |E| + 1, so |E| = |C| + |V| - 1
  -- (|V| + |E|) - (|V| + |C| + |J|)
  --   = (|V| + |C| + |V| - 1) - (|V| + |C| + |J|)
  --   = |V| - 1 - |J|
  --   = (|V| - |J|) - 1
  --   = k - 1
  omega

/-- Alternative formulation: the number of additional checks exceeds the number
    of additional qubits by exactly 1, relative to the original code.
    Specifically: (|V| + |C| + |J|) - |J| = (|V| + |E|) - n + 1
    i.e., the net check increase minus net qubit increase equals 1. -/
theorem additional_checks_exceed_additional_qubits_by_one
    (n : ℕ)
    (hn : Fintype.card V = n)
    (hcr : CycleRankProperty G (C := C)) :
    Fintype.card V + Fintype.card C + Fintype.card J =
    (Fintype.card V + Fintype.card G.edgeSet) - n + Fintype.card J + 1 := by
  unfold CycleRankProperty at hcr
  omega

/-! ## Corollaries -/

/-- When the original code has k = 0 (no logical qubits), the deformed code
    has numQubits ≤ numChecks (i.e., the subtraction underflows to 0). -/
theorem deformed_k_zero_when_original_k_zero
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hn : Fintype.card V = Fintype.card J)
    (hcr : CycleRankProperty G (C := C)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numQubits ≤
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numChecks := by
  rw [deformed_numQubits_eq, deformed_numChecks_eq]
  unfold CycleRankProperty at hcr
  omega

/-- The deformed code numChecks is always at least 1 more than what would preserve k,
    i.e., numChecks - numQubits of the deformed code ≥ numChecks - numQubits of the
    original code + 1 (in the appropriate sense). -/
theorem deformed_numChecks_ge
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (hcr : CycleRankProperty G (C := C)) :
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numChecks =
    (deformedStabilizerCode G cycles checks data hcyc hcomm).numQubits -
    Fintype.card V + Fintype.card J + 1 := by
  rw [deformed_numQubits_eq, deformed_numChecks_eq]
  unfold CycleRankProperty at hcr
  omega

/-- The net effect on parameters: if the original code encodes k logical qubits
    and k ≥ 1, the deformed code encodes k - 1 logical qubits.
    Stated using the HasParameters predicate from Rem_3. -/
theorem deformed_code_parameter_k_minus_one
    (data : DeformedCodeData G checks)
    (hcyc : ∀ (c : C) (v : V),
      Even (Finset.univ.filter (fun e : G.edgeSet => e ∈ cycles c ∧ v ∈ (e : Sym2 V))).card)
    (hcomm : ∀ i j : J, PauliCommute (checks i) (checks j))
    (n k : ℕ)
    (hn : Fintype.card V = n)
    (hk : n - Fintype.card J = k)
    (hk_pos : k ≥ 1)
    (hcr : CycleRankProperty G (C := C)) :
    let DC := deformedStabilizerCode G cycles checks data hcyc hcomm
    DC.numQubits - DC.numChecks = k - 1 := by
  exact codespace_dimension_change_after_gauging G cycles checks data hcyc hcomm n k hn hk hk_pos hcr

/-- The number of additional qubits (|E|) and additional checks (|V| + |C|) satisfy
    the relation: additional checks = additional qubits + 1. -/
theorem additional_gauging_checks_eq_qubits_plus_one
    (hcr : CycleRankProperty G (C := C)) :
    Fintype.card V + Fintype.card C = Fintype.card G.edgeSet + 1 := by
  unfold CycleRankProperty at hcr
  omega

/-- Expressed differently: the edge count equals the vertex + cycle count minus 1. -/
theorem edge_count_eq
    (hcr : CycleRankProperty G (C := C)) :
    Fintype.card G.edgeSet + 1 = Fintype.card V + Fintype.card C := by
  unfold CycleRankProperty at hcr
  omega

end CodespaceDimension
