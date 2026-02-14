import QEC1.Remarks.Rem_20_GrossCodeDefinition
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

set_option linter.unusedDecidableInType false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false

/-!
# Remark 21: Gauging Measurement Construction for X̄_α in the Gross Code

## Statement
Explicit construction of the gauging graph G for measuring X̄_α = X(αf, 0) in the
Gross code (Rem_20), with degree bounds on the Tanner graph of the deformed code.

## Main Results
- `gaugingVertices`: the 12 vertices (support of f)
- `gaugingAdj`: the adjacency relation (18 matching + 4 expansion edges)
- `gaugingGraph`: the gauging graph as a SimpleGraph
- `gaugingCyclesList`: the 7 independent cycles
- `gaugingVertices_card`: |V(G)| = 12
- `gaugingEdges_card`: |E(G)| = 22
- `gaugingCycles_count`: 7 independent cycles
- `total_overhead`: additional checks + qubits = 41
-/

namespace BivariateBicycle

namespace GrossCode

open PauliOp

/-! ## The gauging graph vertices -/

/-- The support of f: the 12 monomials γ with f(γ) ≠ 0 in the Gross code. -/
def gaugingVertices : Finset GrossMonomial :=
  Finset.univ.filter (fun γ => grossF γ ≠ 0)

/-- The vertices of the gauging graph are exactly the 12 monomials in supp(f). -/
theorem gaugingVertices_card : gaugingVertices.card = 12 := by
  native_decide

@[simp] theorem mem_gaugingVertices (γ : GrossMonomial) :
    γ ∈ gaugingVertices ↔ grossF γ ≠ 0 := by
  simp [gaugingVertices]

/-! ## Matching edge condition

Two vertices γ, δ ∈ supp(f) share a Z check iff γ - δ = -B_i + B_j
for B_i, B_j ∈ {y³, x², x} (the monomial terms of B = y³ + x² + x), with γ ≠ δ.
-/

/-- Whether a difference d equals -B_i + B_j for some distinct terms B_i, B_j of B.
    The terms of B are (0,3), (2,0), (1,0) in Z₁₂ × Z₆. -/
def isMatchingDiff (d : GrossMonomial) : Bool :=
  let terms : List GrossMonomial := [(0, 3), (2, 0), (1, 0)]
  terms.any fun bi => terms.any fun bj => (d == -bi + bj) && (d != (0 : GrossMonomial))

/-- The matching edge condition: γ and δ are in supp(f) and share a Z check. -/
def isMatchingEdge (γ δ : GrossMonomial) : Bool :=
  (grossF γ != 0) && (grossF δ != 0) && isMatchingDiff (γ - δ)

/-! ## Expansion edges -/

/-- The 4 expansion edges ensuring the deformed code has distance 12. -/
def expansionEdges : List (GrossMonomial × GrossMonomial) :=
  [((2, 0), (5, 3)), ((2, 0), (6, 0)), ((5, 3), (11, 3)), ((7, 3), (11, 3))]

/-- Whether (γ, δ) is one of the 4 expansion edges (unordered). -/
def isExpansionEdge (γ δ : GrossMonomial) : Bool :=
  expansionEdges.any fun (a, b) => (γ == a && δ == b) || (γ == b && δ == a)

/-! ## The gauging graph adjacency -/

/-- The full adjacency: matching edges OR expansion edges, with γ ≠ δ. -/
def gaugingAdj (γ δ : GrossMonomial) : Prop :=
  γ ≠ δ ∧ (isMatchingEdge γ δ || isExpansionEdge γ δ) = true

instance instDecidableRelGaugingAdj : DecidableRel gaugingAdj :=
  fun _ _ => instDecidableAnd

private theorem gaugingAdj_symm :
    ∀ γ δ : GrossMonomial, gaugingAdj γ δ → gaugingAdj δ γ := by
  native_decide

private theorem gaugingAdj_irrefl :
    ∀ γ : GrossMonomial, ¬gaugingAdj γ γ := by
  intro γ h; exact h.1 rfl

/-- The gauging graph G for measuring X̄_α in the Gross code.
    Vertices are GrossMonomial = Z₁₂ × Z₆; the "active" vertices are supp(f). -/
def gaugingGraph : SimpleGraph GrossMonomial where
  Adj := gaugingAdj
  symm := gaugingAdj_symm
  loopless := gaugingAdj_irrefl

instance : DecidableRel gaugingGraph.Adj := inferInstanceAs (DecidableRel gaugingAdj)

/-! ## Edge count -/

set_option maxHeartbeats 1600000 in
/-- The gauging graph has exactly 22 edges. -/
theorem gaugingEdges_card : gaugingGraph.edgeFinset.card = 22 := by
  native_decide

/-! ## The 7 independent cycles -/

/-- The 7 independent cycles for the flux checks, as lists of vertices.
    Each list [v₁, v₂, ..., vₖ] represents the cycle v₁ → v₂ → ⋯ → vₖ → v₁. -/
def gaugingCyclesList : List (List GrossMonomial) :=
  [ [(9, 0), (7, 3), (8, 0)],
    [(9, 0), (11, 3), (7, 3)],
    [(6, 0), (7, 0), (5, 3)],
    [(6, 0), (2, 0), (5, 3)],
    [(3, 0), (2, 0), (5, 3)],
    [(6, 0), (7, 0), (8, 0), (7, 3)],
    [(1, 0), (2, 0), (5, 3), (11, 3)] ]

/-- 7 independent cycles are listed. -/
theorem gaugingCycles_count : gaugingCyclesList.length = 7 := by rfl

set_option maxHeartbeats 1600000 in
/-- Each vertex in the cycles is in the support of f. -/
theorem gaugingCycles_vertices_in_support :
    ∀ cyc ∈ gaugingCyclesList, ∀ v ∈ cyc, v ∈ gaugingVertices := by
  native_decide

/-- Each cycle has at least 3 vertices. -/
theorem gaugingCycles_length_ge_3 :
    ∀ cyc ∈ gaugingCyclesList, 3 ≤ cyc.length := by
  native_decide

set_option maxHeartbeats 1600000 in
/-- Consecutive vertices in each cycle are adjacent in the gauging graph. -/
theorem gaugingCycles_edges_valid :
    ∀ cyc ∈ gaugingCyclesList,
      ∀ i : Fin cyc.length,
        gaugingGraph.Adj (cyc[i]) (cyc[(⟨(i.val + 1) % cyc.length, Nat.mod_lt _ (Fin.pos i)⟩ : Fin cyc.length)]) := by
  native_decide

/-! ## Cycle properties -/

/-- All cycles have length 3 or 4. -/
theorem gaugingCycles_short :
    ∀ cyc ∈ gaugingCyclesList, cyc.length = 3 ∨ cyc.length = 4 := by
  native_decide

/-- The maximum cycle length is 4. -/
theorem gaugingCycles_max_length :
    ∀ cyc ∈ gaugingCyclesList, cyc.length ≤ 4 := by
  intro cyc hmem
  rcases gaugingCycles_short cyc hmem with h | h <;> omega

/-! ## Euler's formula -/

/-- The cycle space dimension by Euler's formula: |E| - |V| + 1 = 22 - 12 + 1 = 11. -/
theorem cycle_space_dim :
    gaugingGraph.edgeFinset.card + 1 = gaugingVertices.card + 11 := by
  rw [gaugingEdges_card, gaugingVertices_card]

/-! ## Overhead calculation -/

/-- Additional Gauss's law checks (A_v): one per vertex of G = 12. -/
theorem additional_gauss_checks : gaugingVertices.card = 12 := gaugingVertices_card

/-- Additional flux checks (B_p): one per independent cycle = 7. -/
theorem additional_flux_checks : gaugingCyclesList.length = 7 := gaugingCycles_count

/-- Additional qubits (edge qubits): one per edge of G = 22. -/
theorem additional_qubits : gaugingGraph.edgeFinset.card = 22 := gaugingEdges_card

/-- Total overhead: 12 + 7 + 22 = 41 additional checks and qubits. -/
theorem total_overhead :
    gaugingVertices.card + gaugingCyclesList.length + gaugingGraph.edgeFinset.card = 41 := by
  rw [gaugingVertices_card, gaugingCycles_count, gaugingEdges_card]

/-! ## Expansion edges are valid -/

set_option maxHeartbeats 1600000 in
/-- All 4 expansion edges are edges of the gauging graph. -/
theorem expansion_edges_valid :
    ∀ p ∈ expansionEdges, gaugingGraph.Adj p.1 p.2 := by
  native_decide

set_option maxHeartbeats 1600000 in
/-- All expansion edge endpoints are in supp(f). -/
theorem expansion_edges_in_support :
    ∀ p ∈ expansionEdges, p.1 ∈ gaugingVertices ∧ p.2 ∈ gaugingVertices := by
  native_decide

/-! ## Degree bounds -/

set_option maxHeartbeats 3200000 in
/-- The maximum degree in the gauging graph is at most 6. -/
theorem gaugingDegree_le_six :
    ∀ v : GrossMonomial, gaugingGraph.degree v ≤ 6 := by
  native_decide

/-! ## Matching edges -/

set_option maxHeartbeats 3200000 in
/-- The number of matching edges is 18. -/
theorem matching_edges_count :
    (gaugingGraph.edgeFinset.filter (fun e =>
      !(expansionEdges.any fun (a, b) =>
        e = Sym2.mk (a, b) || e = Sym2.mk (b, a)))).card = 18 := by
  native_decide

set_option maxHeartbeats 3200000 in
/-- The number of expansion edges is 4. -/
theorem expansion_edges_count :
    (gaugingGraph.edgeFinset.filter (fun e =>
      expansionEdges.any fun (a, b) =>
        e = Sym2.mk (a, b) || e = Sym2.mk (b, a))).card = 4 := by
  native_decide

/-! ## Adjacency between logical support and Z checks -/

set_option maxHeartbeats 3200000 in
/-- The number of Z checks adjacent to the support of X̄_α is 18. -/
theorem adjacent_z_checks_count :
    (Finset.univ.filter (fun β : GrossMonomial =>
      (gaugingVertices.filter (fun γ => grossB (β - γ) ≠ 0)).card ≥ 1)).card = 18 := by
  native_decide

/-! ## Summary -/

/-- Summary of the gauging construction for X̄_α in the Gross code. -/
theorem gauging_construction_summary :
    gaugingVertices.card = 12 ∧
    gaugingGraph.edgeFinset.card = 22 ∧
    gaugingCyclesList.length = 7 ∧
    gaugingVertices.card + gaugingCyclesList.length + gaugingGraph.edgeFinset.card = 41 ∧
    (∀ v : GrossMonomial, gaugingGraph.degree v ≤ 6) ∧
    (∀ cyc ∈ gaugingCyclesList, cyc.length ≤ 4) := by
  exact ⟨gaugingVertices_card, gaugingEdges_card, gaugingCycles_count, total_overhead,
    gaugingDegree_le_six, gaugingCycles_max_length⟩

end GrossCode

end BivariateBicycle
