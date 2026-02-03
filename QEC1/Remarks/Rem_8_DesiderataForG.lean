import QEC1.Remarks.Rem_5_CheegerConstantDefinition
import QEC1.Definitions.Def_1_BoundaryCoboundaryMaps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic

/-!
# Rem_8: Desiderata for Graph G in Gauging Measurement

## Statement
When choosing the graph $G$ for the gauging measurement procedure, three desiderata guide
the selection to achieve constant qubit overhead and maintain fault tolerance:

1. **Short paths**: $G$ should contain a constant-length edge-path between any pair of vertices
   that are in the $Z$-type support of some check from the original code. This ensures
   deformed checks have bounded weight.

2. **Sufficient expansion**: The Cheeger constant should satisfy $h(G) \geq 1$. This ensures
   the deformed code distance is at least as large as the original code distance.

3. **Low-weight cycles**: There should be a generating set of cycles for $G$ where each cycle
   has weight at most some constant. This ensures the $B_p$ flux operators have bounded weight.

When such a graph is found, the gauging measurement procedure has constant qubit overhead.

## Main Definitions
- `ShortPathsProperty`: Desideratum 1 - constant-length paths between Z-type support vertices
- `SufficientExpansion`: Desideratum 2 - Cheeger constant h(G) ≥ 1
- `LowWeightCyclesProperty`: Desideratum 3 - generating cycles with bounded weight
- `GaugingGraphDesiderata`: All three desiderata together

## Informal Justifications (as stated in the remark)
- Short paths ⟹ deformed checks have bounded weight
- h(G) ≥ 1 ⟹ deformed code distance ≥ original code distance
- Low-weight cycles ⟹ B_p flux operators have bounded weight
- All three ⟹ constant qubit overhead
-/

namespace QEC1

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Desideratum 1: Short Paths Property -/

/-- **Desideratum 1: Short Paths Property**

    G should contain a constant-length edge-path between any pair of vertices
    that are in the Z-type support of some check from the original code.

    Parameters:
    - `G`: the graph
    - `zTypeSupports`: collection of Z-type support sets from stabilizer checks
    - `k`: the constant path length bound

    The property states: for any Z-type support set S, and any u, v ∈ S,
    there exists a walk from u to v in G of length at most k. -/
def ShortPathsProperty (G : SimpleGraph V) (zTypeSupports : Finset (Finset V)) (k : ℕ) : Prop :=
  ∀ S ∈ zTypeSupports, ∀ u ∈ S, ∀ v ∈ S, ∃ p : G.Walk u v, p.length ≤ k

/-! ## Desideratum 2: Sufficient Expansion -/

/-- **Desideratum 2: Sufficient Expansion**

    The Cheeger constant should satisfy h(G) ≥ 1.
    This is exactly the `IsStrongExpander` property from Rem_5. -/
def SufficientExpansion (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  IsStrongExpander G

/-- Sufficient expansion means h(G) ≥ 1 -/
lemma sufficientExpansion_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    SufficientExpansion G ↔ CheegerConstant G ≥ 1 := Iff.rfl

/-! ## Desideratum 3: Low-Weight Cycles Property -/

/-- **Desideratum 3: Low-Weight Cycles Property**

    There should be a generating set of cycles for G where each cycle has weight
    (number of edges) at most some constant w.

    A cycle is represented as a set of edges. The "generating set" property means
    the cycles span the kernel of the boundary map (cycle space) over Z₂.

    Parameters:
    - `G`: the graph with a chosen collection of cycles
    - `w`: the constant weight bound

    For a GraphWithCycles structure, we check that all cycles have bounded weight. -/
def LowWeightCyclesProperty {E C : Type*} [DecidableEq E] [DecidableEq C]
    [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C) (w : ℕ) : Prop :=
  ∀ c : C, (G.cycles c).card ≤ w

/-! ## Combined Desiderata -/

/-- **The Three Desiderata for Gauging Graph G**

    A graph satisfies the gauging desiderata if:
    1. Short paths (bounded by k) between vertices in Z-type supports
    2. Sufficient expansion: h(G) ≥ 1
    3. Low-weight cycles (bounded by w) in a generating set

    The informal justification from the remark:
    - (1) ensures deformed checks have bounded weight
    - (2) ensures deformed code distance ≥ original code distance
    - (3) ensures B_p flux operators have bounded weight
    - All three together ensure constant qubit overhead -/
structure GaugingGraphDesiderata {E C : Type*} [DecidableEq E] [DecidableEq C]
    [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C) [DecidableRel G.graph.Adj]
    (zTypeSupports : Finset (Finset V))
    (pathBound : ℕ) (cycleBound : ℕ) : Prop where
  /-- Desideratum 1: Short paths between Z-type support vertices -/
  short_paths : ShortPathsProperty G.graph zTypeSupports pathBound
  /-- Desideratum 2: Cheeger constant h(G) ≥ 1 -/
  expansion : SufficientExpansion G.graph
  /-- Desideratum 3: All generating cycles have weight at most cycleBound -/
  low_weight_cycles : LowWeightCyclesProperty G cycleBound

/-! ## Informal Consequences (as stated in the remark)

The remark states the following informal implications. These are not proven here
as they depend on the full gauging construction from other definitions:

1. **Short paths ⟹ bounded deformed check weight**:
   If original check has Z-type support S and we have paths of length ≤ k,
   the deformed check adds at most k · |S|/2 additional edge operators.

2. **h(G) ≥ 1 ⟹ distance preservation**:
   The deformed code distance is at least as large as the original code distance.

3. **Low-weight cycles ⟹ bounded flux operator weight**:
   Each flux operator B_p = ∏_{e ∈ p} Z_e has weight at most w (the cycle bound).

4. **All three ⟹ constant qubit overhead**:
   The gauging measurement procedure has qubit overhead O(1) per original qubit.
-/

/-- The consequence of desideratum 3: flux operator weight is bounded by cycle weight.
    This is immediate from the definition of flux operators B_p = ∏_{e ∈ p} Z_e. -/
lemma flux_operator_weight_bounded {E C : Type*} [DecidableEq E] [DecidableEq C]
    [Fintype E] [Fintype C]
    (G : GraphWithCycles V E C) (w : ℕ)
    (hlw : LowWeightCyclesProperty G w) (c : C) :
    (G.cycles c).card ≤ w :=
  hlw c

end QEC1
