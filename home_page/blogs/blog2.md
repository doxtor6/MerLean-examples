[MerLean-prover](https://arthurmerlean.com/) is a direct extension of the autoformalization component of [MerLean](https://arthurmerlean.com/), built to prove Lean theorems. It is part of MerLean2, a larger system designed to automatically conduct frontier research in mathematics and applied mathematics, especially in quantum computation.

We tested MerLean-prover on [FormalQualBench](https://www.math.inc/formalqualbench), a benchmark of 23 graduate-level theorems formalized in Lean 4, designed to evaluate automated formalization agents. Unlike scaffolded benchmarks, agents receive only expert-verified Lean statements and must construct their own definitions, lemmas, and proof strategies from scratch. Correctness is verified by Comparator, which checks that proofs compile, prove the intended statement, and use no disallowed axioms.

## Results

So far, MerLean-prover has been tested on the first 8 of 23 problems, solving all of them — all 82 statements at 100% success rate, with no axioms and no sorry. The remaining 14 problems will be tested and results updated later. Full results and Lean source code are available at [MerLean_FormalQualBench](https://github.com/doxtor6/MerLean_FormalQualBench).

| Problem | Area | Solved (within 4 hours) | Duration | Est. Cost |
|---------|------|--------|----------|-----------|
| DeBruijnErdos | Graph Theory | Yes (Yes) | 23m | $9.00 |
| JordanDerangementTheorem | Group Theory | Yes (Yes) | 36m | $20.37 |
| ParisHarringtonPrinciple | Combinatorics / Logic | Yes (Yes) | 1h 46m | $57.33 |
| ColorfulCaratheodoryTheorem | Combinatorial Geometry | Yes (Yes) | 2h 50m | $108.75 |
| DLOQuantifierElimination | Model Theory / Logic | Yes (Yes) | 3h 58m | $172.32 |
| BanachStoneTheorem | Functional Analysis | Yes (No) | 5h 33m | $162.45 |
| GleasonKahaneZelazkoTheorem | Functional Analysis | Yes (Yes) | 2h 16m | $126.48 |
| VonNeumannDoubleCommutantTheorem | Operator Algebras | Yes (Yes) | 2h 4m | $77.22 |
| **Total** | | **8/8** | **~19h** | **$733.92** |

Average cost per solved problem: **~$91.74**. Cost estimated using Claude Opus 4.6 API pricing (input $15/MTok, output $75/MTok, cache write $18.75/MTok, cache read $1.50/MTok).

## Run Details

- **N = 1.** Single attempt per problem, no cherry-picking.
- **No human in the loop.** MerLean-prover's autoformalization pipeline runs autonomously: extract statements from the paper, formalize each statement in Lean 4, compile, fix errors, and verify faithfulness.
- **Comparator-verified.** Every proof checked by Comparator for correctness and no illegal axioms.
- **MerLean-prover + Claude Opus 4.6.** Uses [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) for proof state inspection.

## Remaining Problems

The following 14 problems have not yet been tested and will be attempted next. We expect MerLean-prover to solve some of these that other systems have not, within the 4-hour time constraint.

BorsukUlamTheorem, BurnsidePrimeDegreeTheorem, CollatzMapAlmostBoundedValues, ErdosDiscrepancyProblem, GreenTaoTheorem, Hilbert17thProblem, JordanCycleTheorem, KakeyaTheorem3D, MaynardTaoBoundedPrimeGaps, PontryaginDuality, QuillenSuslinTheorem, RungeTheorem, SchauderFixedPointTheorem, TernaryGoldbachTheorem

Stay tuned for updates as we work through the rest of the benchmark!
