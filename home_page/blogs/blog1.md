We evaluated with updated [MerLean](https://arthurmerlean.com/) on "Balanced Product Quantum Codes" by Breuckmann & Eberhardt ([arXiv:2012.09271](https://arxiv.org/abs/2012.09271)) — one of the most important theoretical papers in Quantum Error Correction, with almost 300 citations since 2021. The paper covers deep mathematics including chain complexes, cohomology, CSS & LDPC codes, expander graphs, Cayley graphs, and the LPS construction of Ramanujan graphs, making it an ideal and challenging testbed for autoformalization at the frontier.

The vast majority of the formalization completed successfully, confirming the rigor of the paper's constructions and results. MerLean produced verified Lean 4 code covering the core algebraic structures, the balanced product construction, and the code-theoretic properties. The full formalization can be explored via the [interactive blueprint](https://doxtor6.github.io/MerLean_bpqc/blueprint/) and [dependency graph](https://doxtor6.github.io/MerLean_bpqc/blueprint/dep_graph_document.html). However, at one point MerLean got trapped in an hours-long loop.

![MerLean log showing the loop](/assets/img/blog1_1.png)

To understand why MerLean got stuck, you need to know how it works under the hood. MerLean relies on two components working in tension:

1. **Compile-fix loop:** Translates paper content into Lean 4 and iteratively compiles until the math is sound.
2. **Faithfulness Checker:** An LLM auditor that verifies the Lean code exactly matches the original paper's formulas.

These two engines entered a tug-of-war. The agent, trying to satisfy the compiler, produced correct Lean code that slightly adjusted a constant in the formula. The Faithfulness Checker flagged this as deviating from the source and restored the original. The compiler then refused to compile it. Compile, fail, deviate, flag, restore, fail — stuck in a loop because both components were working perfectly. The root cause turned out to be a small discrepancy in a constant in Theorem 12 — the kind of subtle issue that does not affect the paper's main results. We contacted the authors, who graciously confirmed. Now our agent can correctly handle this situation, automatically resolving the discrepancy and generating a structured errata document with original vs. corrected formulas and Lean evidence.

To test whether Lean was essential, we fed the paper directly to Claude Code. While Claude spotted minor typos, it completely missed the constant discrepancy that triggered the loop. This is where Lean shines: the compiler pinpoints the exact location of the issue with a level of rigor that LLMs alone cannot match.

Formalization-driven proofreading is becoming increasingly common. Joseph Tooby-Smith (PhysLean) [found a discrepancy](https://arxiv.org/abs/2603.08139) in a widely cited high-energy physics paper during formalization. Math, inc.'s Gauss [corrected minor issues](https://x.com/mathematics_inc/status/2028542396779155756) in the original 8-dimensional sphere packing paper. Formalization is becoming a practical complement to peer review.

Our formalization does require introducing axioms for well-known theorems not yet in Mathlib, producing a "partial formalization" rather than a fully self-contained proof. But even a partial formalization validates the logical structure of a paper and lays the foundation for our next goal: an autoprover that contributes to frontier research, not just checks it.

We'd love to hear your thoughts, questions, or suggestions!
