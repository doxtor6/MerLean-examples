We evaluated [MerLean](https://arthurmerlean.com/) on "Balanced Product Quantum Codes" by Breuckmann & Eberhardt ([arXiv:2012.09271](https://arxiv.org/abs/2012.09271)) — one of the most important theoretical papers in Quantum Error Correction, with almost 300 citations since 2021. When we fed the paper to MerLean, the system got trapped in an hours-long loop.

![MerLean log showing the loop](/assets/img/blog1_1.png)

To understand why MerLean got stuck, you need to know how it works under the hood. MerLean relies on two components working in tension:

1. **Compile-fix loop:** Translates paper content into Lean 4 and iteratively compiles until the math is sound.
2. **Faithfulness Checker:** An LLM auditor that verifies the Lean code exactly matches the original paper's formulas.

These two engines entered a tug-of-war. The agent, trying to satisfy the compiler, produced correct Lean code that deviated from the paper. The Faithfulness Checker flagged this as unfaithful and restored the original formula. The compiler then refused to compile it. Compile, fail, deviate, flag, restore, fail — stuck in a loop because both components were working perfectly. The root cause in an actual mathematical errors in the paper that had slipped past peer review. We contacted the authors, who confirmed the errors. Fortunately, these mistakes do not affect the main theorem. Once errors are located, we use LLMs to fix the math. Our autoresidual pipeline generates structured errata PDFs with original vs. corrected formulas and Lean evidence: [Errata PDF](https://doxtor6.github.io/MerLean_bpqc/blueprint/errata.pdf). To test whether Lean was essential, we fed the paper directly to Claude Code. While Claude spotted minor typos, it completely missed the mathematical errors. This is where Lean shines: the compiler counters hallucinations and pinpoints the exact discrepancy. 

Autoformalization isn't just about producing Lean code — it can serve as automated proofreading for research papers at the frontier. This is becoming a familiar story in formal mathematics. Joseph Tooby-Smith (PhysLean) [found an error](https://arxiv.org/abs/2603.08139) in a widely cited high-energy physics paper during formalization. Math, inc.'s Gauss [fixed errors](https://x.com/mathematics_inc/status/2028542396779155756) in the original 8-dimensional sphere packing paper. Formalization is becoming a practical tool for catching mistakes in frontier research.

Our formalization does require introducing axioms for well-known theorems not yet in Mathlib, producing a "partial formalization" rather than a fully self-contained proof. But even a partial formalization catches real errors that human reviewers missed — validating the verifier and laying the foundation for our next goal: an autoprover that contributes to frontier research, not just checks it.

We'd love to hear your thoughts, questions, or suggestions!
