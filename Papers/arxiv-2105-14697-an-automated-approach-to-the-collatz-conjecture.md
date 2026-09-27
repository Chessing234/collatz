# arxiv-2105-14697-an-automated-approach-to-the-collatz-conjecture

Citation: Emre Yolcu et al., "An Automated Approach to the Collatz Conjecture", arXiv:2105.14697 [2021].

Authors: Emre Yolcu, Scott Aaronson, Marijn J. H. Heule

arXiv: [2105.14697](https://arxiv.org/abs/2105.14697)

Year: 2021

Classification: structural

Abstract:

We explore the Collatz conjecture and its variants through the lens of termination of string rewriting. We construct a rewriting system that simulates the iterated application of the Collatz function on strings corresponding to mixed binary-ternary representations of positive integers. We prove that the termination of this rewriting system is equivalent to the Collatz conjecture. We also prove that a previously studied rewriting system that simulates the Collatz function using unary representations does not admit termination proofs via natural matrix interpretations, even when used in conjunction with dependency pairs. To show the feasibility of our approach in proving mathematically interesting statements, we implement a minimal termination prover that uses natural/arctic matrix interpretations and we find automated proofs of nontrivial weakenings of the Collatz conjecture. Although we do not succeed in proving the Collatz conjecture, we believe that the ideas here represent an intere

Lean file: `Collatz/Papers/Arxiv2105_14697.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
