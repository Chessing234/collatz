# arxiv-2403-04777-specifying-and-verifying-the-convergence-stairs-of-the-colla

Citation: Ali Ebnenasir, "Specifying and Verifying the Convergence Stairs of the Collatz Program", arXiv:2403.04777 [2024].

Authors: Ali Ebnenasir

arXiv: [2403.04777](https://arxiv.org/abs/2403.04777)

Year: 2024

Classification: verification

Abstract:

This paper presents an algorithmic method that, given a positive integer $j$, generates the $j$-th convergence stair containing all natural numbers from where the Collatz conjecture holds by exactly $j$ applications of the Collatz function. To this end, we present a novel formulation of the Collatz conjecture as a concurrent program, and provide the general case specification of the $j$-th convergence stair for any $j > 0$. The proposed specifications provide a layered and linearized orientation of Collatz numbers organized in an infinite set of infinite binary trees. To the best of our knowledge, this is the first time that such a general specification is provided, which can have significant applications in analyzing and testing the behaviors of complex non-linear systems. We have implemented this method as a software tool that generates the Collatz numbers of individual stairs. We also show that starting from any value in any convergence stair the conjecture holds. However, to prove 

Lean file: `Collatz/Papers/Arxiv2403_04777.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
