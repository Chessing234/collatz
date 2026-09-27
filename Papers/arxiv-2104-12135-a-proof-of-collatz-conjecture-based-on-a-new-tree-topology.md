# arxiv-2104-12135-a-proof-of-collatz-conjecture-based-on-a-new-tree-topology

Citation: Hassan Rezai Soleymanpour, "A Proof of Collatz Conjecture Based on a New Tree Topology", arXiv:2104.12135 [2021].

Authors: Hassan Rezai Soleymanpour

arXiv: [2104.12135](https://arxiv.org/abs/2104.12135)

Year: 2021

Classification: cycle

Abstract:

Consider a finite positive integer. If it is even, divide it by 2, and if it is odd, multiply it by 3 and add 1. This will give you a new integer. Following the procedure for the new integer, you will receive another integer. Repeat the steps, and after a few repetitions, you will finally reach 1. Collatz conjecture states that the final integer in the mentioned process will always be 1, no matter what integer it starts with. Although the procedure of the conjecture is easy to describe, its correctness has not yet been confirmed. This article proves the conjecture by introducing a tree topology of it. Given the proposed tree, we can prove that all integers are uniquely distributed on the tree, and there is no cycle other than 1-2-1. We also see how every trajectory ends in 1.

Lean file: `Collatz/Papers/Arxiv2104_12135.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
