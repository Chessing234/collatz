# arxiv-1609-00374-collatz-conjecture-for-2-100000-1-is-true-algorithms-fo

Citation: Wei Ren, "Collatz Conjecture for $2^{100000}-1$ is True - Algorithms for Verifying Extremely Large Numbers", arXiv:1609.00374 [2016].

Authors: Wei Ren

arXiv: [1609.00374](https://arxiv.org/abs/1609.00374)

Year: 2016

Classification: verification

Abstract:

Collatz conjecture (or 3x+1 problem) is out for about 80 years. The verification of Collatz conjecture has reached to the number about 60bits until now. In this paper, we propose new algorithms that can verify whether the number that is about 100000bits (30000 digits) can return 1 after 3*x+1 and x/2 computations. This is the largest number that has been verified currently. The proposed algorithm changes numerical computation to bit computation, so that extremely large numbers (without upper bound) becomes possible to be verified. We discovered that $2^{100000}-1$ can return to 1 after 481603 times of 3*x+1 computation, and 863323 times of x/2 computation.

Lean file: `Collatz/Papers/Arxiv1609_00374.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
