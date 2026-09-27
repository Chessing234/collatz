# arxiv-2304-11388-collatz-dynamics-is-partitioned-by-residue-class-regularly

Citation: Wei Ren, "Collatz Dynamics is Partitioned by Residue Class Regularly", arXiv:2304.11388 [2023].

Authors: Wei Ren

arXiv: [2304.11388](https://arxiv.org/abs/2304.11388)

Year: 2023

Classification: verification

Abstract:

We propose Reduced Collatz Conjecture that is equivalent to Collatz Conjecture, which states that every positive integer can return to an integer less than it, instead of 1. Reduced Collatz Conjecture is easier to explore because certain structures must be presented in reduced dynamics, rather than in original dynamics (as original dynamics is a mixture of original dynamics). Reduced dynamics is a computation sequence from starting integer to the first integer less than it, in terms of ``I'' that represents (3*x+1)/2 and ``O'' that represents x/2. We formally prove that all positive integers are partitioned into two halves and either presents ``I'' or ``O'' in next ongoing computation. More specifically, (1) if any positive integer x that is i module $2^t$ (i is an odd integer) is given, then the first t computations (each one is either ``I'' or ``O'' corresponding to whether current integer is odd or even) will be identical with that of i. (2) If current integer after t computations (

Lean file: `Collatz/Papers/Arxiv2304_11388.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
