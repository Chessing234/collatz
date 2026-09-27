# arxiv-2309-09991-the-proof-of-the-collatz-conjecture

Citation: Chin‐Long Wey, "The Proof of the Collatz Conjecture", arXiv:2309.09991 [2023].

Authors: Chin‐Long Wey

arXiv: [2309.09991](https://arxiv.org/abs/2309.09991)

Year: 2023

Classification: verification

Abstract:

The 3n+1, or Collatz problem, is one of the hardest math problems, yet still unsolved. The Collatz conjecture is to prove or disprove that the Collatz sequences COL(n) always eventually reach the number of 1, for all n belongs to N+ (all positive integers). The Syracuse conjecture is a (2N+1)-version of Collatz conjecture, where (2N+1) is all odd integers. The Syracuse and Collatz problem can be conceptually described by a tree trunk and branches. The trunk is made of the junctions that produce the main branches, where J0=1 is the root junction. Each branch consists of active and dead junctions, where only the active junctions are capable of producing new sub-branches. Conceptually assuming the trunk and branches can grow indefinitely and can also absorb nutrients from the root. As the tree grows indefinitely, all N+ (2N+1) are included for the Collatz (Syracuse) sequence. This paper develops both inverse Collatz (Syracuse) functions to construct the tree trunk and branches starting fr

Lean file: `Collatz/Papers/Arxiv2309_09991.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
