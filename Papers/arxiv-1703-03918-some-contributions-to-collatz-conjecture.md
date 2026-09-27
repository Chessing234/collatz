# arxiv-1703-03918-some-contributions-to-collatz-conjecture

Citation: Livio Colussi, "Some contributions to Collatz conjecture", arXiv:1703.03918 [2017].

Authors: Livio Colussi

arXiv: [1703.03918](https://arxiv.org/abs/1703.03918)

Year: 2017

Classification: verification

Abstract:

The Collatz conjecture can be stated in terms of the reduced Collatz function R(x) = (3x+1)/2^m (where 2^m is the larger power of 2 that divides 3x+1). The conjecture is: Starting from any odd positive integer and repeating R(x) we eventually get to 1. In a previous paper of the author the set of odd positive integers x such that R^k(x) = 1 has been characterized as the set of odd integers whose binary representation belongs to a set of strings G_k. Each string in G_k is the concatenation of k strings z_k z_{k-1} ... z_1 where each z_i is a finite and contiguous extract from some power of a string s_i of length 2x3^{i-1} (the seed of order i). Clearly Collatz conjecture will be true if the binary representation of any odd integer belongs to some G_k. Lately Patrick Chisan Hew showed that seeds s_i are the repetends of 1/3^i. Here two contributions to Collatz conjecture are given: - Colla

Lean file: `Collatz/Papers/Arxiv1703_03918.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
