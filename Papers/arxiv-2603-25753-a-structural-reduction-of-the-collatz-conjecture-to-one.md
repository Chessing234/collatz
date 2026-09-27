# arxiv-2603-25753-a-structural-reduction-of-the-collatz-conjecture-to-one

Citation: Chang, Edward Y., "A Structural Reduction of the Collatz Conjecture to One-Bit Orbit Mixing", arXiv:2603.25753 [2026].

Authors: Chang, Edward Y.

arXiv: [2603.25753](https://arxiv.org/abs/2603.25753)

Year: 2026

Classification: structural

Abstract:

We reduce the Collatz conjecture to a fixed-modulus, one-bit orbit-mixing problem. Working with the compressed odd-to-odd Collatz map, we prove exact low-depth decomposition formulas at depths K = 3, 4, 5, reducing block-discrepancy terms to explicit run statistics. We then prove a Map Balance Theorem: among the 2^(K-3), 1 burst residues modulo 2^K that initiate gaps, the counts mapping to gap starts congruent to 3 versus congruent to 7 (mod 8) differ by exactly 1 for every K >= 5. Thus all residual bias is orbit-level, not map-level. For the dominant n congruent to 1 (mod 8) class, the gap outcome depends on a single binary variable, bit 4 of the orbit value at burst-ending times, reducing the conjecture to whether every orbit visits two residue classes modulo 32 with sufficient balance along a sparse subsequence.

Lean file: `Collatz/Papers/Arxiv2603_25753.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
