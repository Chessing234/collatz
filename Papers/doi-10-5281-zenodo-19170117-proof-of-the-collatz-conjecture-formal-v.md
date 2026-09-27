# doi-10-5281-zenodo-19170117-proof-of-the-collatz-conjecture-formal-v

Citation: Eduardo Andres, Garcia Lecaros, "Proof of the Collatz conjecture - Formal Verification in Lean 4", DOI:10.5281/zenodo.19170117 [2026].

Authors: Eduardo Andres, Garcia Lecaros

DOI: [10.5281/zenodo.19170117](https://doi.org/10.5281/zenodo.19170117)

Year: 2026

Venue: (unknown)

Classification: verification

Abstract:

We establish a structural resolution of the Collatz Conjecture. The proof proceeds through a strict interception of the scalar cycle equation over the Syracuse dynamics. We demonstrate that any hypothetical cycle defines a forced mixed-radix expansion satisfying the identity n * (2^K - 3^m) = S, where the accumulator S is strictly positive. We introduce the Diophantine Sign Lemma, which proves that if the average of even projections falls below the viability threshold (K/m < log_2(3)), the fraction collapses, forcing the cycle into the negative integers. Conversely, if the cycle operates in the strictly positive regime, we apply the Schmidt Subspace Theorem for S-unit equations to prove the algebraic disjointness of the accumulator, rendering the space of integer solutions empty....

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_19170117.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-j (2026-09-15)
