# doi-10-5281-zenodo-19709214-an-unconditional-proof-of-the-collatz-co

Citation: Liu, Xingming, "An Unconditional Proof of the Collatz Conjecture under the Modulo-6 Framework", DOI:10.5281/zenodo.19709214 [2026].

Authors: Liu, Xingming

DOI: [10.5281/zenodo.19709214](https://doi.org/10.5281/zenodo.19709214)

Year: 2026

Venue: (unknown)

Classification: structural

Abstract:

This paper presents an unconditional proof of the Collatz conjecture. The proof is based on the "modulo-6 framework"—every positive integer can be uniquely expressed as N = 2ᵃ·3ᵇ·M, where M = 1, or M = 6n−1 (yin number), or M = 6n+1 (yang number) with n ∈ ℕ ⁺ . This framework automatically strips away the factors 2 and 3 in the Collatz iteration, reducing the conjecture to the convergence of yin and yang numbers. By introducing a classification of the parameter n modulo 2ˢ, we construct a deterministic finite automaton whose state set is = (ℤ /2ˢℤ ) × {−, +}. Furthermore, we prove that all odd numbers generated along any orbit belong to a uniform algebraic form X = K·3ᵃ·m + B, where K ∈ {1,2,4}, a ≥ 0, m satisfies certain modulo conditions, and B belongs to a finite constant set. Based on...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_19709214.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
