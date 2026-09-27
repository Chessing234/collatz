# doi-10-5281-zenodo-18641817-the-collatz-conjecture-as-a-quasi-closed

Citation: Ziadah, "The Collatz Conjecture as a Quasi-Closed Cycle", Zenodo, DOI:10.5281/zenodo.18641817 [2026].

Authors: Ziadah

DOI: [10.5281/zenodo.18641817](https://doi.org/10.5281/zenodo.18641817)

Year: 2026

Venue: Zenodo

Classification: cycle

Abstract:

This paper derives an algebraic equivalence from the Collatz Conjecture using the transformation: x = (n - 1) / 4 Under this transformation, every positive natural number n can be written as: n = 4x + 1 This representation decomposes the positive integers into four quartic categories according to the fractional part of x: x = k x = k + 1/2 x = k + 1/4 x = k + 3/4 where k is an integer. Thus, the quartic lattice is: Q = { k, k + 1/4, k + 1/2, k + 3/4 | k ∈ Z } Rewriting the Collatz map: If n is even: T(n) = n / 2 If n is odd: T(n) = 3n + 1 In terms of x, the dynamics become two affine transformations: Even branch: x → ((4x + 1) / 8) - 1/4 Odd branch: x → 3x + 1 Therefore, the iteration is gov...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_18641817.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-q (2026-09-16)
