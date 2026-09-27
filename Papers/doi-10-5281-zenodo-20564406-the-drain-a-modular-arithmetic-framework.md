# doi-10-5281-zenodo-20564406-the-drain-a-modular-arithmetic-framework

Citation: Jaludi, Abdul, "The Drain: A Modular Arithmetic Framework for the Collatz Conjecture", DOI:10.5281/zenodo.20564406 [2026].

Authors: Jaludi, Abdul

DOI: [10.5281/zenodo.20564406](https://doi.org/10.5281/zenodo.20564406)

Year: 2026

Venue: (unknown)

Classification: verification

Abstract:

This paper develops a modular arithmetic framework for the Collatz conjecture using the compressed function f(n) = n/2 for even n and f(n) = (3n+1)/2 for odd n. The Core Theorem establishes that every odd-even compressed cycle strictly decreases log(n) by at least log(2) - log(3/2) = 0.2877, verified across 62,701 cycles. A No-Cycle Theorem follows: no non-trivial cycle exists under the compressed function terminating at a power of 2. Analysis of 148 known delay records reveals two universal structural constants: steps per run = 4.111 and odd steps per run = 2.484, both stable to within 2.5% across all records. For paths with odd step fraction near 0.606, each digit count occupies an 84.1-step window -- a hard constraint derived from LOG10 / (LOG2 - 0.606 x LOG3) = 84.1. Every Family A...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20564406.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-j (2026-09-15)
