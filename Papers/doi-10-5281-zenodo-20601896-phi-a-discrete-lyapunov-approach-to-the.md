# doi-10-5281-zenodo-20601896-phi-a-discrete-lyapunov-approach-to-the

Citation: Perez Burelli, Pedro Luis, "Phi: A Discrete Lyapunov Approach to the Collatz Conjecture - Bioacoustic Resonance, Ternary Digit Sums, and Formal Verification in Lean 4", Zenodo, DOI:10.5281/zenodo.20601896 [2026].

Authors: Perez Burelli, Pedro Luis

DOI: [10.5281/zenodo.20601896](https://doi.org/10.5281/zenodo.20601896)

Year: 2026

Venue: Zenodo

Classification: cycle

Abstract:

We introduce Φ, a discrete Lyapunov-type energy function proposed as a structural approach to the Collatz conjecture. The seed formula is: Φ(n) = ln(n) − 6·h₃(n) + 0.1·|sin(2π·543·ln n)|, where h₃(n) is the base-3 digit sum of n, κ = 6 is an empirically determined constant motivated by a heuristic connection to Ramanujan's identity π/√3, and the oscillatory term at 543 Hz serves as a harmonic dither breaking structural ties. We claim Φ(T(n)) < Φ(n) for all n ≥ 2, implying every Collatz orbit descends to the cycle 1 → 2 → 1. Core components have been partially formalized in Lean 4 without 'sorry' placeholders (file: collatz_vanquished_b2.lean, SHA-256: 6d2e001c…c746e). Empirical verification...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20601896.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-p (2026-09-16)
