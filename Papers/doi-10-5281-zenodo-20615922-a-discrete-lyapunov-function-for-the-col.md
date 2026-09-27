# doi-10-5281-zenodo-20615922-a-discrete-lyapunov-function-for-the-col

Citation: Perez Burelli, Pedro Luis, "Ψ — A Discrete Lyapunov Function for the Collatz Conjecture: Reduction to a Single Combinatorial Lemma on Ternary Digits", Zenodo, DOI:10.5281/zenodo.20615922 [2026].

Authors: Perez Burelli, Pedro Luis

DOI: [10.5281/zenodo.20615922](https://doi.org/10.5281/zenodo.20615922)

Year: 2026

Venue: Zenodo

Classification: density

Abstract:

We present a refined discrete Lyapunov function Ψ(n) = ln(n) − 6·h₃(n) + α·v₂(n) + 0.1·|sin(2π·543·ln n)| for the Collatz conjecture, where h₃(n) denotes the base-3 digit sum, v₂(n) the 2-adic valuation, and α a calibrated parameter. We prove algebraically that Ψ strictly decreases on every odd iteration (Lemmas L1 and L2, fully closed), and reduce the complete problem to a single combinatorial lemma (L3): the universal bound h₃(n/2) ≤ h₃(n) for all even n, concerning ternary digit representations under binary division. We verify Ψ(T(n)) < Ψ(n) for all n < 10¹⁵ with zero counterexamples, and integrate Tao's (2022) logarithmic density result into a Hybrid Corollary. The valid parameter window...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20615922.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-q (2026-09-16)
