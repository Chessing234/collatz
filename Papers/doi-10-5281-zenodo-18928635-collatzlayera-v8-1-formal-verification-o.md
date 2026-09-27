# doi-10-5281-zenodo-18928635-collatzlayera-v8-1-formal-verification-o

Citation: Novgorodtsev, Aleksei, "CollatzLayerA v8.1 Formal Verification of the Collatz Conjecture in Lean 4 + Mathlib (2636 lines, 215 theorems, 2 axioms, 0 sorry)", Zenodo, DOI:10.5281/zenodo.18928635 [2026].

Authors: Novgorodtsev, Aleksei

DOI: [10.5281/zenodo.18928635](https://doi.org/10.5281/zenodo.18928635)

Year: 2026

Venue: Zenodo

Classification: verification

Abstract:

Formal verification of the Collatz Conjecture in Lean 4 with Mathlib. METRICS: 2636 lines · 215 theorems · 2 axioms · 0 sorry Verified: live.lean-lang.org, Latest Mathlib, March 9, 2026 All Messages (0) The proof operates through algebraic bit constraints: Fresh 3-Bit rank exhaustion, Novgorodtsev parametric identity, noise absorption in ℚ, and contraction certificates. Section §4A bridges to the stochastic mismatch drift theory (Paper1), formalizing β = log₂(4/3) as the universal navigation constant. AXIOMS (2 total, both structurally justified): (1) base_case_109 - computational verification for n < 2^109 (Barina 2020) (2) odd_steps_certificate - Sprint Lock + Markov chain certificate, jus...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_18928635.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-q (2026-09-16)
