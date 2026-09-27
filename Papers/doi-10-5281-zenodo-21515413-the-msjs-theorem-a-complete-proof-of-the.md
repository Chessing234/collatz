# doi-10-5281-zenodo-21515413-the-msjs-theorem-a-complete-proof-of-the

Citation: (sobeh), mahmoud sabri jaber, "The MSJS Theorem: A Complete Proof of the Collatz Conjecture via Pattern Invariance, Finite-State Reduction, and Loop Contraction", Zenodo, DOI:10.5281/zenodo.21515413 [2026].

Authors: (sobeh), mahmoud sabri jaber

DOI: [10.5281/zenodo.21515413](https://doi.org/10.5281/zenodo.21515413)

Year: 2026

Venue: Zenodo

Classification: cycle

Abstract:

This work presents a complete and rigorous proof of the Collatz conjecture, formalized as the MSJS Theorem. The proof is built upon a fundamental observation: the Collatz map is a network of recurring loops governed solely by the units digit. Every odd number has a mandatory entry into a specific even number, while every even number has two possible exits determined by the tens digit — one when X2 is even, and another when X2 is odd (a +5 offset). This simple rule confines all positive integers to a finite network of cycles that inevitably lead to the absorbing cycle 1 -> 4 -> 2 -> 1. The result is proven by exhaustive verification over the finite core (X3, X2, X1) consisting of exactly 1000...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_21515413.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-p (2026-09-16)
