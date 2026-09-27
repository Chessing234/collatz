# doi-10-5281-zenodo-20314162-collatz-conjecture-a-formal-axiom-system

Citation: Yamamoto, Takeo, "Collatz Conjecture: A Formal Axiom System and Executable Framework Based on Structural Properties in Lean 4", Zenodo, DOI:10.5281/zenodo.20314162 [2026].

Authors: Yamamoto, Takeo

DOI: [10.5281/zenodo.20314162](https://doi.org/10.5281/zenodo.20314162)

Year: 2026

Venue: Zenodo

Classification: cycle

Abstract:

This repository provides a formal axiom system for the Collatz conjecture, fully implemented and verified in the Lean 4 proof assistant. Rather than pursuing a standard ZFC arithmetic derivation, this work establishes that key structural properties of the Collatz map—such as loop prohibition, a deterministic two-step contraction mechanism, and confluent orbit merging—are provable as sorry-free theorems from standard integer axioms. Utilizing the Curry-Howard isomorphism, global convergence is adopted as an independent axiom justified by extensive empirical evidence and computational validation up to $2^{71}$. The resulting framework passes Lean's strict type-checker (CI-verified Green) and s...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20314162.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-o (2026-09-16)
