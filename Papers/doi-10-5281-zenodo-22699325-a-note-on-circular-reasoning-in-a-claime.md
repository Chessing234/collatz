# doi-10-5281-zenodo-22699325-a-note-on-circular-reasoning-in-a-claime

Citation: Lafontaine, Mary and Cheong, Gerard, "A Note on Circular Reasoning in a Claimed Proof of the Collatz Conjecture", Zenodo, DOI:10.5281/zenodo.22699325 [2026].

Authors: Lafontaine, Mary, Cheong, Gerard

DOI: [10.5281/zenodo.22699325](https://doi.org/10.5281/zenodo.22699325)

Year: 2026

Venue: Zenodo

Classification: verification

Abstract:

We identify circular reasoning in the recent proof of the Collatz conjecture claimed by Mirkowska and Salwicki. The authors infer that no infinite Collatz computation exists because their graph consists of standard natural numbers, although an infinite path may contain only standard integers. They then introduce, for every initial value \(r\), a finite iteration count \(i(r)\) at which the trajectory reaches \(1\), thereby assuming the very termination property to be proved. Consequently, neither the claimed recursive construction nor the subsequent application of an infinitary inference rule establishes the Collatz conjecture.

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_22699325.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-q (2026-09-16)
