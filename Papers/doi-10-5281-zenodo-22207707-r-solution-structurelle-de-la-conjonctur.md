# doi-10-5281-zenodo-22207707-r-solution-structurelle-de-la-conjonctur

Citation: Jean Patrick Yann Orphée Brou, "Résolution structurelle de la conjoncture de collatz par classification multiplicative des entiers", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22207707 [2026].

Authors: Jean Patrick Yann Orphée Brou

DOI: [10.5281/zenodo.22207707](https://doi.org/10.5281/zenodo.22207707)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: cycle

Abstract:

The Collatz conjecture, formulated in 1937, states that by iteratively applying the rule n \to n/2 if n is even, and n \to 3n+1 if n is odd, every positive integer eventually reaches the trivial cycle 4 \to 2 \to 1 . In this paper, I present a complete proof of this conjecture. My method relies on an original classification of integers based on their prime factorization. I define a projection function f that skips directly from one odd number to the next, and I introduce a step counter t to track the evolution of the sequence. By partitioning odd numbers into four groups (A, B, C, D), I prove two fundamental lemmas: (1) every composite odd number projects, after a finite number of steps, ont...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_22207707.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-l (2026-09-16)
