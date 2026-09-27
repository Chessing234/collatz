# doi-10-5281-zenodo-19476171-a-computer-assisted-well-founded-descent

Citation: REDERO, Julien, "A computer-assisted well-founded descent for Collatz components under dyadic leaf certificates", DOI:10.5281/zenodo.19476171 [2026].

Authors: REDERO, Julien

DOI: [10.5281/zenodo.19476171](https://doi.org/10.5281/zenodo.19476171)

Year: 2026

Venue: (unknown)

Classification: verification

Abstract:

We present a component-wise descent framework for the Collatzproblem based on a combination of analytic reduction and finite veri-fication organized over a dyadic hierarchy.The argument proceeds by reducing the problem to odd multiplesof 3 using an anti-9 lifting mechanism, and introducing a valuationparameter e(u) = v2(9u + 1) that governs the dynamics.For the regime e(u) ≥ 7, we construct an explicit analytic descentmap u 7 → u∗ = (u − 7)/64 which strictly decreases u while preservingconnected components of the Collatz graph.For the complementary regime e(u) ≤ 6, we introduce a recursivehierarchy of dyadic residue classes moduloMt = 9 · 214+6t,and associate to each leaf a certificate encoding a finite sequence ofaccelerated iterations together with a descent inequality.The key technical...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_19476171.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
