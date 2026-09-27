# doi-10-33774-coe-2021-9w3gs-orbits-theory-a-complete-proof-of-the-co

Citation: Jorge Crespo, "Orbits Theory. A Complete Proof of the Collatz Conjecture", DOI:10.33774/coe-2021-9w3gs [2021].

Authors: Jorge Crespo

DOI: [10.33774/coe-2021-9w3gs](https://doi.org/10.33774/coe-2021-9w3gs)

Year: 2021

Venue: (unknown)

Classification: structural

Abstract:

In this work a complete proof of the Collatz Conjecture is presented. The solution assumes as hypothesis that Collatz's Conjecture is a consequence. We found that every natural number n_i∈N can be calculated starting from 1, using the function n_i=((2^(i-Ω)-C))⁄3^Ω , where: i≥0 represents the number of steps (operations of multiplications by two subtractions of one and divisions by three) needed to get from 1 to n_i, Ω≥0 represents the number of multiplications by three required and 0≤C≤2^(i-⌊i/3⌋ )-2^((i mod 3)) 3^⌊i/3⌋ is an accumulative constant that takes into account the order in which the operations of multiplication and division have been performed. Reversing the inversion, we have obtained the function: ((3^Ω n_i+C))⁄2^(i-Ω)=1 that proves that Collatz Conjecture it’s a consequence...

Lean file: `Collatz/Papers/Journal_10_33774_coe_2021_9w3gs.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-g (2026-09-15)
