# doi-10-33774-coe-2025-f00x5-v2-partial-sums-of-the-3x-1-accumulation-te

Citation: Sebastien Riche, "PARTIAL SUMS OF THE 3X+1 ACCUMULATION TERM", DOI:10.33774/coe-2025-f00x5-v2 [2025].

Authors: Sebastien Riche

DOI: [10.33774/coe-2025-f00x5-v2](https://doi.org/10.33774/coe-2025-f00x5-v2)

Year: 2025

Venue: (unknown)

Classification: structural

Abstract:

The "3x+1" accumulation term, E(v_k), is what becomes of the "+1" part after k iteration of the "shortcut" Collatz function T(n) which takes odd integers n to (3n+1)/2 and even integers n to n/2, so T^k(n)=(3^i*n+E(v_k))/2 where i is the number of odd terms in the trajectory of n. A known and easy to prove result is that the total sum of the accumulation terms of all the 2^k possible parity vectors v_k of length k is k4^(k-1). This paper will show that the partial sum of the accumulation terms of all vectors v_k of length k for a fixed value of i is the sum from p=0 to i-1 of the binomial(k,p)*(2^k - 3^p). A very insightful proof of this will be presented, as well as a more classical one.

Lean file: `Collatz/Papers/Journal_10_33774_coe_2025_f00x5_v2.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-l (2026-09-16)
