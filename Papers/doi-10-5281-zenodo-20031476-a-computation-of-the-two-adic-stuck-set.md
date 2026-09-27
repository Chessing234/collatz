# doi-10-5281-zenodo-20031476-a-computation-of-the-two-adic-stuck-set

Citation: Christopher Clack, "A Computation of the Two-Adic Stuck Set for the Collatz Map", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20031476 [2026].

Authors: Christopher Clack

DOI: [10.5281/zenodo.20031476](https://doi.org/10.5281/zenodo.20031476)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: verification

Abstract:

Let T denote the Syracuse map T(n) = (3n+ 1)/2ν2 (3n+1) on the odd positive integers, where ν2 is the 2-adic valuation. For each K ≥1, let SK be the set of odd residues r (mod 2K) for which the partial sums of log2 3·ν3−log2 2·ν2 along the orbit of r remain non-positive over all Syracuse steps resolvable within K bits of input. The set SK is the natural nite-precision approximation to the set of stuck 2-adic integers those whose Collatz orbits would, if they failed to terminate at 1, fail by drifting to innity rather than entering a non-trivial cycle. We compute |SK| by exact enumeration with 128-bit integer arithmetic for K= 3,4,...,30, and by Monte Carlo sampling for K = 33,50,60,70,80,90,100 (N = 2 ×108 samples per K). At K = 30 the exact enumeration gives |S30|= 11 759 296 survivors...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20031476.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
