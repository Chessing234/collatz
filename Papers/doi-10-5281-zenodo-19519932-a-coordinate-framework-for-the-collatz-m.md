# doi-10-5281-zenodo-19519932-a-coordinate-framework-for-the-collatz-m

Citation: Neel Alkoraishi, "A Coordinate Framework for the Collatz Map via Branch Decomposition", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19519932 [2026].

Authors: Neel Alkoraishi

DOI: [10.5281/zenodo.19519932](https://doi.org/10.5281/zenodo.19519932)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: cycle

Abstract:

I present a deterministic framework for analyzing the Collatz map via abranch decomposition using coordinates (x, k, y) and branch endpoints C(x, k).Every positive integer lies on a uniquely determined branch, while even integersare represented via powers of 2.Within each branch, the coordinate sum x + y strictly decreases under iter-ation of the Collatz map. Across branches, the directed acyclic graph (DAG) ofbranch endpoints defines a branch index I(C) that strictly decreases along everypath. Combining these two monotone quantities into a lexicographic LyapunovfunctionL(n) := (I(C), x + y)ensures global descent.Branch reparameterization at transitions is bounded, preventing unboundedgrowth that could otherwise block descent. Consequently, all trajectories even-tually reach the unique...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_19519932.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
