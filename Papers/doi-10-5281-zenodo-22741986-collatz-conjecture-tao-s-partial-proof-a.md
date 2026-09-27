# doi-10-5281-zenodo-22741986-collatz-conjecture-tao-s-partial-proof-a

Citation: Andrew Stewart Caldin, "Collatz Conjecture: Tao's Partial Proof and a Claimed Full Solution via Cayley Graphs — E8 Intelligence Research", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22741986 [2026].

Authors: Andrew Stewart Caldin

DOI: [10.5281/zenodo.22741986](https://doi.org/10.5281/zenodo.22741986)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: density

Abstract:

FINDING: Collatz conjecture remains unproven; strongest recent result is Tao's partial proof (2019) showing almost all orbits are bounded below by any diverging function, plus a novel arxiv paper framing it as an automorphic Cayley colour graph with a claimed full proof (unverified). | MATH: Collatz map T(n) = n/2 if n even, (3n+1)/2 if n odd; conjecture: ∀n∈ℕ, ∃k: T^k(n)=1. Tao's result: for f(n)→∞, lim_{N→∞} (1/N)Σ_{n≤N} 1_{sup_{k≤f(n)} T^k(n) < f(n)} = 1. Arxiv 2008.13643v8 claims proof via reverse rule n→(m·2^n−1)/3, constructing a Cayley graph with root cycle 4→2→1→4. | CONNECTION: The arxiv paper's Cayley colour graph framing suggests a lattice/root-system structure — the Collatz map a...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_22741986.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-k (2026-09-16)
