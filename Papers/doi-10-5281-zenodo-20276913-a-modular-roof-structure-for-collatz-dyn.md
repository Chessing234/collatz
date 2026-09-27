# doi-10-5281-zenodo-20276913-a-modular-roof-structure-for-collatz-dyn

Citation: William Betancourt Reyes, "A Modular Roof Structure for Collatz Dynamics and a Reduction to Strict Descent Between Local Maxima", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20276913 [2026].

Authors: William Betancourt Reyes

DOI: [10.5281/zenodo.20276913](https://doi.org/10.5281/zenodo.20276913)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: verification

Abstract:

This work introduces a modular framework for analyzing the dynamics of the Collatz function through two key constructions: a modular transformation 𝑆(𝑛), based on congruences modulo 18, and a roof function 𝑇(𝑛), which assigns a controlled local maximum within each orbit. Using these roofs, we define a descent function 𝐹(𝑇) that tracks the even values immediately following odd ones in the Collatz trajectory. Computational evidence shows that every chain of roofs eventually reaches the minimal roof 16, although temporary upward jumps may occur. Once a stable roof 𝑇=𝑝(𝑇)is reached, the descent becomes strictly monotonic. This suggests that the global Collatz dynamics can be reduced to the discrete study of 𝐹 over roofs, revealing a rigid modular structure underlying Collatz orbits.

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20276913.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
