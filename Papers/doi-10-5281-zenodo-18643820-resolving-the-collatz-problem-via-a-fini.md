# doi-10-5281-zenodo-18643820-resolving-the-collatz-problem-via-a-fini

Citation: Toru Kawahara, "Resolving the Collatz Problem via a Finite-State Phase Machine Structural Absorption, Core Phases, and Exhaustive Bounded Delay", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18643820 [2026].

Authors: Toru Kawahara

DOI: [10.5281/zenodo.18643820](https://doi.org/10.5281/zenodo.18643820)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: verification

Abstract:

This paper presents a complete structural resolution of the odd-only Collatz problem via an explicit finite-state reformulation. The Collatz dynamics are reconstructed as a deterministic finite-state phase machine by compressing odd integers into phase states modulo a fixed power of two. Within this framework, global behavior is reduced from an infinite iterative process to a finite reachability problem on a fully enumerable transition graph. In contrast to the previous version (v0.5, DOI: https://doi.org/10.5281/zenodo.18446986), the present release provides an exhaustive certification of global reachability and bounded absorption. All states of the finite-state machine are shown to reach a small absorbing core consisting of the phases {1, 5, 17}, with a uniformly bounded delay. The...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_18643820.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-h (2026-09-15)
