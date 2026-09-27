# doi-10-5281-zenodo-18892856-a-structural-reduction-framework-for-the

Citation: Yoshiki Ueoka et al., "A Structural Reduction Framework for the Collatz Problem via Alternating Binary Notation, Collatz Phase Expression, and a Lean-Supported Proof Architecture", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18892856 [2026].

Authors: Yoshiki Ueoka, Taichi Hyuga, Hojin Yamadori

DOI: [10.5281/zenodo.18892856](https://doi.org/10.5281/zenodo.18892856)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: verification

Abstract:

We present a structural reduction framework for the Collatz problem based on Alternating Binary Notation (ABN) and Collatz Phase Expression (CPE).Instead of treating the iteration as orbit-tracing on integers viewed as isolated points, we encode odd states by signed binary block structures and analyze the accelerated odd map$F(n)=\frac{3n+1}{2^{v_2(3n+1)}}$as a local rewriting process on CPE. The key point is that one-step updates are confined to a constant-size local window.From this locality, we derive inequalities for structural quantities such as the chain count $\mu$, the total chain length $H_{CS}$, the total node length $H_K$, and the total length $B=H_{CS}+H_K$.These inequalities imply that the high-$\mu$ region (in particular, $\mu\ge4$) descends in finitely many steps to the...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_18892856.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-h (2026-09-15)
