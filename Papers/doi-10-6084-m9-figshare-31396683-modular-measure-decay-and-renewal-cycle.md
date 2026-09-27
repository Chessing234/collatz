# doi-10-6084-m9-figshare-31396683-modular-measure-decay-and-renewal-cycle

Citation: Cain, Lukas, "Modular Measure Decay and Renewal-Cycle Contraction for the Collatz Conjecture: A Lean 4 Formalization", figshare, DOI:10.6084/m9.figshare.31396683 [2026].

Authors: Cain, Lukas

DOI: [10.6084/m9.figshare.31396683](https://doi.org/10.6084/m9.figshare.31396683)

Year: 2026

Venue: figshare

Classification: cycle

Abstract:

We present a partial machine-checked formalization of the Collatz conjecturein the Lean 4 proof assistant, comprising over twenty-one thousand lines ofproof across fifteen source files. The development introduces a three-layerframework that decomposes the conjecture into modular measure decay, renewal-cyclecontraction, and a bridging argument connecting residue-class analysis toindividual trajectories. At the first layer, we prove that the fraction of"bad" residue classes -- those admitting no finite contraction witness at agiven modular resolution -- decays geometrically to zero as the resolutionincreases. At the second layer, we formalize an explicit renewal-cycle mapthat tracks each odd i...

Lean file: `Collatz/Papers/Journal_10_6084_m9_figshare_31396683.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-p (2026-09-16)
