# arxiv-2101-09719-collatz-convergence-is-a-hydra-game

Citation: Alexander Rahn et al., "Collatz convergence is a Hydra game", arXiv:2101.09719 [2021].

Authors: Alexander Rahn, Eldar Sultanow, Idriss Aberkane

arXiv: [2101.09719](https://arxiv.org/abs/2101.09719)

Year: 2021

Classification: verification

Abstract:

The Collatz dynamic is known to generate a complex quiver of sequences over natural numbers which inflation propensity remains so unpredictable it could be used to generate reliable proof of work algorithms for the cryptocurrency industry. Here we establish an ad hoc equivalent of modular arithmetic for Collatz sequences to automatically demonstrate the convergence of infinite quivers of numbers, based on five arithmetic rules we prove apply on the entire Collatz dynamic and which we further simulate to gain insight on their graph geometry and computational properties. We then formally demonstrate these rules define an automaton that is playing a Hydra game on the graph of undecided numbers we also prove is embedded in 24N-7, proving that in ZFC the Collatz conjecture is true, before giving a promising direction to also prove it in Peano arithmetic.

Lean file: `Collatz/Papers/Arxiv2101_09719.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
