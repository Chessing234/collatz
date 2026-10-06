# Collatz

Formal exploration of the Collatz conjecture in Lean, with verified partial
results, computational experiments, and literature notes. **The conjecture
remains unproved.**

The main library uses Lean core. A separate [Mathlib extension](ProofAtlasAttack/README.md)
contains additional analytic results and verification instructions.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build Collatz
```

The Lean version is pinned in `lean-toolchain`. Run the integrity checks
(requires Bash and Python 3):

```sh
bash scripts/check_integrity.sh
```

[CI](.github/workflows/ci.yml) also checks generated certificates and the exact
interval and coefficient-descent developments. The Mathlib extension has its
own verification instructions.

## Research entry points

- [Research status](RESEARCH.md) — results, open questions, and limitations.
- [Proof index](INDEX.md) — guide to the Lean library.
- [First coefficient crossing through 1,024 steps](Research/FirstLight1024.md) —
  a conditional descent theorem for unbounded inputs, retained from the
  universal-descent development; it does not assert a crossing by 1,024 for
  every input.
- [Coefficient crossing and interval shape](Research/CoefficientDescent/README.md) —
  effective finite-exception transfer, a separately certified 256-step theorem,
  and the exact interval-shape consequences.
- [Exact first-descent intervals](Research/DescentIntervals/README.md) —
  complete classifier, refinement conservation, and the remaining coverage
  obligation.
- [Natural stopping density](Research/StoppingNaturalDensity.md),
  [Korec density bounds](Research/KorecCertified.md), and
  [inverse interval decisions](Research/InverseInterval.md).
- [Research notes](Research/) and [argument summaries](Devices/) — experiments
  and verification records.
- [Literature](Papers/index.md) — sources and references.

Conditional theorems keep their hypotheses explicit. Finite computations and
almost-everywhere results do not prove convergence for every positive input.
