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

- [Anchored barriers and finite cycle extraction](Research/BarrierKernel.md) —
  exact window splitting, the greatest invariant barrier kernel, an executable
  interval checker, exact one- and two-step capacities, and smaller verified
  budgets for cycle extraction. A sharp eight-step excursion theorem forces
  a hypothetical orbit floor to exceed five times its starting value.

- [First passage through 2,592 steps](Research/PassageAtlas/README.md) —
  a stronger conditional descent theorem, an exact residual condition
  equivalent to Collatz, and 32,768 new depth-fifteen class certificates.

- [Stopping atlas and first crossing through 1,538 steps](Research/StoppingAtlas/README.md) —
  15,360 infinite-class certificates, finite counting conservation, a tighter
  discrepancy bound, and explicit remaining universal-descent obligations.

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
