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

## Documentation

- [Research status](RESEARCH.md) — results, open questions, and limitations.
- [Proof index](INDEX.md) — guide to the Lean library.
- [Research notes](Research/) — arguments, experiments, and verification records.
- [Literature](Papers/index.md) — sources and references.
