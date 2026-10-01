# Collatz

A research lab for AI-assisted exploration of the Collatz conjecture, with
formal proofs in Lean, computational experiments, and a literature archive.
The aim is to turn useful ideas into precise statements, check their proofs,
and record exactly where each approach stops.

**This repository does not contain a proof of the Collatz conjecture.**
It contains partial results, conditional reductions, and documented obstructions
to proposed proof strategies.

## Start here

- [Research frontier](RESEARCH.md): proved results, open hypotheses, and failed approaches.
- [Concept index](INDEX.md): a map of the main Lean development.
- [Mathlib-based extension](ProofAtlasAttack/README.md): predecessor-density and Syracuse-distribution results, attribution, and verification reports.
- [Research notes](Devices/): explanations of individual arguments and their limits.
- [Literature index](Papers/index.md): tracked sources.

## Two Lean developments

| Development | Scope | Dependencies and verification |
| --- | --- | --- |
| [`Collatz/`](Collatz/) | Arithmetic, reachability, finite verification, cycle bounds, and reductions of the conjecture. | Uses Lean core without Mathlib. The integrity script builds the library, scans for proof escapes, and audits selected theorem axiom footprints. |
| [`ProofAtlasAttack/`](ProofAtlasAttack/) | Analytic predecessor-density and Syracuse-distribution arguments. | Uses Mathlib and imported work by Tao and Mazur / ProofAtlas. Has separate build instructions and endpoint audits. |

The main development's integrity checks reject `sorry`, added axioms, and
`native_decide`. Its audited footprints allow only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. See the extension's README
for its own verification scope and upstream attribution.

Computational experiments outside Lean are identified separately from
kernel-checked results. A conditional theorem proves an implication; it does
not establish its hypothesis.

## Selected results

### Main development

- **Finite convergence:** every positive `n < 3,998,720` reaches `1`.
  See [the verified range](Collatz/Search/VerifiedRung14187.lean).
- **Cycle-length bound:** an accelerated cycle through a positive point that
  does not reach `1` has length at least `14,187`.
  See [the theorem](Collatz/Strategy/Frontier14187.lean).
  Here the accelerated map is `T(n) = n/2` for even `n` and `(3n+1)/2` for odd `n`.
- **Descent reduction:** Collatz is equivalent to `1` being the only positive
  integer whose accelerated orbit never falls below its starting value.
  See [NeverDrops](Collatz/Strategy/NeverDrops.lean).
- **Uniform inverse-tree coverage:** for every positive target `a` not divisible
  by `3`, every class modulo `27` contains an odd `n < 19419*a` reaching `a`
  in at most `22` accelerated steps.
  See [the statement and limits](Devices/QuantitativeBackwardCover.md).

The library also develops parity-word identities, residue sieves, inverse-tree
counting bounds, and obstructions to local descent arguments. The
[research frontier](RESEARCH.md) records the details and remaining gaps.
The finite convergence and cycle bounds do not settle all positive integers
or exclude all nontrivial cycles.

### Mathlib-based extension

- **Predecessor density:** every positive target not divisible by `3` has a
  predecessor set of positive lower natural density. The
  [residue-class extension](Devices/ResidueDensity.md) establishes positive
  lower density in every fixed class modulo `2^p * 3^q`.
- **Uniform Syracuse atom bound:** for the actual Syracuse probability law,
  there is an absolute `c > 0` such that `μ_n(r) ≥ c / 3^n` for every `n ≥ 1`
  and every unit residue `r` modulo `3^n`.
  See [the theorem, proof, and attribution](Devices/SyracuseUniformFloor.md).
- **Inverse-boundary analysis:** a hypothetical injective positive odd orbit
  gives a rational remainder with a positive real limit and a zero 2-adic
  limit. These limits are compatible, so they do not yield a contradiction.
  See [the boundary check](Devices/InverseBoundary.md).

These results do not exclude divergent orbits or unknown cycles. Verification
reports and historical audit counts are maintained in the
[extension README](ProofAtlasAttack/README.md); local verification does not
establish historical priority or independent mathematical review.

## Current research additions

- [Bounded-descent obstruction](Research/ResidueMonotoneObstruction.md):
  residue-wise nondecreasing heights cannot guarantee a drop within a fixed
  number of steps, even beyond an arbitrary starting-value cutoff.
- [First-crossing certificates](Research/FirstLightCertificates.md) and
  [exact counting](Research/FirstLightCounting.md): the certified 256-step
  horizon identifies first coefficient crossings with first actual descents.
  The horizon is a hypothesis; it is not a universal stopping-time bound.
- [Density statement audit](Research/TaoStatementRepair.md): meaningful
  logarithmic-density definitions replace a vacuous Tao placeholder.
  The full published theorem is recorded, not proved in this core package.

## Build and check

With Lean and Lake available through `elan`, run from the repository root.
The required Lean version is pinned in [`lean-toolchain`](lean-toolchain).
The integrity script also requires Python 3 and Bash.

```sh
lake build Collatz
```

For the full main-library integrity check, which includes the build:

```sh
bash scripts/check_integrity.sh
```

[CI](.github/workflows/ci.yml) runs the main build and integrity check on pushes
and pull requests. The Mathlib-based extension is checked separately; follow
its [build and verification instructions](ProofAtlasAttack/README.md#extension).

## Repository layout

| Path | Contents |
| --- | --- |
| [`Collatz/Core/`](Collatz/Core/) | Basic arithmetic and reachability. |
| [`Collatz/Search/`](Collatz/Search/) | Kernel-checked finite verification and stopping times. |
| [`Collatz/Structure/`](Collatz/Structure/) | Cycles, divergence, congruences, and residue sieves. |
| [`Collatz/Strategy/`](Collatz/Strategy/) | Proof strategies, reductions, and obstructions. |
| [`Collatz/Chains/`](Collatz/Chains/) | Decompositions of the conjecture into hypotheses. |
| [`ProofAtlasAttack/`](ProofAtlasAttack/) | Separate Mathlib-based extension and verification evidence. |
| [`Devices/`](Devices/) and [`Research/`](Research/) | Argument summaries, investigations, and research artifacts. |
| [`Blueprint/`](Blueprint/) | Expository notes on the development. |
| [`Papers/`](Papers/) | Literature records and source tracking. |
| [`scripts/`](scripts/) | Integrity checks, certificate generators, and computational probes. |

## Research workflow

1. Find a source or formulate a candidate lemma.
2. State it precisely in Lean and record its assumptions.
3. Prove it, leave it explicitly open, or document a counterexample.
4. Link the result to its source and explain its scope.
5. Run the relevant build and verification checks before submitting the change.
