# Density preservation fails at the orbit minimum

The actual Collatz orbit-minimum map does not preserve natural density one
under preimage. This is now a Lean theorem, without assuming any unproved
case of convergence or divergence.

Let P(n) mean that some accelerated iterate falls strictly below n. The
formalized Terras theorem proves that P has density one. Let M(n) be the
minimum of the entire accelerated orbit, as constructed by repeated first
descent. A minimum never descends further, so

    ∀ n, ¬P(M(n)).

The preimage of P under M is therefore empty. This is a direct obstruction
to extending the proved density-preservation property of each fixed number
of first-descent rounds to their pointwise stabilized endpoint.

## The image is exactly the exceptional set

Every minimum is non-descending. Conversely, a non-descending start m is
already its own orbit minimum. Lean proves the exact equality in predicate
form:

    (∃ n, M(n) = m) ↔ ¬P(m).

Thus the range of M has natural density zero. The formal count statement
says that for every positive integer r, eventually

    r · #{m < N : ∃ n, M(n) = m} ≤ N.

A map can send every input into a density-zero image even when all its
finite approximations preserve density one under preimage. Neither image
sparsity nor failure of transport establishes whether the positive image
contains any value other than 1. That remains the convergence question.

## Terminal times escape every fixed horizon

The time obstruction is more general than choosing this particular minimum.
Suppose a rule t(n) lands at a non-descending orbit point on a density-one
set of inputs. For every fixed K, almost every start has P at each of its
orbit positions 0 through K, by the fixed-window transport theorem. Such a
start cannot land at a non-descending point at any of these times. Hence

    DensityOne {n : K < t(n)}

for every fixed K. In particular t is not density-tight: there cannot be
fixed horizons whose tails become arbitrarily sparse in natural density.
This is `terminal_time_dense_tails` and `terminal_time_not_tight`.

Choosing an attained minimum time gives a total example satisfying these
conclusions. The selection is classical and is not claimed to be the first
attainment time or a computable algorithm.

The same phenomenon holds when counting first-descent rounds instead of
accelerated steps. The earlier stabilization proof supplies a terminal round
R(n) ≤ n. Nevertheless, for every fixed K, the set {n : K < R(n)} has density
one. The input-dependent bound R(n) ≤ n is fully compatible with failure of
density tightness.

## Finite observations and their limits

An independent Python probe follows all positive starts through 100,000 to
1, using a finite cap that would fail on an unresolved trajectory. It records
first attainment times and the number of strict record minima. These are
finite computable observations, not evaluations of the classical Lean
choices. First attainment gives a lower bound for any chosen time reaching
the same minimum.

| Positive starts tested | First minimum time > 32 | Terminal round > 16 |
| --- | ---: | ---: |
| 1–1,000 | 461 | 1 |
| 1–10,000 | 7,472 | 4,861 |
| 1–100,000 | 91,934 | 94,057 |

Every observed minimum is 1; its explicit cycle 1 → 2 → 1 confirms that it
never drops. No tested start needs more than 32 descent rounds. These finite
facts neither prove convergence for all starts nor contradict density-one
tails at every fixed horizon. No monotonicity or practical rate of approach
to the asymptotic density is asserted.

## Verification

All 15 theorem endpoints are included in the dedicated axiom audit. They
use only `propext`, `Classical.choice`, and `Quot.sound`. Principal endpoints
are also included in the main-library integrity check. The result is a
structural consequence of the verified descent and density theorems; no
historical novelty is claimed.

```sh
lake build Collatz.Strategy.MinimumTransportBarrier
lake env lean scripts/audit_minimum_transport.lean
python3 scripts/probe_minimum_transport.py
bash scripts/check_integrity.sh
```

[Lean proof](../Collatz/Strategy/MinimumTransportBarrier.lean),
[audit](MinimumTransportAxioms.txt), [probe](MinimumTransportProbe.json),
[repeated-descent construction](DescentRounds.md).
