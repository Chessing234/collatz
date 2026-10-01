# First-crossing descent certificates

2026-10-01. This extends the existing `FirstLightDescent` certificate design.
It is a bounded-first-crossing result for unbounded starting values, not a
universal bound on stopping time and not a proof of Collatz. Historical novelty
is not claimed; coefficient stopping is classical Terras territory.

## Exact scope

Let T be the accelerated Collatz map and a(n,k) the number of odd steps in
its first k steps. A first coefficient crossing is an index k such that

    3^a(n,k) < 2^k,

while every earlier index has the reverse weak inequality. The new endpoint is

    n > 1, k ≤ 256, FirstLight(n,k)  ⇒  T^k(n) < n.

There is no upper bound on n. There is also no theorem here that every n has
a first crossing, much less one by step 256. Long all-odd prefixes prevent
interpreting this as a universal 256-step descent theorem.

## A reusable certificate theorem

The preceding accumulator argument bounds any failure to descend at the
first crossing by

    3 (2^k - 3^a) n ≤ a 3^a.

`descent_of_certificates` accepts two finite inputs for arbitrary horizon H
and threshold N:

1. For all k ≤ H and a ≤ k with 3^a < 2^k,
   a 3^a < 3 (2^k - 3^a) N.
2. Every 1 < n < N has a first crossing by H at which it descends.

If n ≥ N, the first certificate contradicts a failure bound. If n < N,
uniqueness of the first crossing identifies it with the finite certificate's
witness. This proof is reusable; larger certificates need not duplicate it.

## Data and validation

At H=256 the sufficient threshold is N=6701. The limiting pair in the exact
integer probe is (k,a)=(233,147). All 6,699 exceptional starts pass; their
maximum first-crossing index is 81, attained at n=703.

A separate H=512 probe passes with N=99730 and limiting pair (485,306).
It checks 99,728 starts; the maximum first crossing is 135 at n=35655.
**The 512 horizon is experimental here, not an exported Lean theorem.**

The gap and small-start certificates for H=256 use kernel `decide`, not native
execution. The small-start certificate uses a stateful scanner carrying the
current value and odd count; it evaluates each prefix once. Lean proves its
soundness, completeness, and monotonicity in the horizon. Boundary checks cover
horizon zero, the first crossing of 3 at index 4, and the nondescending orbit of 1.
The final certificate build completed in 29 seconds in this local run; this is
a single observed build time, not a controlled performance benchmark. The independent Python probe verifies the complete gap table and
follows the actual integer trajectories. The two certificate components and
the generic and specialized theorems, and the scanner checks have a separate
14-endpoint axiom audit.

```sh
lake build Collatz.Strategy.FirstLightCertificates
lake env lean scripts/audit_first_light_certificates.lean
python3 scripts/probe_first_light_certificates.py --horizon 256
python3 scripts/probe_first_light_certificates.py --horizon 512
```

[Lean source](../Collatz/Strategy/FirstLightCertificates.lean),
[256 probe](FirstLight256Probe.json), [512 probe](FirstLight512Probe.json),
and [axiom audit](FirstLightCertificatesAxioms.txt).
