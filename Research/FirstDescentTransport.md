# Density transport through the first actual descent

The [fixed-window transport theorem](StepDensityTransport.md) now extends to
input-dependent times under an explicit uniform tail condition. The first
actual descent time satisfies that condition. Therefore its induced map
preserves natural density one under preimage.

## A controlled stopping rule

For a total time function τ(n), the new predicate `DensityTight τ` means

    for every r>0, there are K and N₀ such that, for every N≥N₀,
    r · count{n<N : τ(n)>K} ≤ N.

Thus arbitrarily large selected times occupy an arbitrarily small eventual
proportion of the inputs. A globally bounded time function satisfies this
condition, but a global bound is not required. Merely assigning a finite
integer τ(n) to each input does not establish the uniform condition.

For every natural-density-one predicate P, Lean proves

    DensityOne {n : P(T^τ(n)(n))}

when τ is density-tight. The proof splits failures into two sets: the tail
τ(n)>K and the failures of P at some state in the fixed window through K.
The latter is small by fixed-window density transport. Choosing both estimates
at precision 2r bounds their union at precision r.

## The first-descent map

`firstTime n` selects the least actual descent time when one exists and is
zero otherwise. This is a noncomputable totalization, not an algorithm claimed
to decide whether every orbit descends. The proof verifies its least-time
meaning on descending inputs. Define

    D(n) = T^firstTime(n)(n).

If firstTime(n)>H, the start has no descent through H. The previously proved
uniform stopping estimate bounds the count of that finite-horizon survival
set. In particular, at precision r the proof takes H=160r and cutoff

    N₀ = 2r · ((160r)·3^(160r) + 1 + 2^(160r)).

It follows that `firstTime` is density-tight and that D preserves every
density-one predicate under preimage. On non-descending inputs D leaves the
start unchanged; on descending inputs it strictly decreases. This is a
justified use of an input-dependent stopping time because the needed uniform
tail estimate is supplied explicitly.

## What the first drop cannot accomplish

For every n, the same module proves n≤2D(n). A single accelerated step never
reduces its input by more than a factor two. Immediately before a first
descent, the orbit is still at least n, so its first lower endpoint is at
least n/2. The default case D(n)=n satisfies the bound as well.

As a consequence, for every n≥32,

    n^4 ≤ D(n)^5.

Thus the first descent alone cannot satisfy the strict 4/5 power target at
these starts. The proved power-density theorem finds a later iterate; it does
not identify that iterate with the first descent. This prevents confusing
the new density-transport result with an immediate stronger power contraction.
Neither result proves universal convergence.

## Checks

Both modules build, all sixteen endpoints pass the standard axiom audit, and
the full main-library integrity check passes with the new theorems included.
An independent probe checks first-descent semantics and size bounds at all
inputs below 10,000 and checks 22,545 selected-time failure-count covers.
The largest observed first-descent time is 81. At horizon 64 the sample has
12 starts with larger first times; at horizon 128 it has none. The finite
survival count also includes 0 and 1, whose selected times are zero by the
totalization convention. No global classification of non-descending starts
is inferred from these sample counts.

```sh
lake build Collatz.Strategy.FirstDescentDensityTransport
lake env lean scripts/audit_first_descent_transport.lean
python3 scripts/probe_first_descent_transport.py
bash scripts/check_integrity.sh
```

[Stopping-rule framework](../Collatz/Structure/StoppingRuleDensity.lean),
[first-descent proofs](../Collatz/Strategy/FirstDescentDensityTransport.lean),
[audit](FirstDescentTransportAxioms.txt), [probe](FirstDescentTransportProbe.json).
