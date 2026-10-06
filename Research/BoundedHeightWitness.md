# Explicit witnesses against bounded height schedules

The [size-comparison obstruction](ComparableHeightObstruction.md) excludes a
universal bounded nonincrease schedule. The new result gives a finite location
and a computable search for a failing input.

Suppose n+1≤h(n)≤C(n+1) for every n above a cutoff and above 1. For every finite
horizon B, the theorem provides an x satisfying

    cutoff < x < (cutoff+3)·3^(B(2C+1)+1),     1 < x,

such that every positive iterate through B strictly increases h:

    h(x) < h(T^k(x))     for all 1≤k≤B.

This x defeats the proposed bounded height schedule. It is not a counterexample
to Collatz convergence and may descend at a later time.

## Finite localization

Set q=cutoff+3, K=B(2C+1)+1, and n=q·2^K−1. The proof finds x=T^t(n) for some
0≤t≤B(2C+1). It uses the exact all-odd formula to bound x by q·3^K.

The central local theorem needs only the comparisons n_t+1≤h(n_t)≤C(n_t+1)
at the finitely many states n_t=T^t(n), for 0≤t≤B(2C+1). If every such state
had a nonincrease choice within B steps, concatenating 2C+1 choices would
contradict the size growth along the run. This gives a finite way to falsify
a schedule proposal without assuming bounds on all natural numbers.

The Boolean function `failureCheck` tests a single candidate x. The function
`runFailureCheck` searches all the specified orbit indices. Lean proves exact
semantics for both and proves that the local comparison hypotheses guarantee
a successful search. The search can use any supplied computable height.

## Verification

The module builds and all ten endpoints pass an axiom audit. Three examples
are reduced directly by Lean's kernel, including the residue-oscillating
height h(n)=(n+1)(1+n mod 7), horizon B=2, and failure input x=9,663,676,415.

An independent integer probe exhausts 63 runs across size, residue, and binary
digit heights and checks 1,764 states. Each run contains a failure; all found
failures satisfy the explicit location bound. The probe includes B=0, where
the positive-time condition is vacuous, to check the boundary case.

```sh
lake build Collatz.Strategy.BoundedHeightWitness
lake env lean scripts/audit_bounded_height_witness.lean
python3 scripts/probe_bounded_height_witness.py
```

[Lean source](../Collatz/Strategy/BoundedHeightWitness.lean),
[audit](BoundedHeightWitnessAxioms.txt), [probe](BoundedHeightWitnessProbe.json).
