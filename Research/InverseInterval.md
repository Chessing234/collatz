# Certified inverse search within a proposed cycle interval

The forced-doubling argument eventually encounters two admissible inverse
branches. The new executable search follows both, while retaining only values
inside a specified interval [lo,hi] and excluding multiples of three.

Lean proves the exact meaning of `survives lo hi k v`:

    true ↔ there is a reverse path of k transitions from v,
           with every value in [lo,hi] and not divisible by three.

A positive cycle confined to the interval survives every search depth from
every point of that cycle. Therefore a false result is a finite certificate
excluding such a cycle through the tested input. It does not rule out a
cycle using larger values, a transient path into another cycle, or an
unbounded orbit.

There is now also a proved complete decision depth: at k = hi−lo+1,
survival is equivalent to membership in a positive cycle confined to the
interval. Shorter successful searches retain only their finite-path meaning.

## Both inverse branches are covered

The complete predecessor theorem is

    T(p)=v ↔ p=2v or (v ≡ 2 mod 3 and p=(2v−1)/3).

The even branch is always available. The odd branch is tested only when it
is integral; its source is then odd. At every recursive call, the same
interval and modulo-three filters apply. The search neither chooses a
preferred branch nor assumes that a locally admissible predecessor belongs
to a cycle.

`survives_iff` proves equivalence with an independently stated inductive path
predicate. `path_truncate` and `survives_truncate` show that surviving sets
can only decrease as the requested depth grows. `cycle_survives` follows
the actual predecessors around a hypothetical cycle to prove that pruning
cannot discard it. `rejection_excludes_cycle` is the resulting soundness
interface.

## Why short survival is inconclusive

The kernel checks this concrete example:

    survives 7 56 4 7 = true,
    survives 7 56 5 7 = false.

The surviving reverse path is

    7 ← 14 ← 28 ← 56 ← 37.

The odd alternative at 56 passes the elementary filters, as predicted by
the earlier boundary analysis. But 37 has only its doubling predecessor 74,
which is outside the interval. Other branches have already been pruned.
The added search therefore resolves an obstruction that the single-step
filters alone leave open, for this particular finite interval.

The trivial cycle provides a positive control: Lean proves that 1 survives
every depth in [1,2]. No nontrivial positive cycle is asserted or discovered.
The theorem for rejection requires positivity because the modulo-three
filter deliberately excludes zero's fixed point.

## Completeness at an explicit depth

`path_as_forward` reads a reverse path as a forward orbit from its oldest
predecessor p. A path with k transitions supplies k+1 orbit values. At
k = hi−lo+1 there are more positions than integer values in the interval,
so two positions i<j repeat. Determinism makes every later point periodic,
including the endpoint v where the reverse search started.

The proof preserves the interval condition beyond the finite path:
every future endpoint value equals a value on the repeated prefix, and all
those values were checked. Thus the cycle obtained is through v itself and
stays in the proposed interval. It is not merely an unrelated cycle found
among predecessors.

The main interface is `survives_decision_positive_iff`:

    survives lo hi (hi−lo+1) v = true
      ↔ v > 0 and v lies on a cycle entirely inside [lo,hi].

`survives_stable` proves that increasing the depth beyond this point cannot
change the result. `all_depths_iff_decision` equates survival at every depth
with this single finite check. The bound counts all integers in the interval,
so it is conservative: the modulo-three filter may eliminate states sooner.
Empty intervals are handled by the same natural-number formulas.

This decides periodic membership within a finite bound, not convergence or
divergence in general. For example, 4 reaches the trivial cycle but is not
itself periodic, so its full-depth inverse search in [1,100] rejects it.
The argument is an elementary finite-state consequence of determinism, not
a claimed new historical Collatz result.

## Independent graph tests

The Python probe compares the recursive search with a separate finite-graph
calculation. It starts with all allowed values, repeatedly takes their
forward images, and intersects with the original allowed set. After k
rounds, membership must agree with existence of a k-step reverse path.

All 17,199 comparisons passed across intervals with lo from 0 through 8,
hi from 0 through 20, and depths through 6. This includes empty intervals,
zero, and off-by-one endpoint cases. The graph on [1,100] stabilized after
20 pruning rounds at exactly {1,2}; that measured result agrees with the
proved stability of the Boolean search after the decision depth.

The extended probe compares full-depth answers with direct forward cycle
detection on 5,022 interval/input combinations, and checks agreement three
depths later. All comparisons passed. Its 116 accepted cases are periodic
points in the tested intervals; rejection of transient point 4 is checked
separately.

The probe also tested 33 odd candidate minima from 5 through 101 that are
not divisible by three. Using each candidate's residue-table spread factor
to set the proposed maximum, it eventually rejected every candidate within
that interval. The JSON artifact records the bounds and first rejection
depths. These observations do not improve the already verified convergence
range; they validate the branching mechanism on finite examples.

The Lean search is a simple recursive reference implementation and can
repeat work on shared subproblems. The independent Python probe memoizes
those subproblems and also checks the graph formulation. The decision-depth
proof is general, but no runtime-efficiency claim is made: the finite bound
and recursive branching may still be impractical for large intervals.

## Verification

All nine search theorem endpoints and all eight completeness endpoints are
included in their dedicated axiom audits. The principal interfaces, including
complete decision and eventual stability, are in the main-library integrity check.

```sh
lake build Collatz.Search.InverseInterval
lake env lean scripts/audit_inverse_interval.lean
lake build Collatz.Search.InverseIntervalComplete
lake env lean scripts/audit_inverse_interval_complete.lean
python3 scripts/probe_inverse_interval.py
bash scripts/check_integrity.sh
```

[Lean search and proofs](../Collatz/Search/InverseInterval.lean),
[axiom audit](InverseIntervalAxioms.txt),
[completeness proof](../Collatz/Search/InverseIntervalComplete.lean),
[completeness audit](InverseIntervalCompleteAxioms.txt),
[probe](InverseIntervalProbe.json),
[residue-spread bounds and their local limitation](CycleInverseSpread.md).
