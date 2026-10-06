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

## A bounded-list implementation

`intervalStates lo hi` enumerates only the proposed interval width and
filters out multiples of three. `advanceLayer` maps each retained entry
forward once and discards images outside the allowed set. Starting with
`intervalStates`, the recursive `layers` function repeats this operation.

Lean proves that membership in the kth layer is exactly the same predicate
as the original recursive inverse search. At the decision depth, the layer
contains exactly the positive periodic points whose cycles fit in the
interval. `layerCheck` supplies Boolean membership for this result. For
multiple queries, the completed layer can be computed once and reused.

Each round maps and filters an existing list, so the list never grows.
`layer_length_le` bounds every layer by hi−lo+1 entries. This avoids
re-exploring an inverse tree separately for every endpoint. The bound is on
list entries, not bytes or arithmetic bit costs; the complete number of
rounds can still be large.

Duplicates are deliberately retained. For example, the completed layer for
[1,4] is `[1,2,1]`, which represents two periodic values, not three. In the
[1,100] probe, the completed list has 48 entries but only values 1 and 2.
Its length must not be used as a count of periodic points. Set membership
stabilizes past the decision depth even when list order or multiplicity
changes.

`decision_layer_empty_iff` also provides a batch certificate: the completed
list is empty exactly when no positive cycle is confined to the interval.
This is stronger than excluding a cycle through one selected input, while
remaining explicitly limited to the finite interval.

## Proven early stopping

`sameMembersCheck` compares both membership directions between two lists,
ignoring order and duplicates. Lean proves that advancing a layer respects
this relation. Thus if one round leaves membership unchanged, every later
round has the same members.

`pruneStable` returns the next list when this fixed point is detected, or
continues until its fuel is exhausted. Its result records both the retained
states and the number of rounds actually evaluated. `pruneStable_correct`
proves equality of membership with the full-budget computation from any
initial list. Separate theorems bound the reported rounds by the fuel and
the result length by the initial length.

`earlyDecision` starts from the allowed interval and supplies the complete
interval-width budget. It therefore has the same exact positive-cycle
semantics as the complete layer, with both resource bounds expressed in
terms of the interval width. An arbitrary call to the lower-level runner
with less fuel should not be treated as a complete decision merely because
it returned a finite result.

The kernel-checked two-cycle example stops after one round:
`[1,2]` advances to `[2,1]`. Literal list equality would miss that fixed
membership set. The [1,100] probe evaluates 21 rounds instead of its full
budget of 100: 20 rounds change membership, and one more detects stability.

The membership comparison currently uses list containment checks. Fewer
rounds do not by themselves imply less wall-clock time: comparisons have a
cost, which can be quadratic in list length. No benchmarked speedup or
arithmetic bit-complexity bound is claimed here.

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

The original recursive Lean search remains as a specification and can repeat
work on shared subproblems. The list implementation computes all endpoints
together with a proved length bound. The extended Python probe compares
list layers to set-based graph pruning on 1,323 cases, checks the length
bound at every round, and records duplicates explicitly. All comparisons
passed. The early-stop extension also passed 19,656 comparisons from
arbitrary small lists, including duplicates, initially disallowed entries,
empty lists, and zero fuel. Its completed interval answers agree with the
independent forward-cycle detector on all 5,022 cases. None of these methods
makes arbitrary large intervals practical merely by having a finite
completeness theorem.

## Verification

All nine search endpoints, eight completeness endpoints, 15 list-layer
endpoints, and 12 early-stop endpoints are included in their dedicated axiom
audits. The principal
interfaces, including complete decision, eventual stability, the list length
bound, and the empty-layer certificate, are in the main-library integrity check.

```sh
lake build Collatz.Search.InverseInterval
lake env lean scripts/audit_inverse_interval.lean
lake build Collatz.Search.InverseIntervalComplete
lake env lean scripts/audit_inverse_interval_complete.lean
lake build Collatz.Search.InverseIntervalLayers
lake env lean scripts/audit_inverse_interval_layers.lean
lake build Collatz.Search.InverseIntervalEarlyStop
lake env lean scripts/audit_inverse_interval_early_stop.lean
python3 scripts/probe_inverse_interval.py
bash scripts/check_integrity.sh
```

[Lean search and proofs](../Collatz/Search/InverseInterval.lean),
[axiom audit](InverseIntervalAxioms.txt),
[completeness proof](../Collatz/Search/InverseIntervalComplete.lean),
[completeness audit](InverseIntervalCompleteAxioms.txt),
[list implementation](../Collatz/Search/InverseIntervalLayers.lean),
[list-layer audit](InverseIntervalLayersAxioms.txt),
[early-stop implementation](../Collatz/Search/InverseIntervalEarlyStop.lean),
[early-stop audit](InverseIntervalEarlyStopAxioms.txt),
[probe](InverseIntervalProbe.json),
[residue-spread bounds and their local limitation](CycleInverseSpread.md).
