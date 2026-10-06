# Exact counts inside a certified stopping horizon

2026-10-01. These modules connect the first-crossing certificate to actual
finite stopping times and to finite counting. They do not prove universal
descent, and the counting principles are standard rather than claims of
historical novelty.

## The conditional bridge

`ExactThrough H` means: every first coefficient crossing at index k≤H causes
an actual drop for every starting integer n>1. Under this assumption:

- First actual descent at k≤H is equivalent to first coefficient crossing at k.
- No actual descent through H is equivalent to all coefficient prefixes being
  heavy: 2^j ≤ 3^a(n,j) for j≤H.
- Starts greater than 1 in the same residue modulo 2^H have the same first
  descent index within the horizon, or both have no descent within it.

The existing 256-step certificate discharges the assumption at H=256.
There is no assertion that every n crosses by H. Odd-count periodicity is
already in the repository; the added interface transfers the certified
first-crossing result to the first actual descent and the entire window.

## Exact counting and cutoff errors

For any periodic Boolean predicate P of period M, write C(N) for its count
on [0,N), and A=C(M). The generic module proves

    C(N) = floor(N/M) A + C(N mod M).

It also proves, for M>0,

    M C(N) ≤ N A + M²,    N A ≤ M C(N) + M².

The integer precision theorem gives both normalized error inequalities with
error at most 1/q once N≥Mq (when q,N>0). Thus arbitrary-cutoff counts approach
the exact period proportion A/M, with an explicit cutoff. The formal statement
uses integer cross multiplication; it does not import real-analysis limits.

For Collatz we count the predicate on shifted starts n+2. This counts actual
starts in [2,N+2), so 0 and 1 cannot silently break the equivalence with descent.
The Boolean heavy-prefix predicate is periodic for every H. Its identification
with actual no-descent requires `ExactThrough H`.

## Prior work and tests

`SieveDensity.lean` already reports the same small-horizon survivor counts.
Our Python check independently compares a binary-word dynamic program,
exhaustive orbit representatives r+2·2^H and r+3·2^H, and the arbitrary-cutoff
formula for H=0,...,16. It reproduces 2,114 classes at H=16. This number is not
new. The Python dynamic program's equivalence with the Lean predicate is not
yet formalized; the script is regression evidence, while the Lean counting
identities are proved for all cutoffs.

All four modules build. A separate audit checks 37 theorem endpoints, using
only Lean's standard logical axioms. Repository-wide integrity is still a
separate check; a resource-heavy historical certificate build was interrupted.

```sh
lake build Collatz.Strategy.FirstLightCounting
lake env lean scripts/audit_first_light_counting.lean
python3 scripts/probe_first_light_periodicity.py
```

[Consequences](../Collatz/Strategy/FirstLightConsequences.lean),
[periodicity](../Collatz/Strategy/FirstLightPeriodicity.lean),
[generic counts](../Collatz/Structure/PeriodicCounting.lean),
[Collatz interface](../Collatz/Strategy/FirstLightCounting.lean),
[axiom audit](FirstLightCountingAxioms.txt),
[independent probe](FirstLightPeriodicityProbe.json).
