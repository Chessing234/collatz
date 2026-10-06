# Why the order of density and exponent quantifiers matters

This continues the [halving comparison model](DensityCompatibilityModel.md),
which fixes 0, 1, and 3. It is not the Collatz map.

Write P(p,q,n) for the assertion that some model iterate m satisfies m^q<n^p.
For every fixed p>0 and every q, the new Lean proof establishes P(p,q,n) for
all n≥3^q+1. Indeed, every positive orbit reaches 1 or 3, so its minimum m
satisfies m≤3, and then m^q≤3^q<n≤n^p.

Thus every fixed positive rational-power target holds with natural density
one, even for exponents arbitrarily close to zero. This is stronger in its
range of exponents than the recorded Korec threshold for actual Collatz, but
it concerns a different map and gives no improvement to Korec's theorem.

For one fixed n>1, however, the proof establishes the equivalence

    reaches 1  ↔  for every q>0, P(1,q,n).

The forward direction is immediate. For the reverse direction take q=n.
If an attained positive integer m were at least 2, then m^n≥2^n>n, contrary
to the required power bound. Therefore that iterate must equal 1.

The model's basin of 3 has a positive lower density, so reaching 1 does not
have density one. Consequently the theorem proves both

    for every q>0: DensityOne {n : P(1,q,n)}
    not DensityOne {n : for every q>0, P(1,q,n)}.

A countable intersection of density-one sets need not retain density one.
The exceptional sets depend on the exponent. A proof attempting to deduce
convergence from a family of power estimates must control this dependence;
it cannot simply interchange these quantifiers.

The supporting density module derives complementary count bounds from the
integer-precision definition, proves that a positive lower fraction of
exceptions excludes density one, and proves that every density-one set
intersects a set with an eventually positive linear count bound.

## Verification

Both modules build with Lean core. Eleven theorem endpoints pass the standard
axiom audit. An independent integer probe checks eight reciprocal exponents
on [0,10000), and the q=n pointwise test for every 2≤n<10000. It again finds
4,095 positive starts below 10,000 that do not reach 1. These computations
support the implementation; the Lean proofs establish the unbounded claims.

```sh
lake build Collatz.Strategy.DensityPowerCountermodel
lake env lean scripts/audit_density_power.lean
python3 scripts/probe_density_power.py
```

[Model proof](../Collatz/Strategy/DensityPowerCountermodel.lean),
[density lemmas](../Collatz/Structure/DensitySeparation.lean),
[audit](DensityPowerAxioms.txt), [probe](DensityPowerProbe.json).
