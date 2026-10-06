# Why the power-hitting rule is not density-tight

The [controlled stopping-rule theorem](FirstDescentTransport.md) transports
natural density one through a selected time τ(n) when its large-time tails
are uniformly small in density. The first actual descent time has this
property. Times that achieve a strict sublinear power target at density one
do not.

For p<q, Lean proves that any successful hit at time k satisfies

    T^k(n)^q < n^p  ⇒  n^(q−p) < 2^(kq).

The argument is elementary and applies to the actual accelerated Collatz map.
Each step shrinks size by at most a factor two, so n≤2^k T^k(n). Raise this
inequality to q, combine it with the strict power target, and cancel n^p.
The proof also handles the natural-number boundary cases directly.

A convenient consequence is that, once n≥2^(Kq), no time k≤K reaches the
target. Thus every fixed time window eventually fails, even though Korec's
theorem establishes eventual success on a density-one set.

## Consequences for selected times

For any total rule τ(n), let Success(n) mean that its selected iterate meets
the p/q power target. If τ is density-tight, the new proof shows that Success
has density zero, expressed by an eventual upper count bound at every integer
precision. Outside the finite prefix n<2^(Kq), every success belongs to the
large-time tail τ(n)>K. The tightness estimate controls this tail, and the
finite prefix is absorbed by increasing the counting cutoff.

Conversely, if Success has density one, then for every fixed K the set
{n : τ(n)>K} has density one. In particular τ is not density-tight. This is
stronger than merely lacking a globally bounded horizon: the selected times
escape every fixed bound on almost all inputs.

The module defines a noncomputable `powerTime` that chooses a successful time
whenever one exists, and uses zero otherwise. Korec's proved rational-exponent
statement makes Success density one in its range. When p<q as well, the new
theorem proves that this actual power-hitting rule fails the tail condition.
The result does not depend on selecting the earliest successful time.

This identifies a missing hypothesis in a proposed bootstrap from the
first-descent transport theorem. It does **not** prove that the power-selected
map fails to preserve density one: the uniform tail condition is sufficient,
and has not been shown necessary for that preservation property. Another
transport argument could use additional structure or quantitative estimates.
Nor does the result challenge the power-density theorem itself.

The restriction p<q matters. Ordinary strict descent corresponds to p=q,
and its first time does satisfy the uniform tail condition. Strict sublinear
power descent demands a greater size reduction as n grows.

## Verification

The module builds, ten endpoints pass the standard axiom audit, and the full
main-library integrity check passes with the new results included. An
independent probe checks 153,000 halving bounds, 339,865 successful power hits,
and 4,500 forbidden-window cases. It also finds first power-hit times for
2≤n<10000 at exponents 1/2, 3/4, 4/5, and 23/29. Those finite samples do not
prove an asymptotic statement at the exponents below the recorded Korec
threshold. They do not evaluate Lean's arbitrary classical choice; the
size-time constraint applies to every successful choice.

```sh
lake build Collatz.Strategy.PowerStoppingTimeBarrier
lake env lean scripts/audit_power_stopping_time.lean
python3 scripts/probe_power_stopping_time.py
bash scripts/check_integrity.sh
```

[Lean proof](../Collatz/Strategy/PowerStoppingTimeBarrier.lean),
[axiom audit](PowerStoppingTimeAxioms.txt), [probe](PowerStoppingTimeProbe.json).
