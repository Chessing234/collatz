# Positive predecessor density does not imply universal convergence for arbitrary maps

2026-10-01. A Lean-checked comparison model. **This is not the Collatz map**,
and it does not refute any claimed theorem about the actual Collatz map.
No historical novelty is asserted for this elementary construction.

## The map

On natural numbers define F(n) to fix 0, 1, and 3, and otherwise send n to
floor(n/2). Positive inputs stay positive. Strong induction proves that every
positive input eventually reaches 1 or 3. Since 3 is fixed, universal
convergence to 1 is false.

Nevertheless every positive target has positive lower natural density of
predecessors. The checked endpoint gives the explicit bound

    N < 2 (max(a,2)+1) P_a(N),     for N ≥ max(a,2)+1,

where P_a(N) counts starts n < N that reach a at some time. The count has no
fixed iteration limit. Thus each target has lower density at least
1/[2(max(a,2)+1)]. The estimate is deliberately simple, not claimed optimal.

## Proof of the density estimate

For a ≥ 2, every start in [a*2^k,(a+1)*2^k) reaches a after exactly k steps:
write n = a*2^k+r with 0 ≤ r < 2^k and repeatedly halve. Before the final
step every value is at least 4, so neither fixed-point exception intervenes.
For a = 1, use the block for target 2 and one additional step.

For an arbitrary cutoff N ≥ b+1, where b=max(a,2), choose
k = floor(log_2(floor(N/(b+1)))). Then the whole block lies below N and
its length 2^k satisfies N < 2(b+1)2^k. A no-duplicates list inclusion
turns block length into a lower bound on the actual predecessor count.
These facts, including the count comparison, are all formalized in Lean.

## What the comparison establishes

All-target positive lower predecessor density is insufficient, by itself,
for universal convergence in arbitrary positive-integer dynamical systems.
In this example the problem is two terminal basins, not divergence.
An argument for Collatz that uses its density results must also use properties
that exclude this possibility in the actual map. The comparison does not prove
logical independence of any Collatz-specific statement, nor refute an argument
that uses additional arithmetic hypotheses.

## Verification

[Lean source](../Collatz/Strategy/DensityCountermodel.lean),
[nine-endpoint axiom audit](DensityCountermodelAxioms.txt), and
[independent enumeration](DensityCountermodelProbe.json).

```sh
lake build Collatz.Strategy.DensityCountermodel
lake env lean scripts/audit_density_countermodel.lean
python3 scripts/probe_density_countermodel.py
```

The probe follows complete model trajectories and counts visited targets for
every cutoff through 10,000 and every target through 32. It checks the same
strict inequality using enumeration rather than the dyadic-block formula.
Finite checks validate conventions; the universal theorem is the Lean proof.

The [density compatibility extension](DensityCompatibilityModel.md) proves that
this same map also has natural-density-one finite stopping time and a
logarithmic-density-one almost-bounded conclusion, while failure to reach 1
has an explicit positive lower density.
