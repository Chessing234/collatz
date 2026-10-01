# Density conclusions can coexist with a second basin

This is a logical stress test using the comparison map from
[DensityCountermodel](DensityCountermodel.md), **not the Collatz map**. It fixes
0, 1, and 3, and otherwise sends n to floor(n/2).

The new module proves that the following properties coexist:

- Finite stopping time has natural density one: every n≥4 drops immediately.
- Positive inputs that never reach 1 have positive lower density. For every
  N≥4, their count F(N) below N satisfies N≤8F(N).
- Every positive orbit attains a value at most 3. Consequently, for every
  rational-valued function tending to infinity, the orbit eventually goes
  below that function for a logarithmic-density-one set of inputs.
- The original comparison module proves positive lower predecessor density
  for every positive target, even with these two terminal basins.

The failure set contains all predecessors of 3. Composition of iterates proves
that none of those inputs can also reach the fixed point 1. The existing
predecessor-count bound then gives the explicit lower bound on F(N).

The small witness 6→3 shows why the sets differ. The start 6 descends, while 3
never drops below itself. Pulling back a never-dropping target therefore need
not produce more never-dropping starts. Almost-all descent cannot be read as
almost-all convergence to 1, and almost-bounded minima allow a bounded second
basin. These facts identify a gap in a proposed combination of density
arguments; they do not establish any counterexample for actual Collatz, nor
rule out arguments using additional properties of that map.

The Lean module builds and its eleven theorem endpoints use only standard
logical axioms. An independent test on [0,10000) finds 9,997 starts with finite
stopping time and 4,095 positive starts failing to reach 1. It checks the lower
failure-count bound at every cutoff from 4 through 10,000.

```sh
lake build Collatz.Strategy.DensityCompatibilityModel
lake env lean scripts/audit_density_compatibility.lean
python3 scripts/probe_density_compatibility.py
```

[Source](../Collatz/Strategy/DensityCompatibilityModel.lean),
[audit](DensityCompatibilityAxioms.txt), [probe](DensityCompatibilityProbe.json).
