# Attacking universal descent through the accumulated +1 correction

2026-09-28. Status: checked necessary condition and conditional descent
criterion; universal descent is not proved. No historical novelty is claimed.

## The attempted bridge

For the accelerated Collatz map T, let a be the number of odd inputs among
m,T(m),...,T^(k−1)(m). Suppose m>1 is odd, its orbit never falls below m,
and those first k orbit values are distinct. The existing SortStair theorem
bounds the orbit product by the product over the smallest possible distinct
odd values m,m+2,...,m+2a−2.

I tried to make the additive correction too small to sustain a never-dropping
orbit. The resulting exact inequality is

    2^(6k) (m−1) ≤ 3^(6a) (m+2a−1).

Equivalently, in real logarithms (this display is a mathematical interpretation,
not an additional Lean theorem),

    k log 2 − a log 3 ≤ (1/6) log(1 + 2a/(m−1)).

The right side grows only logarithmically in a for fixed m. The exact integer
inequality is Lean theorem `SixthPowerDrift.never_drop_bound`, with m=t+1.
Its injectivity and never-drop hypotheses are explicit.

## Derivation checked in Lean

For every integer x≥1,

    (3x+1)^6 (x−1) ≤ (3x)^6 (x+1).

`single_factor` proves this by polynomial arithmetic after x=t+1. Multiplying
at x=m,m+2,...,m+2a−2 telescopes the factors x−1 and x+1. Written without
division, `staircase_envelope` proves

    stairPlus(m,a)^6 (m−1)
      ≤ (3^a stair(m,a))^6 (m+2a−1).

Combining with the already-proved staircase bound and cancelling its positive
product gives the stated orbit inequality. This is an explicit consequence
of the existing stronger staircase estimate, not a strengthening of it.

## What still fails

The proposed contradiction needs a prefix satisfying the opposite strict
inequality. `descent_of_gap` proves that such a prefix, with the stated
injectivity, implies an actual later descent. It does not prove any particular
bound on the descent time.

`envelope_allows_heavy` proves an exact limitation: whenever 2^k≤3^a, the
new inequality is automatically satisfied for every m. Thus the estimate
cannot exclude prefixes with too many odd steps. A divergent orbit remains
compatible with this direction of inequality. This says nothing about which
infinite parity sequences are realizable by a positive integer; proving that
those integer orbits must eventually leave this region is precisely the
unresolved task. The theorem is not an impossibility result for all approaches.

Repeating prefixes and nontrivial cycles also require their own argument;
injectivity cannot be silently assumed for every hypothetical counterexample.

## Provenance and verification

New source: `Collatz/Strategy/SixthPowerDrift.lean`.
Audit: `scripts/audit_sixth_power_drift.lean`.
Axiom report: `Research/SixthPowerDriftAxioms.txt`.

The targeted build passed (64 jobs, with existing dependency warnings).
The six-endpoint axiom audit passed; dependencies are standard Lean axioms only.
No Mathlib, proof placeholders, added axioms, or external computation oracle
were used. The full repository integrity build was not rerun.

Prior local inputs are `SortStair.neverDrops_staircase` and the staircase
products in `StairBound`. For related classical background, I inspected
Halbeisen and Hungerbuehler, *Optimal bounds for the length of rational Collatz
cycles* (1997), especially the affine-word and cycle framework in Sections 1–3:
https://www.math.ch/norbert.hungerbuehler/publications/Optimal_bounds_for_the_length_of_rational_Collatz_cycles.pdf
This limited literature check does not establish priority for the displayed
sixth-power estimate. The derivation is elementary, and no novelty claim is made.
