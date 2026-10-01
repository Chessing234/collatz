# Natural density one of actual finite stopping time

2026-10-01. The main core-only Lean library now proves

    NaturalDensity.DensityOne Collatz.hasFiniteStoppingTime.

This reconstructs the classical Terras/Everett conclusion, not a historically
new mathematical result. The predicate asks for an actual accelerated iterate
below the starting value. It does not ask for convergence to 1. Natural density
one does not imply that every input belongs to the set.

Historical sources: [Terras's 1976 article](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers)
and the account of the earlier Terras/Everett result in
[Korec's paper, pp. 85–86](https://www.dml.cz/handle/10338.dmlcz/133225).
The argument here reuses this repository's weighted-residue estimate and
accumulator bound. It is not a transcription of Terras's original proof.

## What closes the gap

The previous `Density` module bounds heavy residue classes. Turning that into
a count of actual orbits needs control of the additive correction. If the first
coefficient crossing is at k≤H but the orbit does not drop, the existing bound
implies

    3 (2^k − 3^a) n ≤ a 3^a ≤ H 3^H.

The coefficient gap is a positive integer. Thus n>H3^H rules out failure.
Above that explicit cutoff, first crossings and first actual descents agree;
the whole finite-horizon survival predicate is periodic modulo 2^H. The sharper
256-step certificate additionally classifies small starts, but is not needed
for the mathematical argument about finite exceptions at arbitrary H.

The shifted survival-count interface and the new unshifted interface both
have checked cutoff-error bounds. For the unshifted count C_H(N) of actual
non-descent through H, let A_H be the existing heavy-residue count. Then

    C_H(N) ≤ H3^H + 1 + (floor(N/2^H)+1) A_H.

This inequality holds for every H and N. The geometric estimate already proved
in the repository is transferred to all-prefix survival as well.

## Explicit precision

A small kernel calculation gives 2·243^16≤256^16. Combining repeated blocks
with the existing fifth-power estimate yields

    s A_(80s) ≤ 2^(80s).

For requested precision q>0, take H=160q and

    N0 = 2q (H3^H + 1 + 2^H).

For every N≥N0, Lean proves q C_H(N)≤N. Every input outside this no-descent set
has finite stopping time. Counting the complement gives

    (q−1)N ≤ q · count{n<N : hasFiniteStoppingTime n}.

Together with the universal upper bound on counts, this is the library's
integer-precision formulation of natural density one. The cutoff is purposely
coarse, and no optimized quantitative stopping-time estimate is claimed.

## Validation and limits

The modules passed the pinned Lean compiler; the combined package has a
27-endpoint axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.
An independent integer-orbit probe checks 4,160 pairs of representatives above
the coarse threshold at horizons 0 through 64. The proof itself covers all
finite horizons and all cutoffs. No statistical sampling is used as proof.

The paper wrapper now exports `terrasDensityOne_proved`. Its older diagonal
bounded-horizon, rational-epsilon formulation is retained under
`diagonalDensityOne` as a separate unproved statement. No equivalence proof
between that historical formulation and the checked definition is claimed.

```sh
lake build Collatz.Papers.Terras1976
lake env lean scripts/audit_stopping_natural_density.lean
python3 scripts/probe_first_light_eventual.py
```

[Actual stopping density](../Collatz/Structure/StoppingNaturalDensity.lean),
[arbitrary-horizon cutoff](../Collatz/Strategy/FirstLightEventual.lean),
[geometric precision](../Collatz/Structure/DensityPrecision.lean),
[axiom audit](StoppingNaturalDensityAxioms.txt),
[probe results](FirstLightEventualProbe.json).
