# Korec statement repair

The previous wrapper proved an inequality with no orbit or set count. It has
been replaced by a counted natural-density statement for rational exponents.
The published source is [Korec, Theorem 1](https://www.dml.cz/handle/10338.dmlcz/133225).
For p/q above the threshold, encoded as 3^q<4^p with q>0, the recorded predicate
asks whether some accelerated iterate satisfies T^k(n)^q<n^p. The full theorem
is not proved here; the real-exponent formulation is not formalized.

The density definition uses integer precision: for every positive q,
eventually (q−1)N≤q·count(N). Lean checks the universal upper count bound,
set-inclusion monotonicity, and that the empty set does not have density one.
The orbit checks distinguish the strict bound at inputs 1 and 2.

The three new modules and existing wrapper were checked with the repository's
pinned Lean compiler. Seventeen supporting proof endpoints have a separate
axiom audit. The statement itself is a definition, never an assumed axiom.
A Python regression checks integer powers on [0,10000). Both 4/5 and the
out-of-range exponent 3/4 pass for starts above 1 by step 256. This sample
therefore cannot distinguish the asymptotic exponent threshold.

```sh
lake build Collatz.Papers.Journal_1994_Korec_a_density_estimate_for_the_3x
lake env lean scripts/audit_korec_statement.lean
python3 scripts/probe_korec_power_bounds.py
```

[Statement](../Collatz/Papers/Korec1994.lean),
[density definition](../Collatz/Structure/NaturalDensity.lean),
[axiom audit](KorecStatementAxioms.txt), [probe](KorecPowerProbe.json).

The subsequent [4/5 density proof](KorecFourFifths.md) now establishes a genuine
specialization and every larger positive rational exponent. The full recorded
range above log₄(3) remains unproved.
