# Rational band obstruction and integer return clock

The investigation of wider bands exposed a limit of the real affine
relaxation used to guide the ratio-five certificate. It is not sufficient
to strengthen an integer theorem by treating its orbit values and anchor
as unconstrained rational numbers. This note records a counterexample to
that transfer, not a counterexample to the integer Collatz conjecture.

## Exact denominator encoding

For an odd fixed denominator `d`, a rational state `n/d` has an even or
odd numerator. Its numerator update is

`denominatorStep(d,n) = n/2` if `n` is even, and `3n+d` otherwise.

An even numerator is halved exactly; the odd denominator remains fixed.
Reducing such a fraction cancels an odd common factor and preserves the
numerator parity. At denominator one, Lean proves both the step and the
whole orbit equal the original integer definitions, including zero.
The Lean file works with natural numerators and exact cross-multiplied
comparisons; it does not silently identify the offset map with `3n+1`.

At denominator five the numerator cycle is

`23→74→37→116→58→29→92→46→23`.

Lean proves its least positive period is eight and every future value lies
in `[23,116]`. Every odd scale `t` gives the encoding with denominator `5t`
and numerators multiplied by `t`; the normalized rational cycle is the
same. Even scales are deliberately excluded from the numerator parity
statement and rejected by a test control.

The underlying affine cycle method is standard. [Halbeisen and
Hungerbühler, *Optimal Bounds for the Length of Rational Collatz Cycles*](https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf)
define the odd-denominator rational parity rule and present the affine
parity-word fixed-point formula (Lemma 2, attributed there to Lagarias).
Their accelerated map includes an odd update followed immediately by a
halving. The ordinary eight-step word here corresponds to the five-step
accelerated word `11010`. No priority claim is made for this rational cycle
or the standard affine identity.

## Why integrality matters

The rational minimum is `23/5>1`. The maximum/minimum ratio is
`116/23≈5.04348`, so every state remains in the ratio-`51/10` band anchored
at that minimum. Yet every value is strictly less than `(81/16)*(23/5)`.
The exact gap between that threshold and the maximum is `7/80`.
Consequently, even the multiplicative part of the repository's integer
floor excursion theorem fails for this rational floor. The cycle does
exceed five times its minimum, by `1/5`, and therefore does not refute the
ratio-five excursion result.

Lean proves the generalized return equation for the branch word `OEOEEOEE`:

`32*x8 = 27*x0 + 23*d`.

Closure forces `5*x0=23*d`, and the full natural-number classification is
`d=5t`, `x0=23t`. In particular, denominator one has no closed encoding in
this word. The actual integer class `n=32q+11` instead satisfies

`C^8(n)=27q+10<n`.

The code gives its exact eight-step trace, return identity, and the converse
source-residue constraint. This integer class was already closed in
`Strategy/ExcursionMap.lean`; the new file records the fixed clock and its
relationship to the rational closure obstruction. It is not a newly
resolved residue class or an established frontier discovery.

The exploratory real-affine guide exhausted ratio five at depth twelve,
but retained feasible prefixes at depth 48 for several larger ratios.
Those surviving prefixes are evidence about a relaxation, not integer
orbits. In particular, the rational anchor `23/5` is not an allowed natural
anchor in the current band-clock theorem. No wider-band integer exit
clock is refuted or proved by this exploration. A subsequent search can
use the anchor's integrality and state congruences before declaring a
prefix viable.

## Verification

Run `python3 scripts/audit_rational_band_obstruction.py`. It builds the
module, checks all 24 named theorem axiom footprints, scans the source for
proof escapes, and requires Lean to reject four false transfers. Independent
Fraction tests check 10,000 rational states, 4,100 odd scales including large
integers, 56 exact affine branch words (16 parity-valid), 10,004 integer
traces, and denominator-one/even-scale controls. These finite tests
corroborate the universal Lean proofs; no computation is imported as an
axiom. The library export and CI include the new audit.

The conjecture and the requested frontier-novel proportion remain open.
