# Korec's recorded rational-exponent theorem is proved

The Lean development now proves the complete rational-exponent proposition
recorded in `Korec1994.lean`:

    q > 0 and 3^q < 4^p
      imply DensityOne {n : some accelerated iterate m satisfies m^q < n^p}.

The endpoint is `Collatz.Papers.Korec1994.rationalExponentStatement_proved`.
The bibliographic wrapper now exports `mainStatement_proved` for the same
proposition. This formalizes the positive rational-exponent cases of
[Korec's Theorem 1](https://www.dml.cz/handle/10338.dmlcz/133225). It is a
reconstruction of a classical result, not a claim of historical novelty.

For q>0, the integer hypothesis is exactly the strict threshold
p/q>log₄(3). The interface uses integer powers throughout. It does not formalize
real-valued exponentiation or the theorem for arbitrary real exponents.
It also does not prove universal convergence: each exponent may have an
exceptional set of density zero.

## A finite certificate, without a density assumption

For exponents p and q, a certificate consists of a positive block length K,
a parity threshold h≤K, and ordered nonnegative weights B≤A with A+B>0. Its
substantive fields are the two strict integer inequalities

    (A+B)^K < 2^K · A^h B^(K−h),
    3^(q h) < 2^(p K).

These fields do not assume convergence or density. The first controls the
high-odd-count residue tail. The second leaves room for the affine correction
when bounding an actual orbit by a power of its starting value.

The uniform proof works for any such certificate. It derives arbitrary
integer precision for the exceptional residue count, proves the actual orbit
bound on multiplicative scale intervals, chooses a block-aligned period for
each counting cutoff, and controls both a discarded prefix and the final
incomplete period. This generalizes the previously checked
[4/5 specialization](KorecFourFifths.md).

## Constructing a certificate for every admissible exponent

The new balanced-moment lemma proves, for every integer r≥2,

    r^(2r) < (r+1)^(r+1) (r−1)^(r−1).

Its proof uses an upper bound for the difference of adjacent powers and a
strict polynomial inequality, rather than real differentiation. Consequently
K=2r, h=A=r+1, and B=r−1 satisfy the strict moment gap. The threshold h/K can
approach one half from above.

The multiplier condition can be met at one of these thresholds whenever
3^q<4^p. In the checked construction, put a=3^q and t=a², and use r=t+2.
The existing integer geometric-precision lemma gives

    a · a^(t+2) < (4^p)^(t+2),

which is exactly 3^(q(t+3))<2^(p·2(t+2)). The balanced-moment lemma supplies
the other gap at that same block. Thus every exponent satisfying the recorded
threshold has a certificate, and the uniform density proof applies.

The closed-form parameters and eventual counting cutoffs are deliberately
coarse and generally impractical for enumeration. This affects efficiency,
not the theorem's quantifiers. Concrete exponents often admit much smaller
certificates. The independent search finds K=212 for 4/5 and K=2548 for
23/29; the latter illustrates coverage strictly beyond the former 4/5 bound.

## Verification

The final theorem and its bibliographic wrapper build under the pinned Lean
compiler. Fifteen new proof endpoints are included in the axiom audit, using
only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.
The proof does not assume the recorded statement, universal convergence, or
any unproved density result. The full main-library integrity check passed
with the theorem and its bibliographic wrapper included in the axiom audit.

An independent exact-integer probe checks 201 balanced gaps, 971 admissible
exponent certificates among positive p,q≤40, 26 closed-form constructions,
and 480 scale selections at different block lengths. It excludes 629 pairs
that do not satisfy the strict exponent condition. The tests support the
arithmetic implementation; the Lean proof establishes the unbounded result.

```sh
lake build Collatz.Papers.Journal_1994_Korec_a_density_estimate_for_the_3x
lake env lean scripts/audit_korec_certified.lean
python3 scripts/probe_korec_certified.py
bash scripts/check_integrity.sh
```

[Uniform density proof](../Collatz/Papers/KorecCertified.lean),
[certificate construction](../Collatz/Structure/PowerDensityParameters.lean),
[balanced moment gap](../Collatz/Structure/BalancedMomentGap.lean),
[scale selection](../Collatz/Structure/GeneralPowerScaleSelection.lean),
[axiom audit](KorecCertifiedAxioms.txt), [probe](KorecCertifiedProbe.json).

The [certificate-boundary theorem](PowerCertificateBarrier.md) proves the
converse as well: this certificate format exists exactly in the recorded
exponent range. Searching different weights within the same format cannot
prove a smaller exponent.

The [logarithmic-window refinement](KorecLogWindow.md) preserves the witnessing
time: almost every start reaches the power target by floor(log₂ n). It also
provides an executable finite scan with proved exact semantics.
