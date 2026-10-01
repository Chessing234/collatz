# Rigorous bounds on the odd-step stopping correction

The existing stopping-time note gave three examples where the affine lower
bound was within one step of the actual first arrival at 1. Its wording
suggested more than those examples establish. That wording is now scoped
to the measured cases, and a general upper bound has been proved separately.

For a positive start n with first arrival at 1 at accelerated time k, let
q be the number of odd source values before that arrival. Lean proves

    3^q · n ≤ 2^k,
    3^q · 2^k ≤ 10^q · n.

These are exact integer inequalities. They are conditional on first arrival
existing and do not bound q independently, so they do not prove convergence
or a universal time limit.

## A bound for arbitrary finite prefixes

The general theorem assumes that every odd source value among the first k
steps is at least M. It proves

    M^q · 2^k · T^k(n) ≤ (3M+1)^q · n.

Only the odd source values need this lower bound. Even steps are exact
halvings. At an odd source x≥M, the local scaled inequality is

    M · 2T(x) = M(3x+1) ≤ (3M+1)x.

Multiplying these local inequalities along the prefix gives the result.
The proof handles M=0, n=0, and k=0 in the general interface; the first-hit
specialization separately requires a positive starting value.

Before first arrival at 1, every orbit value is positive and different
from 1. An odd value is therefore at least 3. Taking M=3 and T^k(n)=1 gives
the upper bound. The existing affine estimate supplies the lower bound.

The first-arrival condition cannot simply be dropped. At the later return
1 → 2 → 1, k=2 and q=1. The proposed upper inequality would say 12≤10,
which is false. This counterexample is checked by the Lean kernel.

## What this says about the correction ratio

The real-number gloss, not a separate real-analysis formalization, is

    1 ≤ 2^k / (3^q n) ≤ (10/9)^q.

Thus the additive correction to log₂(n)+q·log₂(3) is at most
q·log₂(10/9). This is much weaker than a uniform one-step error estimate,
but unlike the earlier empirical observation it follows for every first-hit
trajectory from the stated hypotheses. The odd-step count remains part of
the bound and is precisely one of the quantities that needs control.

## Exact finite tests

The probe checks 68,244 prefix/parameter combinations, including empty
prefixes, zero inputs, zero M, and prefixes that later include the odd
source 1. It then checks both first-hit inequalities for all starts from
1 through 100,000, with an explicit finite iteration cap that would report
an unresolved input.

All sampled correction ratios are below 2. The largest observed ratio is
attained at n=993, with k=61 and q=32:

    2^61 / (3^32 · 993)
      = 2305843009213693952 / 1840049047529878113
      ≈ 1.253142144395068.

That finite observation does not prove a universal ratio below 2. The three
examples in the older note were also recomputed: their displayed step
counts, odd counts, and rounded logarithms agree with direct iteration.
No historical novelty is claimed for the product-bound argument.

## Verification

All six theorem endpoints are included in the dedicated axiom audit. The
prefix bound, two-sided first-hit result, and later-return counterexample
are also included in the main-library integrity check.

```sh
lake build Collatz.Strategy.StoppingCorrectionBounds
lake env lean scripts/audit_stopping_correction.lean
python3 scripts/probe_stopping_correction.py
bash scripts/check_integrity.sh
```

[Lean proof](../Collatz/Strategy/StoppingCorrectionBounds.lean),
[corrected earlier note](../Collatz/Strategy/TotalStoppingLower.lean),
[axiom audit](StoppingCorrectionAxioms.txt),
[probe](StoppingCorrectionProbe.json).
