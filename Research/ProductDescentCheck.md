# A finite product certificate for descent

For a positive start n, let q be the odd-step count through time k. Lean now
proves that the strict integer comparison

    (3n+1)^q < n^q · 2^k

certifies an actual descent at some index j≤k. The theorem has no upper
restriction on k. `productCheck n k` is the executable Boolean interface.

This packages the finite-prefix form of the existing product argument.
Related inequalities already occur in the library for cycles and odd-clock
trajectories; no historical novelty is claimed.

## Why the certificate is sound

Assume there was no descent through k. Every odd source value in that
prefix is then at least n. Applying the general scaled prefix upper bound
with M=n gives

    n^q · 2^k · T^k(n) ≤ (3n+1)^q · n.

Since T^k(n)≥n and n is positive, canceling the last factor yields

    n^q · 2^k ≤ (3n+1)^q.

The checked strict inequality contradicts this necessary condition. Hence
a descent occurred somewhere in the prefix. `no_drop_product_bound` and
`productCheck_sound` formalize these two steps.

## Comparison with coefficient crossing

A successful product check always implies 3^q<2^k, because
(3n)^q≤(3n+1)^q. The product condition is therefore stricter than pure
coefficient lightness. It does not improve the already certified
first-crossing result within its 1,024-step horizon; its distinct interface
is an unconditional sufficient comparison valid at any finite horizon.

The strictness matters in practice. The kernel checks that 27 first falls
below its start at time 59, reaching 23 with 37 odd steps. Its coefficient
is light at that time, but the product test is false. The finite probe
finds the first successful product check for 27 only at time 65.

The conclusion also must not be strengthened to endpoint descent. For
2 → 1 → 2, the product check succeeds at time 2, while the endpoint equals
the start. The witness is the earlier value 1. This is another kernel-checked
example. A zero-step window never certifies a strict descent.

## A universal-descent target, with its premise exposed

`convergence_of_universal_checks` proves that

    (∀ n>1, ∃ k, productCheck n k = true)
      implies the Collatz conjecture.

The implication uses the established reduction to excluding positive
never-droppers above 1. The universal premise is not proved here. Nor is
failure of this sufficient test shown equivalent to nonconvergence or to
absence of all descent. The missed first descent of 27 illustrates why
such converse claims require separate arguments.

The checker computes the actual odd count and large integer powers. It is
a transparent arithmetic certificate, not claimed to outperform a direct
scan for a smaller orbit value.

## Finite tests

The independent probe checks all 402,000 prefixes formed by starts 1–2,000
and horizons 0–200. Every successful certificate has an observed earlier
descent and a light coefficient. Every non-descending prefix obeys the
necessary product inequality.

There are 379,821 successful product checks, compared with 380,099 light
prefixes. Four observed first descents are missed by the product check:
starts 27, 31, 47, and 63. In 340 successful checks the endpoint is not below
the start, confirming that prefix and endpoint claims differ. These are
finite comparisons, not evidence establishing the universal premise above.

## Verification

All 10 theorem endpoints are included in the dedicated axiom audit. The
soundness, comparison with coefficient lightness, conditional universal
reduction, and missed-first-descent example are included in the main-library
integrity check.

```sh
lake build Collatz.Strategy.ProductDescentCheck
lake env lean scripts/audit_product_descent.lean
python3 scripts/probe_product_descent.py
bash scripts/check_integrity.sh
```

[Lean checker and proofs](../Collatz/Strategy/ProductDescentCheck.lean),
[axiom audit](ProductDescentAxioms.txt), [probe](ProductDescentProbe.json),
[scaled prefix bound](StoppingCorrectionBounds.md),
[first-crossing certificate](FirstLight1024.md).
