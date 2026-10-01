# Exact exponent boundary of the parity-moment certificate

The certificate used in the [general Korec proof](KorecCertified.md) exists
**if and only if** 3^q<4^p. Lean now proves both directions. Existence was
established in the density proof; the new result proves necessity.

This characterizes the power of this certificate format. It does not say that
the actual Collatz power-density conclusion fails at smaller exponents or
that other proof methods cannot establish such conclusions.

## Why the boundary is forced

A certificate uses a block length K, a threshold h≤K, and ordered weights
B≤A. Its strict moment condition is

    (A+B)^K < 2^K A^h B^(K−h).

If 2h≤K, the homogeneous weight at h is no greater than the weight at K−h.
Their product is (AB)^K. Consequently,

    (A^h B^(K−h))² ≤ (AB)^K.

The elementary inequality 4AB≤(A+B)² then implies

    2^K A^h B^(K−h) ≤ (A+B)^K,

contradicting the strict moment condition. Thus every certificate has K<2h.

The second certificate condition is 3^(qh)<2^(pK). Squaring it and using
K<2h shows that 4^p≤3^q would be impossible: it would force

    (4^p)^K ≤ 3^(qK) ≤ 3^(2qh) < (4^p)^K.

Therefore 3^q<4^p is necessary. Together with the parameter-construction
proof, this yields the exact equivalence.

In particular, no certificate of this format can prove exponent 3/4 because
3^4≥4^3. Finite experiments finding small orbit values at that exponent do
not contradict the barrier: those experiments concern the dynamics, whereas
this theorem restricts a particular sufficient proof condition. Improving
the exponent range requires changing the argument, not merely searching for
larger blocks or better weights inside this format.

No historical novelty is asserted for the underlying inequalities or moment
method. The contribution here is an explicit checked boundary for the
repository's certificate interface.

## Verification

The module builds and seven endpoints pass the standard axiom audit. An
independent exhaustive probe checks 3,234 low-threshold weight inequalities,
finds 1,790 strict moment gaps, and tests 144,990 multiplier conditions over
small parameters. All 56,548 certificates found satisfy the exponent
condition. None certifies 3/4. Zero weights and zero exponents are included
in these boundary checks. The full main-library integrity check also passed
with the exact-boundary theorem included in its axiom audit.

```sh
lake build Collatz.Structure.PowerCertificateBarrier
lake env lean scripts/audit_power_certificate_barrier.lean
python3 scripts/probe_power_certificate_barrier.py
bash scripts/check_integrity.sh
```

[Lean proof](../Collatz/Structure/PowerCertificateBarrier.lean),
[axiom audit](PowerCertificateBarrierAxioms.txt),
[probe](PowerCertificateBarrierProbe.json).
