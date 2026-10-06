# Power descent within a logarithmic window

The certificate proof of the recorded rational cases of Korec's theorem
contains a useful bound on the witnessing time. For every positive q with
3^q < 4^p, Lean now proves that a natural-density-one set of starts n satisfies

    ∃ k ≤ floor(log₂ n), (T^k n)^q < n^p.

Here T is the accelerated map: n/2 for even n and (3n+1)/2 for odd n.
This extracts witness information from the existing classical argument; no
claim of historical novelty is made. The exceptional set need not be empty,
and this statement does not prove universal convergence.

## Why the window is available

On a scale beginning at 2^(K s), the certificate argument proves the target
at the specific time K s. Since 2^(K s) ≤ n, that time is at most floor(log₂ n).
Previously the final interface discarded the time bound when introducing
the existential witness.

The proof now exposes `certified_endpoint_power` and a reusable
`density_one_of_scale_property` lemma. The latter transfers any property
proved on all sufficiently large light-parity portions of the certificate's
scales to a density-one conclusion. Its counting proof retains the discarded
prefix and incomplete final period. The existing Korec theorem and its
bibliographic wrapper retain their original statements.

For p < q, the earlier universal inequality n ≤ 2^k T^k(n) also gives

    n^(q−p) < 2^(k q).

Thus almost every start admits a successful time satisfying both this lower
bound and k ≤ floor(log₂ n). These are integer inequalities; the development
does not require real logarithms or real exponentiation.

## An executable test with exact semantics

`powerScan` retains the current orbit state as it scans a finite segment.
`logPowerCheck p q n` tests times 0 through floor(log₂ n), inclusive, using
at most floor(log₂ n) accelerated transitions. Lean proves that its Boolean
result is true exactly when a target hit exists in that window. Consequently
the success set of this finite test has density one in the recorded range.
This transition bound is not a claim about bit complexity: integer powers
and intermediate orbit values still have computational costs.

False means only that no hit was found within the specified window. For
p/q = 4/5 and n = 3, the window ends at time 1 and the test is false, but
time 4 succeeds. This example is checked by the Lean kernel.

## Independent finite tests

The Python probe compares the rolling scan with direct orbit enumeration on
24,696 combinations of exponents, targets, starting states, and fuel values,
including zero exponents and zero inputs. It also checks every successful
sublinear hit against the lower time bound above.

The measured successes among starts in [0,N) are:

| Exponent | N = 1,000 | N = 10,000 | N = 100,000 |
| --- | ---: | ---: | ---: |
| 3/4 | 548 | 5,247 | 50,326 |
| 4/5 | 622 | 6,183 | 62,662 |
| 23/29 | 602 | 5,946 | 59,308 |
| 1 | 912 | 9,410 | 95,979 |

The 3/4 case lies outside the proved certificate range. Its finite counts
do not establish or refute a density theorem. Even inside the range, these
fractions are far from one and need not increase with N: the 23/29 fraction
falls from 59.46% to 59.308% between the last two cutoffs. The theorem is
asymptotic, and the explicit certificate cutoffs are very coarse.

## Verification

The main-library integrity check passed. The dedicated audit covers all
eleven endpoints in the refactored certificate file, all nine endpoints in
the new window file, and the bibliographic wrapper. Dependencies are confined
to `propext`, `Classical.choice`, and `Quot.sound`; the concrete examples use
no axioms.

```sh
lake build Collatz.Papers.KorecLogWindow
lake env lean scripts/audit_korec_log_window.lean
python3 scripts/probe_log_power_search.py
bash scripts/check_integrity.sh
```

[Lean proof and executable scan](../Collatz/Papers/KorecLogWindow.lean),
[axiom audit](KorecLogWindowAxioms.txt),
[finite probe results](KorecLogWindowProbe.json),
[classical theorem reconstruction](KorecCertified.md).
