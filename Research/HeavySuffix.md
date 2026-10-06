# Analytic connection to a suffix with no coefficient crossing

2026-09-28. **Verification pending.** The new source has not yet passed
the restored Mathlib build; do not cite it as a checked theorem.

Source: `ProofAtlasAttack/CollatzTargetDensity/HeavySuffix.lean`.

The intended chain is:

1. On a positive injective Syracuse orbit, the existing
   `inverse_terms_summable` theorem makes the terms P_k/3 tend to zero,
   where P_k=2^(a_0+...+a_(k-1))/3^k.
2. Consequently P_k<=1 for all sufficiently large k.
3. Since P_0=1, P attains a global maximum at a finite index m.
4. The multiplier of the suffix starting at m is P_(m+k)/P_m<=1.
5. Thus a hypothetical injective orbit supplies an integer start whose
   coefficient stopping time is infinite.

The draft also states the conditional corollary: if every odd positive
start has a coefficient crossing, there is no injective odd orbit. It does
not establish universal crossing or rule out nontrivial cycles.

No novelty claim is made. The maximum-selection argument is elementary;
the analytic summability result is imported from the earlier development.
Historical background separates the cycle and divergent-trajectory questions:
https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/node5.html
https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/node9.html
These sources are context, not formal proof dependencies.

## Environment and verification state

The previously missing dependency cache has been restored by an existing
process in the shared workspace. A duplicate restoration launched during
this investigation was stopped; the existing process was left intact and
subsequently finished. A fresh check found all 1,485 vendored source hashes
unchanged and all nine dependency revisions equal to their lockfile pins.

The targeted build is running with its log at
`/tmp/collatz-heavy-suffix-build.log`. It compiles the imported proof chain
before checking the new module. Build success and the axiom audit remain
required. The audit entry point is:

    cd ProofAtlasAttack
    LEAN_NUM_THREADS=2 python3 scripts/verify_heavy_suffix.py

Run it after the current build finishes (or after resolving a reported
source error), not concurrently with another build of the same target.
The report will be `Verification/heavy-suffix-report.json`. The script
requires five public endpoints, allowed standard axioms only, pinned
dependencies, unchanged upstream source hashes, and stable local sources.

This restores the ability to check the mathematical connection; it does not
turn the conjecture or the missing universal crossing assertion into a theorem.
