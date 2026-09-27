# Finite cutoffs and the least-counterexample argument

**Status: checked in Lean and included in the successful full package audit.
The Collatz conjecture remains unproved.**

The predecessor-density theorem has an eventual cutoff. This follow-up makes
the counting cutoff explicit once an activation generation is supplied, and
tests whether it could be used to find a predecessor below a least
counterexample.

## An explicit counting cutoff

For an initial floor b, cap-growth bound L, root bound M and activation
generation N, define

    H(b,L,M,N) = 2^((2N+4)b 2^N + N(L(N+1)+1)) M,
    Y0(b,L,M,N) = 32(H(b,L,M,N)+1).

The arbitrary-target theorem now proves

    P_a(Y) >= eta Y / (32 Pbar)       for every Y >= Y0(b,L,M,N),

provided the counting state satisfies its existing root-span and cap
conditions, its nonperiodic roots reach a, all initial roots are at most M,
its source potential is positive and at most Pbar, and terminal mass is at
least eta at every generation n>=N. The synchronization requirement is
N>=10^9(e+L+3), where e is the root-span parameter. A positive density
conclusion uses eta>0.

The theorem is `targetCount_from_bounded_roots_and_explicit_start`.
It adapts the pinned source's explicit interval bounds and the local
arbitrary-target source-counting argument. **It does not bound N in terms
of the target.** Supplying a numeral expression for Y0 does not remove the
activation hypothesis.

## Why this cutoff does not force descent

Lean proves Y0(b,L,M,N)>M for every b,L,M,N. If m were a least positive
counterexample, then every positive seed M reaching 3m+1 would also be a
counterexample, hence M>=m. Thus this particular cutoff satisfies Y0>m.

The theorem supplies no predecessor count at cutoff m. This only locates
the cutoff of this construction; it does not exclude another construction
with a useful smaller cutoff or a different contradiction.

## A checked test of an unconditional shortcut

The following three facts hold simultaneously:

    1027 reaches 1;
    P_3082(1027) = 0, where 3082 = 3*1027+1;
    there exist c>0 and X0 such that P_3082(X)>=cX for every X>=X0.

The zero count is an infinite-time statement. A Boolean checker verifies
that each positive start below 1027 avoids 3082 until reaching 1 within
512 ordinary steps. Its soundness proof then uses the invariant cycle
{1,2,4} to exclude a later visit to 3082. Both the certificate and the
soundness theorem are checked by Lean's kernel. The convergence of 1027
itself is checked separately.

Consequently the following unconditional proposed strengthening is false:

    For every odd m>1024, a positive eventual lower bound for
    P_(3m+1)(X) can be activated by some X0<=m.

Applying such a bound at X=m=1027 would assert a positive lower bound for
a zero count. This counterexample does not refute a conditional argument
that uses the assumption that m is a least bad value: 1027 is convergent.

The [original lemma chain](CollatzProofChain.md) still needs its unproved
upper-tail inequality, or a separate argument establishing convergence.
Neither positive asymptotic predecessor density nor this explicit cutoff
provides that missing implication.

## Reproduction

- [Lean proofs and finite certificate](../ProofAtlasAttack/CollatzTargetDensity/FiniteCutoff.lean).
- [Signature and axiom checks](../ProofAtlasAttack/Verification/FiniteCutoff.lean).
- [Verification report](../ProofAtlasAttack/verification/local-report.json).

From `ProofAtlasAttack`, run:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

This stage's full audit passed on 2026-09-08 with 146 named endpoints, including
11 from this module. Their transitive footprints contain only `propext`,
`Classical.choice`, and `Quot.sound`. All 1,485 pinned upstream source hashes
remained unchanged; all 42 extension hashes matched that stage's successful
report. The current report also includes the [ergodic checks](ErgodicChecks.md).
The [audit log](../ProofAtlasAttack/verification/finite-cutoff-axioms.log)
records the literal cutoff expressions and theorem signatures.
