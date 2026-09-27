# Uniform harmonic predecessor bounds

**Status: the theorem and its integer-counting interpretation are checked in
Lean. The full audit passes with 210 named endpoints, including 30 from
this chain. Collatz remains unproved. No historical novelty is claimed.**

A subsequent [orbit packing chain](OrbitReciprocals.md) uses these estimates
to bound reciprocal sums on hypothetical divergent orbits. The current
package audit includes that extension and has 230 named endpoints.

For the ordinary Collatz map, write `x -> a` when the forward orbit of x
visits a, including a visit at time zero. Define

    H_X = sum_{1 <= x <= X} 1/x,
    L_a(X) = (sum_{1 <= x <= X, x -> a} 1/x) / H_X.

The new theorem establishes absolute constants `d > 0` and a natural
number `A >= 1` such that

    3 does not divide a, X >= (A*a)^2  ==>  L_a(X) >= d/a.

Both constants are independent of a and X. They are proved to exist;
numerical values have not been extracted. This is a uniform lower bound
for logarithmic counting ratios. It neither asserts that their limit
exists nor gives a lower natural density of order 1/a.

The endpoint is
[`uniform_raw_logCountingRatio_lower`](../ProofAtlasAttack/CollatzTargetDensity/HarmonicDensity.lean).
Its definitions use the imported ordinary Collatz reachability and the
imported logarithmic counting ratio, normalized by H_X.

## The lemma chain

1. **Exact generator law.** The previously checked
   [fixed-cost polynomials](FixedCostGenerators.md) satisfy
   `G_n(1/2,r) = 2^n Z_n mu_n(r)`, with `2/3 <= Z_n <= 1`.
   The existing uniform Syracuse atom theorem therefore gives
   `G_n(1/2,r) >= c (2/3)^n` on every unit residue.

2. **A bounded cost window.**
   [GeneratorCostTail.lean](../ProofAtlasAttack/CollatzTargetDensity/GeneratorCostTail.lean)
   proves `G_n(3/4,r) <= 4^n`. Since all coefficients are nonnegative,

       sum_{k > 5n} g_n(k,r) 2^(-k)
           <= (2/3)^(5n) G_n(3/4,r)
           <= (128/243)^n.

   Relative to `(2/3)^n`, this error decays as `(64/81)^n`.
   Thus some absolute c'>0 and N>=1 work for every n>=N and unit r:

       sum_{k <= 5n} g_n(k,r) 2^(-k) >= c' (2/3)^n.

   This is an aggregate window estimate. The lower bound at one
   specified central cost remains unproved.

3. **Exact truncation recursion.**
   [GeneratorWindow.lean](../ProofAtlasAttack/CollatzTargetDensity/GeneratorWindow.lean)
   proves the coefficient cutoff commutes with finite sums and handles
   multiplication by X^j with exactly the remaining budget K-j. All
   period, cost, and divisibility conditions are retained.

4. **Real integer predecessors.**
   [GeneratorPredecessors.lean](../ProofAtlasAttack/CollatzTargetDensity/GeneratorPredecessors.lean)
   constructs finite sets of actual odd predecessors. An admissible
   branch with exponent j+1 has child

       b = (2^(j+1) a - 1)/3,
       2^(j+1) a = 3b + 1,  b > 0,  Syr(b) = a.

   Distinct branches have distinct children. Determinism then makes
   their sets of fixed-depth sources disjoint. Induction proves that
   every selected source reaches a in n Syracuse steps and is at most
   `2^(K+n) a`. The same induction, using `1/b >= 3/(2^(j+1)a)`, proves

       harmonicMass(n,K,a) >= (3/2)^n shortValue(n,K,a)/a.

   Setting K=5n cancels the two exponential factors. Every depth n>=N
   contributes at least c'/a in harmonic mass, below the cutoff 64^n a.

5. **Disjoint depths and ordinary targets.** If a target is nonperiodic,
   an integer can hit it at only one depth. Hence depth contributions
   can be added without repetition. The previously checked bounded
   seed supply gives, for any target a prime to three, an odd, fertile,
   nonperiodic root M reaching a with `M <= C*a`, where C is absolute.
   This selection does not assume convergence or exclude unknown cycles.
   [HarmonicTargets.lean](../ProofAtlasAttack/CollatzTargetDensity/HarmonicTargets.lean)
   transfers the disjoint sources to ordinary Collatz predecessors and
   obtains

       logCount(rawReaches(a), 2^(6(N+L))*C*a) >= (L+1) d0/a.

6. **Every sufficiently large cutoff.**
   [HarmonicDensity.lean](../ProofAtlasAttack/CollatzTargetDensity/HarmonicDensity.lean)
   interpolates these exponential cutoffs. For a general B>=1 and
   X>=B^2, put q=floor(log_64(X/B)). Then

       B*64^q <= X < 64^(2(q+1)),
       H_X <= 1 + log X <= 13(q+1).

   Monotonicity of the numerator gives a ratio at least one thirteenth
   of the per-generation coefficient. Take `B=2^(6N)*C*a` to obtain
   the displayed theorem.

## What still prevents a Collatz proof

[HarmonicProofGap.lean](../ProofAtlasAttack/CollatzTargetDensity/HarmonicProofGap.lean)
connects the estimate to the least-counterexample argument. If m were
the least positive integer failing to reach 1, it would be odd, and
every predecessor of 3m+1 would avoid values below m forever. Consequently,
some absolute d1>0 and B>=1 satisfy

    X >= (B*m)^2  ==>  logCountingRatio(avoidsBelow(m), X) >= d1/m.

No contradictory upper bound for this actual avoidance set has been
proved. For any fixed positive C and any fixed integer p>=0, the file
also checks that `d1/m < C/(log m)^p` eventually. An upper estimate of that
inverse-logarithmic size would therefore not close this comparison.
This does not prove that a stronger estimate is impossible.

The result concerns predecessors of a prescribed target. It does not
prove that every forward orbit reaches 1, and it does not resolve the
fixed-central-cost generator condition.

## Evidence and sources

The chain extends the repository's checked uniform Syracuse atom bound
and finite generator identity. The relationship between Syracuse laws
and predecessor counts is classical; see
[Tao's 2020 discussion](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/)
and [Wirsching's generator treatment](https://www.math.uni-bielefeld.de/baake/algdyn/posden.pdf).
The new Lean derivation does not import either discussion as an assumption.

Run in ProofAtlasAttack:

    LEAN_NUM_THREADS=4 python3 scripts/verify.py

The full build completes 5,096 jobs. The
[report](../ProofAtlasAttack/Verification/local-report.json) contains 210
named theorem footprints; the
[new evidence](../ProofAtlasAttack/Verification/harmonic-targets-axioms.log)
contains 30 from this chain. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. All 1,485 pinned upstream source hashes are unchanged,
and all 51 extension source hashes match the successful report. The audit
rejects unfinished proofs, additional axioms, and native proof escapes.
