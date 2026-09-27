# Multiscale Syracuse investigation — 2026-09-07

**Status:** ongoing research, not a breakthrough or a proof of Collatz.
The block-potential algebra is checked in `Collatz/Strategy/BlockPotential.lean`.
Its application to infinite transfer operators below is a mathematical
derivation, not yet a Lean formalization. The needed uniform estimates remain
unproved. Numerical values are exploratory, not certificates.

## A route that avoids the single-scale lift-ratio obstruction

On the 3-adic units, extend test functions by zero on multiples of 3. Write

    L_α h(r) = Σ_{v≥1, 2^v r ≡ 1 mod 3}
                 (3/2^v)^α h((2^v r − 1)/3).

For α>0 set q=2^(−α) and let μ_j^α be the law modulo 3^j of the Syracuse
random variable with independent valuations of law (1−q)q^(v−1).
Let f_j^α(r)=3^j μ_j^α(r), lifted to finer residue spaces when necessary.
Direct substitution in the recursion gives

    L_α f_j^α = s_α f_{j+1}^α,
    s_α = 3^(α−1)/(2^α−1).

This includes Tao's law at α=1, where s_1=1. If
W=Σ_{j=1}^{k−1} f_j^α, then

    L_α W = s_α (W − f_1^α + f_k^α).

W only depends on residues modulo 3^(k−1). Consequently the level-k
minimum-over-three-lifts operator agrees with L_α on W: the three possible
child lifts have equal W-values. This identity avoids the known failure of
uniform lift ratios for a single f_k. It does not supply a useful lower
bound for W by itself.

At α=1, uniform divergence of min_r Σ_{j<k} f_j(r) would make these
one-step lower ratios approach 1, since f_1≤2. That divergence is unproved.
The observed minimum cumulative value is only 2.2871 at k=14.

## A more flexible block criterion

For any positive linear operator L, positive λ, and N≥1 define

    W_N = Σ_{j=0}^{N−1} λ^(N−1−j) L^j g.

Then exactly

    L W_N + λ^N g = λ W_N + L^N g.

Thus L^N g≥λ^N g implies L W_N≥λ W_N. This is elementary algebra,
not an assumption that the block bound holds. `BlockPotential.telescope`,
`one_step_of_block`, and `potential_pos` verify its natural-number version;
rational finite operators can be cleared of denominators. No infinite
Collatz operator or analytic limiting assertion is formalized there.

Take g to be the indicator of the units. Since f_1^α≤B_α g with
B_α=3/(1+q), positivity gives

    L_α^(n−1) g ≥ (s_α^(n−1)/B_α) f_n^α.

Consequently a lower bound m_n^α=min_units f_n^α gives a block bound

    λ = s_α (m_n^α/B_α)^(1/(n−1)).

The resulting W depends only on residues modulo 3^(n−1), so again the
level-n minimum-over-lifts operator agrees with the full operator on W.
All statements here concern the full valuation sum. Implementing a finite
certificate additionally requires a controlled valuation tail.

One substantial target is **subexponential minimum-density decay for biased
laws at α<1 arbitrarily close to 1**. It would make the displayed block
bounds approach s_α>1 and hence give strict finite-level transfer margins.
The usual counting-certificate machinery would still need to be applied.
No such minimum-density estimate is established here.

The distinction between α=1 and nearby α is essential. At α=1 this formula
only produces limits of lower bounds at 1; it does not alone prove that
critical counting exponents approach 1. One must justify that further step,
for example by proving the needed biased-law estimates. The older claim in
`StochasticTree.md` skipped it as well as extrapolating finite data.

## Reverse implication: the same limiting optimization problem

Further audit establishes that the block/minimum-atom viewpoint does not
itself strengthen the finite-cylinder certificate method. Here is a precise
mathematical equivalence, with no spectral compactness assumption.

Fix α>0, let g be 1 on the units, and put

    b_N = min_units L_α^N g,     b_0=1.

These minima exist: each iterate depends on finitely many ternary digits.
They are positive, and bounded above and below exponentially in N.
Positivity and homogeneity imply b_(N+M)≥b_N b_M. Therefore the
superadditive lemma applied to log b_N gives

    R = lim_N b_N^(1/N) = sup_{N≥1} b_N^(1/N).

R is exactly the supremum of the lower one-step ratios obtained from all
strictly positive finite-cylinder test functions. The proof has two parts:

1. The block-potential construction supplies such a test function with
   ratio b_N^(1/N), for every N≥1.
2. Conversely, if L_α w≥λw and a g≤w≤b g for constants 0<a≤b,
   then positivity and iteration give

       b L_α^N g ≥ L_α^N w ≥ λ^N w ≥ a λ^N g.

   Hence b_N≥(a/b)λ^N, and λ≤R after taking N-th roots.

The natural-number algebra of the reverse implication is now checked in
`BlockPotential.block_of_certificate`, using `orbit_mono`, `orbit_scale`,
and `orbit_subeigen`. The real limits and the infinite-operator application
in this section remain a written proof, not a Lean theorem.

This supremum also equals the supremum over all levels of the
minimum-over-lifts lower ratios. A level-k certificate is valid for L_α;
conversely, for a test function depending on k digits, the level-(k+1)
minimum-over-lifts operator is exactly L_α on that function.

Set a_α=3q/(1+q) and B_α=3/(1+q). The bounds
a_α g≤f_1^α≤B_α g imply

    a_α b_N ≤ s_α^N m_(N+1)^α ≤ B_α b_N.

In particular the exponential rate of the minimum density exists and

    lim_n (m_n^α)^(1/n) = R/s_α.

Thus subexponential minimum-density decay is equivalent to R=s_α:
complete disappearance of the loss at that exponent in the limit of the
same finite-level hierarchy. Obtaining counting certificates requires the
weaker condition R>1. The probability formulation changes the objects one
can analyze, but it does not establish either condition.

**Decision:** do not count this equivalence as a new Collatz bound or as an
independent mechanism. Further work on this route needs an actual estimate
from the affine recursion, not another reformulation of R.

## Reproducible tests

Run:

```sh
python3 scripts/syracuse_multiscale.py --levels 14 --alpha 1
python3 scripts/syracuse_multiscale.py --levels 14 --alpha 0.95
```

| α | n | min f_n | n min f_n | min Σ f_j | sum-vector ratio | block bound |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 6 | 0.090393 | 0.542355 | 1.796066 | 0.466717 | 0.538295 |
| 1 | 10 | 0.060876 | 0.608765 | 2.082097 | 0.535871 | 0.678408 |
| 1 | 14 | 0.046917 | 0.656841 | 2.287097 | 0.574690 | 0.749271 |
| 0.95 | 14 | 0.065048 | 0.910670 | 2.608059 | 0.633294 | 0.781145 |

These do not compete with optimized finite-level certificates. A bound
m_n≥c/n is consistent with this short range but is **not proved or claimed**.
Neither is its validity inferred from a curve fit.

The script uses the geometric law conditioned on v≤64. Coupling each
valuation with the original law bounds total variation error by n q^64,
and pointwise normalized-density error by 3^n n q^64. At n=14 this is
3.7e−12 for α=1 and 3.4e−11 for α=0.95. Floating-point rounding is separate
and uncertified; these tail bounds do not turn the computations into proofs.

## Exact restrictions on the minimum at exponent 1

For the actual density f_n (and only at α=1 in this section), grouping
valuations by their parity gives

    f_n(2r)=2f_n(r)                          (r≡1 mod 3),
    f_n(r)=f_n(4r)/4 + 3f_(n−1)((4r−1)/3)/4 (r≡1 mod 3).

Arguments are taken modulo the relevant power of 3. The lower-level density
vanishes on multiples of 3. Projective consistency gives m_n≤m_(n−1).

For n≥2, **a minimum is attained in class 7 modulo 9**. Here is a proof,
not just the observed location of the numerical minimizers. A minimizing
unit cannot be 2 modulo 3: the doubling identity supplies another unit with
half its strictly positive density. If a minimizer r is 1 or 4 modulo 9,
the child in the second displayed identity is a unit. Both terms are bounded
below by their coefficients times m_n, since m_(n−1)≥m_n. Equality forces
f_n(4r)=m_n. Multiplication by 4 takes classes 1→4→7 modulo 9, so after
at most two such steps a minimizer in class 7 is obtained. This does not
assert that every minimizer is in class 7.

The doubling identity also gives f_n≥m_n f_1 on all residues: f_1 is 1
on class 1 and 2 on class 2 modulo 3. Apply the positive transfer and use
the exact value min f_2=2/7 to obtain

    m_(n+1) ≥ (2/7)m_n.

This is an elementary exponential lower bound, not the desired polynomial
bound and not a claimed improvement over existing work.

The correlation that this scalar bound drops is visible by expanding three
pairs of valuations at r≡7 modulo 9:

    f_n(r) = f_n(64r)/64
             + 3f_(n−1)((16r−1)/3)/16
             + 3f_(n−1)((64r−1)/3)/64.

The two children are a and 4a+1. Replacing their densities independently by
coarse floors loses precisely the information needed to improve this
argument. The identities and minimum-location proof in this section are
written mathematics; they are not yet theorems about a formalized Syracuse
probability law in Lean.

## Testing a proposed scalar induction

Update, 2026-09-08: the complete actual-law scan now covers levels 1–18
using exact integer enclosures. The candidate survives this finite range.
See [SyracuseCycleScan.md](SyracuseCycleScan.md) for the cyclic recurrence,
independent checks, and the limited scope of the Lean error proof. No
all-depth estimate follows from these data.

The first 15 actual-law minima numerically satisfy

    1/m_(n+1) − 1/m_n < 3,

which, if proved for every n, would give m_n≥1/(3n−2). This is an
unproved candidate, not an estimate supplied by these experiments. At n=15
the minimum is approximately 0.04411327288; the largest observed reciprocal
increment is about 2.57572, between levels 2 and 3.

An exact falsification test shows why the most immediate induction does not
work. Consider the following alternative normalized density on residues
0 through 8:

    f = (0, 2, 4, 0, 17, 4, 0, 2, 34) / 7.

It has all four of these properties:

- zero on multiples of 3 and minimum 2/7 on the units;
- Haar mean 1;
- projection onto the first Syracuse density (0,1,2) modulo 3;
- f(2r mod 9)=2f(r) for r≡1 modulo 3.

Nevertheless its full exponent-1 transfer at r=25 modulo 27 is

    L_1 f(25) = 794/9709 < 2/13 = (2/7)/(1+3*(2/7)).

To compute this exactly, group valuations by their residue in 1..18,
using 2^18≡1 modulo 27. The total weight of valuations v+18j is
3·2^(18−v)/(2^18−1). This gives the common-denominator numerator 150066
over 7(2^18−1), which reduces to the value above.

`SyracuseFloorObstruction.lean` checks normalization, projection, the
doubling identity, the floor, the modular period, and the exact finite
transfer calculation and strict inequality. The geometric-series grouping
is the written argument relating that calculation to the infinite transfer.

This f is **not** the actual level-2 Syracuse density. The example therefore
does not refute the candidate recurrence for the actual sequence, and is not
a Collatz counterexample. It refutes deriving that recurrence from just the
four listed properties. A successful induction must retain further
correlations imposed by the actual affine recursion.

## Actual-law counterexample to a sufficient pair bound

Define J_n=min_{a≡1 mod 3}(f_n(a)+f_n(4a+1)/4). The paired-child identity
and the minimum-location result give m_(n+1)≥(4/21)J_n. A sufficient
condition for the proposed logistic induction would therefore be

    J_n ≥ 21 m_n / (4(1+3m_n)).

**This sufficient condition is false for the actual Syracuse law.** It fits
the numerical levels 1–13 but fails at level 14, at a=1292371 and
b=4a+1 modulo 3^14=386516. This is different from the earlier counterexample
using an alternative density: the present calculation concerns the actual law.
It still does not refute the logistic recurrence for m_n itself.

The failure is verified by integer interval arithmetic in
`scripts/syracuse_pair_check.py`, without a floating-point decision. With
S=2^60, compute lower atom numerators B_n by adding floor(B_(n−1)/2^v)
over valuations v=1..60. Each actual atom lies in

    [B_n/S, (B_n+61n)/S].

Indeed each step costs at most 60/S in downward rounding, 1/S in omitted
geometric tail, and the previous uniform error multiplied by at most
Σ_{v≥1}2^(−v)=1. The image map for any fixed valuation is injective, and
all array additions and modular products are within their integer ranges.

At level 14 the exact calculation gives

    min_units B_14 = 11309259873,
    B_14(a) = 24144379077,
    B_14(b) = 111370549614,
    E_14 = 854.

Writing M=3^14, d=min B_14 and C=4B_14(a)+B_14(b)+5E_14, the decisive
strict inequality is

    C(S+3Md) < 21dS.

Its exact positive margin is 319784278245251080746673904. Since
t↦21t/(4(1+3t)) is increasing, this proves that the upper enclosure for
the selected pair is below the proposed bound evaluated even at the lower
enclosure for the true minimum. For orientation only, the respective values
are approximately 0.215671486 and 0.215923662.

Reproduce with `python3 scripts/syracuse_pair_check.py`; the expected result
is stored in `SyracusePairCounterexample.json`. A second run at precision
and cutoff 56 also refutes the condition. Exact rational computations check
the interval construction against every reported atom and the minimum at
levels 1–3. This is a reproducible exact-arithmetic calculation, **not a
Lean-verified probability theorem**.

**Decision:** discard this pair-minimum sufficient condition. Any remaining
use of the paired-child recurrence must retain more correlation, including
the term f_(n+1)(64r), or use a different inequality. The scalar logistic
recurrence remains unproved and unrefuted by this test.

## Counting obstruction to a few-word certificate

A separate test rules out proving the target minimum mass by selecting just
one, polynomially many, or even subexponentially many valuation words per
residue. This is an elementary counting argument, not a novelty claim or a
Collatz convergence theorem.

A positive length-n valuation word of total S has probability 2^(−S).
The number of such words with total at most s is binomial(s,n): map a word
to its n strictly increasing partial sums in {1,...,s}. Each word produces
just one residue modulo 3^n, so it can cover at most one of the
2·3^(n−1) units.

The arithmetic inequalities checked in `ShortWordCount.lean` are

    binomial(s,n)·2^n ≤ 3^s,
    binomial(s,n)^5·32^n ≤ 3^(5n)·27^n   if 5s≤8n,
    binomial(s,n) < 2·3^(n−1)            if also n≥12.

The first follows from weighted Pascal induction. Raising it to the fifth
power gives the second; the strict third bound uses
243·27^n < 32·32^n for n≥12. These statements avoid approximate logarithms.
The composition bijection and residue pigeonhole application are written
mathematics, not formalized in that Lean file.

Take s=floor(8n/5). For every n≥12 some unit residue has no valuation word
with total at most s. In fact the fraction of units covered by such words
is at most (3/2)(27/32)^(n/5), which tends to zero. For each uncovered
residue every individual word has probability less than 2^(−8n/5).

Consequently, summing K_n selected words at such a residue gives at most
K_n·2^(−8n/5). To reach a bound of order 3^(−n)·exp(−o(n)), one needs

    K_n ≥ (2^(8/5)/3)^n · exp(−o(n)).

The base is strictly greater than 1 because 2^8=256>243=3^5. Thus a
subexponential number of selected words cannot give the desired uniform
minimum-atom estimate. This does not bound the full probability from above:
many words can contribute to it, and a symbolic proof can handle them
collectively without enumerating them.

**Decision:** do not seek a near-critical minimum-atom bound from a few
particularly short inverse words. Any successful certificate of this type
must capture exponentially many contributions collectively.

## Fixed-total word families

The next collective test counts every positive length-n valuation word with
total exactly 2n. Each contributes 4^(−n). `scripts/syracuse_shell.py`
computes the residue counts with exact integers and checks that their sum
is binomial(2n−1,n−1).

At depths 6, 9, and 12, respectively, this family misses 162 of 486,
3266 of 13122, and 57370 of 354294 unit residues. Thus it does not yet
give a positive minimum at these depths. No eventual-coverage claim or
permanent obstruction follows from these finite counts.

Residue 1 has exactly one word at every tested depth through 12: the word
whose valuations are all 2. This pattern must not be extrapolated. The
verified ordinary integer orbit of 159 reaches 1 in 18 odd-to-odd steps
with total valuation 36, producing an additional word at depth 18.
The script checks this second word directly modulo 3^18.

There is an arithmetic reason this family is difficult. A word producing
residue 1 yields, by successive inverse steps with its valuations, a positive odd integer
predecessor b with n Syracuse steps to 1 and

    b < 2^(2n)/3^n = (4/3)^n.

Intermediate integrality follows from the residue condition, positivity
from starting the inverse construction at 1, and the size bound from the
positive affine offset. Distinct words yield distinct predecessors because
the odd-to-odd map determines each subsequent valuation. Consequently a
near-critical lower bound for this single fixed-total family at residue 1
already requires a large family of actual integer predecessors at this
scale; its large total number of words does not supply that lower bound.

## Why averaged mixing does not close the argument

Tao's fine-scale mixing estimate controls an L1 discrepancy, not the
smallest atom. This distinction cannot be removed by full support or even
exponentially fast L1 approximation alone. Here is an explicit mathematical
counterexample to that abstract inference, **not a Syracuse law**.

On Z_3 with Haar probability measure, fix a and put

    h(x) = (4/3) |x−a|_3.

The integral of |x−a|_3 is (2/3)Σ_{t≥0}9^(−t)=3/4, so h is a probability
density with full support. Let f_n be its conditional expectation on residue
classes modulo 3^n, and let μ_n be the corresponding probability law.
On the class a modulo 3^n,

    f_n(a)=3^(−n),    μ_n(a)=9^(−n).

On any other class, with t=v_3(r−a)<n, f_n(r)=(4/3)3^(−t), so the center
is the minimum. For n≥m the discrepancy f_n−f_m is supported entirely on
the class a modulo 3^m, whose probability mass is 9^(−m). Thus

    ||f_n−f_m||_L1 ≤ 2·9^(−m),
    Σ_{n≥1} f_n(a) = 1/2.

This family has stronger averaged mixing than a superpolynomial-in-m bound,
but exponentially small normalized minimum atoms and a finite cumulative
value at a. A successful proof for Syracuse laws must use their particular
stationarity/affine structure in an additional way.

## Prior work and novelty gate

Krasikov–Lagarias's original goal already includes counting powers arbitrarily
close to 1; the target itself is not new. See their
[paper](https://arxiv.org/abs/math/0205002).

Tao establishes fine-scale L1 mixing for the Syracuse law in Proposition 1.14
of [his paper](https://arxiv.org/abs/1909.03562); it does not state the minimum
atom estimate needed here.

The abstract of a [Nikpour–Rabbani preprint posted August 2026](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7239062)
claims a level-20 counting exponent 0.914947 and explicitly connects its
operator with bounds on the smallest Syracuse atom. Only the abstract was
accessible in this investigation; the full proof has not been audited.
This is an additional reason not to claim that the operator/minimum-atom
connection discovered in this session is novel.

### Further literature discovered during the fixed-total investigation

A [July 2026 ProofAtlas release](https://www.proofatlas.ai/formalizations/natural-density-log-time-collatz/)
claims natural-density almost-bounded descent with a logarithmic clock.
Its headline Lean source and selected adapters were inspected; its recorded
axiom report lists only the standard classical Mathlib axioms. The full
dependency chain has not been independently audited or rebuilt here.

The same site's [September 5 release listing](https://www.proofatlas.ai/advances/)
claims positive lower natural density of starts reaching 1 within
10.46 log n raw steps. Only the listing has been inspected so far. This
potentially changes the counting frontier and should be audited before
choosing an extension. Neither release is a result of this repository,
and neither is asserted here as independently verified.

The remaining question is mathematical, not a missing Lean tactic:
derive a sufficiently strong uniform bound from the actual affine recursion,
or find a different non-circular mechanism controlling exceptional orbits.
