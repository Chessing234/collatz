# Coefficient crossing, exact descent, and interval shape

Investigation dated **6 October 2026**, starting at
`0b0fa49f1dab57e4bc8790b0c09121b7162ce28c`.
All additions and commits for this investigation are measured against that
revision. The inherited source and historical commits are excluded.

**This development does not prove the Collatz conjecture.** It extends a
kernel-checked conditional coefficient-descent horizon from 128 to 256,
proves an effective finite-exception transfer theorem, and resolves the
previous interval-shape census question through depth 256. Its elementary
arguments formalize and connect classical ideas; no historical priority or
new literature-level breakthrough is claimed.

## Literature context

These are established reference results, not theorems newly formalized by this
patch. Sources were checked on the date above. Natural density and logarithmic
density are different notions, and neither an almost-everywhere theorem nor a
finite computation settles every input.

| Work | Notable result | Limit relevant to this investigation |
| --- | --- | --- |
| Terras (1976), independently Everett (1977) | Almost every starting integer, in natural density, eventually falls below its start. Terras's parity-vector analysis relates actual and coefficient stopping times through finite exceptions in each fixed class. | Exceptional starting integers may remain. A local or density argument must not be promoted to universal descent. |
| Korec (1994) | For every exponent greater than log(3)/log(4), almost every orbit reaches at most that power of its initial value, in natural density. | This is still a growing target and an almost-everywhere assertion. |
| Krasikov–Lagarias (2003) | Difference inequalities and computer assistance yield at least x^0.84 inputs below x whose orbits reach one, for sufficiently large x. | A lower bound on a subset does not give complete coverage. |
| Tao (2019; published 2022) | For every function f tending to infinity, the orbit minimum is at most f(N) for logarithmically almost every N. | Neither convergence to one nor a uniform bounded minimum for every N follows. |
| Hercher (2023; corrigendum 2026) | A nontrivial cycle must have at least 92 local minima. | Local minima are not total steps; excluding short cycles does not exclude divergent orbits. |
| Barina's computational project | The page consulted reports all starts below 2075 × 2^60 checked; it records the 2^71 milestone on 15 January 2025. | This is an external finite computational result, separate from this project's Lean certificates. |

Primary and author-hosted sources:

- [Terras's publication record](https://eudml.org/doc/205476). The full-paper endpoint was unavailable during this run; the stopping-time mechanism was checked against [Lagarias's author-hosted exposition, Theorems A–C](https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/node4.html).
- [Krasikov–Lagarias, original paper](https://arxiv.org/abs/math/0205002).
- [Tao, revision 7](https://arxiv.org/abs/1909.03562v7), which also states the preceding Korec bound. This revision records corrections made in July 2026.
- [Hercher's published result and corrigendum link](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html).
- [Barina's live verification project](https://pcbarina.fit.vut.cz/).

This is a selected literature review, not an exhaustive survey of all 2026
preprints. No unreviewed claimed solution is treated as an established theorem.

## Definitions and exact statements

Use the accelerated map T(n)=n/2 for even n and T(n)=(3n+1)/2 for odd n.
Let a(n,k) count odd steps among the first k applications of T. Define

    FirstLight(n,k) := 3^a(n,k) < 2^k
                      and 2^j <= 3^a(n,j) for every j<k.

An actual first descent additionally needs T^k(n)<n. The nonnegative additive
correction in the affine identity explains why coefficient contraction alone
is not an automatic proof of this inequality.

### A checked horizon for unbounded inputs

[Horizon.lean](../../Collatz/Research/CoefficientDescent/Horizon.lean) proves

    n > 1 and k <= 256  ==>  (stoppingTime(n,k) <=> FirstLight(n,k)).

There is **no upper bound on n**. There is also no assertion that a first
coefficient crossing exists by 256 for every n. The explicit input
2^257−1 has no crossing and no actual descent in that entire horizon;
[Examples.lean](../../Collatz/Research/CoefficientDescent/Examples.lean)
checks it in Lean. At n=1 the coefficient crosses at time 2 while T^2(1)=1,
so the hypothesis n>1 is necessary.

The proof reuses the repository's accumulator bound at a first crossing:

    failure to descend ==> 3 (2^k−3^a) n <= a 3^a.

For all 0<=a<=k<=256 with 3^a<2^k, exact arithmetic gives

    a 3^a < 3 (2^k−3^a) 6701.

Thus failure forces n<6701. Every even n>1 has a one-step proof; the remaining
3,349 odd n from 3 through 6,699 have explicit checked witnesses. Their largest
first crossing is 81. Uniqueness of the first crossing lets a small-input
witness settle any proposed crossing time for that same input.

[Gap.lean](../../Collatz/Research/CoefficientDescent/Gap.lean) also proves that
6700 does not suffice for this particular uniform arithmetic bound: the
critical pair is (k,a)=(233,147). This is optimality of the numerical bound,
not a claim that an actual Collatz orbit fails at input 6700 or at that pair.
The finite horizon is a formalization improvement over this repository's
previous checked horizon, not a record relative to historical computational
work on coefficient stopping times.

### Effective transfer and a precise interval obstruction

The existing congruence engine gives, for n=2^k m+r and j<=k,

    T^j(n) = 3^a(r,j) 2^(k−j) m + T^j(r).

[Transfer.lean](../../Collatz/Research/CoefficientDescent/Transfer.lean)
defines the conservative explicit cutoff

    M(k,r) = 1 + sum_{j=0}^k T^j(r)

and proves for every natural r, without requiring r<2^k,

    m >= M(k,r)  ==>  (stoppingTime(2^k m+r,k) <=> FirstLight(r,k)).

If a prefix is light, its scaled integer slope is at least one below 2^k,
and m>T^j(r) makes that prefix actually descend. If it is heavy, the
nonnegative affine correction prevents descent. This proves the equivalence
with an explicit cutoff, rather than an unspecified sufficiently-large clause.

Consequences formalized in the same file:

- The exact-time interval is unbounded precisely when the coefficient word is
  first-light at the specified depth.
- If the coefficient word is not first-light, all exact-time indices are below
  M(k,r).
- A bounded nonempty exact-time interval gives an actual first descent that is
  later than an earlier coefficient crossing. That earlier crossing fails to
  produce descent.
- Conversely, an actual finite first descent that disagrees with the coefficient
  event gives a bounded nonempty exact-time interval.
- At all depths, exclusion of finite nonempty intervals is equivalent to
  coefficient/actual agreement **for inputs with a finite actual first descent**.

The last qualification matters. An input that crosses in coefficient but
never actually descends would not give a nonempty exact-time interval.
Consequently the interval-shape equivalence must not be read as a proof of
unrestricted coefficient correctness or of crossing existence.

### From the census observation to a bounded-depth theorem

[Intervals.lean](../../Collatz/Research/CoefficientDescent/Intervals.lean)
combines transfer with the 256-step theorem. For every k<=256 and every r:

- Increasing the class index preserves exact first descent.
- A nonempty exact-time interval has no finite upper endpoint.
- The classifier returns either an empty set or an infinite tail.

This extends the earlier finite census through depth 16 to **all class
representatives and all class indices through depth 256**, without enumerating
2^256 residue classes. The corresponding question at unrestricted depth remains
open in this development.

## Universal descent: what remains

[Universal.lean](../../Collatz/Research/CoefficientDescent/Universal.lean)
separates two obligations:

1. Every n>1 has some first coefficient crossing, with time allowed to depend
   without bound on the input.
2. Every such first crossing produces an actual descent.

Together these imply Collatz by strong induction, using the existing exact
interval coverage reduction. This patch proves obligation 2 only for crossings
through 256. Neither obligation is established at unrestricted depth. Under
obligation 2 as an explicit hypothesis, coefficient coverage is equivalent to
Collatz. The hypothesis is present in the Lean theorem, not hidden in a name.

Other approaches in the literature review—density, inverse-tree lower bounds,
and cycle exclusion—supply valuable information but do not discharge those two
universal obligations. This investigation keeps those distinctions explicit.

## Certificates, commits, and verification

The atlas has 100 batches of 33 or 34 distinct odd inputs. Each input supplies
an executable complete-class certificate and an infinite-ray stopping-time
theorem. Each batch also proves exhaustive coverage of its odd-input interval;
the aggregate glues these intervals into the complete small-input range.
Different rays may overlap. Neither the rays nor the batches are claimed to be
independent mathematical discoveries.

Every batch is built before its separate commit. Generated Lean certificate
code supplies the requested code volume; line counts exclude blank lines,
comments, reports, generated axiom-printing commands, and inherited code.
The exact counts and final verification status are recorded in
[verification.json](verification.json). Commit and publication evidence is
recorded in [delivery.json](delivery.json).

The final targeted audit passed: **21,672 new Lean code lines**
(21,094 in certificate batches), **6,846 audited public theorems**,
**59,194 counted independent Python checks**, and four rejected false
certificates. There are 35,823 physical Lean lines; generated audit commands are
excluded. The aggregate build comprises 193 jobs. Of the audited theorems,
3,357 use no axioms; all others use only the three standard logical axioms below.

Validation includes:

- Ordinary Lean kernel checking of the aggregate and every imported dependency.
- Transitive axiom footprints for every newly added public theorem, allowing
  only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
- A comment-aware source scan rejecting proof escapes.
- Independent direct-orbit Python tests, exact gap checks, large integer rays,
  deterministic random interval tests, and boundary cases.
- Four intentionally false Lean claims, which must be rejected for falsehood.

The targeted audit does not rebuild the entire historical repository or the
separate Mathlib extension. External literature claims are context; their full
analytic proofs are not newly formalized by this patch.

## Reproduce

From the repository root, using the pinned Lean version and Python 3:

```sh
python3 scripts/coefficient_descent.py --check
python3 scripts/test_coefficient_descent.py
python3 scripts/audit_coefficient_descent.py
```

Regenerate the atlas with `python3 scripts/coefficient_descent.py`. Its optional
`--commit` mode builds each changed batch before staging and committing only
that batch file. It does not push or modify the GitHub default branch.
