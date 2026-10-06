# Stopping atlas and the 1538-step crossing certificate

This addition extends the repository's checked first-coefficient-crossing
horizon from 1024 to **1538**, classifies every binary residue class at depths
10–13, and proves finite first-event counting identities with a sharper error
bound. **It does not prove the Collatz conjecture.** The results are additions
to this repository; no claim of priority over the mathematical literature is made.

## Conventions and exact statements

We use the accelerated map `T(n) = n/2` for even `n` and `(3n+1)/2` for odd
`n`. Let `a(n,k)` count odd steps among the first `k` iterates. A first
coefficient crossing at `k` means

```
3^a(n,k) < 2^k
and, for every j < k, 2^j ≤ 3^a(n,j).
```

This concerns the coefficient of the affine iterate. The positive additive
term makes descent of the actual integer a separate proof obligation.

- **Horizon:** for every `n > 1`, if its first coefficient crossing occurs at
  `k ≤ 1538`, then `T^k(n) < n`. There is no bound here on when a crossing must
  occur. `Horizon.lean` also identifies coefficient crossing with exact first
  descent throughout this horizon.
- **Interval shape:** for every depth `k ≤ 1538` and every representative `r`,
  the indices `m ≥ 0` for which `2^k*m+r` first descends at time `k` form an
  empty set or an upward tail. The theorem is first proved for an arbitrary
  certified horizon. A bounded nonempty interval must lie beyond that horizon.
- **Counting conservation:** at every finite cutoff `[2,N+2)`, the sum of
  coefficient first-event counts through time `H` and the surviving count
  equals `N`. This coefficient identity is unconditional. Its interpretation
  as actual first descent requires the explicit `ExactThrough H` hypothesis.
- **Periodic discrepancy:** if a Boolean predicate has positive period `M`
  with `A` successes per period and `C(N)` successes before `N`, then
  `|M*C(N) - N*A| ≤ A*(M-A)`. Lean states this as two natural-number
  inequalities. It improves the older `M*M` bound and specializes to exact
  coefficient-crossing counts. This is an elementary counting estimate.
- **Forbidden times:** a first coefficient crossing at `k+1` must finish
  with an even step and requires a power of three in `[2^k,2^(k+1))`.
  In particular, no input has exact accelerated stopping time 11. This
  explains the empty depth-eleven census independently of its enumeration.

The horizon extension reuses the existing checked exceptional inputs
`2 ≤ n < 99730`, whose coefficient crossings give descent by time 135.
A new integer gap certificate covers the additional lengths. The same
uniform bound fails at `(k,a) = (1539,971)`, where it would require threshold
`330588`. **This is failure of that bound, not an orbit counterexample.**
It suggests either enlarging the checked exceptional range or strengthening
the additive-term estimate.

## Exhaustive finite census with infinite-class conclusions

Each canonical pair `(k,r)`, `10 ≤ k ≤ 13`, `0 ≤ r < 2^k`, occurs exactly
once. Four theorems per pair certify the computed interval, its equivalence
to exact stopping for every natural index, base parity/endpoint data, and the
symbolic affine endpoint for every index.

| Depth | Residue classes | Empty | Infinite tails | Bounded nonempty |
|---|---:|---:|---:|---:|
| 10 | 1024 | 1012 | 12 | 0 |
| 11 | 2048 | 2048 | 0 | 0 |
| 12 | 4096 | 4066 | 30 | 0 |
| 13 | 8192 | 8107 | 85 | 0 |
| Total | 15360 | 15233 | 127 | 0 |

The period numerators 12, 0, 30, and 85 are separately kernel-checked in
`Census.lean`. At depth 13 the discrepancy bound specializes to
`|8192*C(N) - 85*N| ≤ 689095`.

An empty class has no **first descent at this particular time**. It may have
descended earlier or descend later. The four census depths do not constitute
a covering argument for universal convergence.

## Universal descent and the remaining quantifiers

The existing [universal-descent bridge](../../Collatz/Research/CoefficientDescent/Universal.lean)
separates two obligations:

1. Every `n > 1` has a first coefficient crossing at some finite time.
2. Every such crossing produces actual descent, without a fixed time bound.

Together these imply universal descent, and strong induction then proves
Collatz. The present horizon extends a finite part of the second obligation.
It establishes neither obligation without qualification. Almost-everywhere
statements and larger finite tables do not eliminate every possible exception.

## Techniques considered and boundaries

“All possible techniques” is an open-ended research aspiration, not a
finite deliverable that can honestly be exhausted. The investigation connects
the following concrete routes; it does not claim to have tried every variant.

| Technique | Work available in this repository | Remaining obstacle |
|---|---|---|
| Universal descent / well-founded induction | Explicit convergence equivalence and crossing bridge | Produce a descent witness for every positive input greater than one |
| Affine parity words / modular classes | Exact intervals, symbolic iterates, exhaustive new depth 10–13 census | Unbounded coverage of realizable paths |
| First passage / coefficient gaps | Conditional crossing horizon 1538; checked failure threshold at 1539 | Control crossings for arbitrarily long paths |
| Finite counting / periodicity | Exact partition, quotient–remainder counts, composition-sensitive discrepancy | Density estimates leave possible exceptional inputs |
| Probabilistic and moment bounds | Existing `ParityMoments` and natural-density modules | Deterministic control of all exceptional trajectories |
| Inverse trees / difference inequalities | Existing inverse-interval decisions and tree certificates | Establish full coverage, beyond a lower bound on convergent inputs |
| Cycle arithmetic / Diophantine gaps | Existing cycle and frontier certificates | Exclude every nontrivial cycle and all divergent trajectories |
| Lyapunov functions / potentials | Existing `BlockPotential` and obstruction modules | Construct a globally applicable decreasing quantity |
| 2-adic / symbolic dynamics | Parity periodicity and congruence interfaces | Distinguish positive-integer trajectories from unrestricted symbolic paths |
| Automated search / proof certificates | Deterministic generator, independent tests, kernel proofs, negative controls | Search success on bounded domains is not a termination proof |

These routes differ in scope. Existing paper-statement modules are not
silently counted as proofs of their cited papers. The separate Mathlib
extension is outside this addition's verification target.

## Notable external results and attribution

Sources were checked on 2026-10-06. These are literature results, not results
newly proved by this addition.

- **Terras / Everett:** almost every starting integer has finite stopping
  time in natural density. Parity classes and coefficient stopping time
  underlie this result. Lagarias's [survey exposition](https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/node4.html)
  also describes the finite difference between exact coefficient and actual
  stopping sets at a fixed time.
- **Korec:** for every exponent greater than `log(3)/log(4)`, almost every
  orbit reaches below the corresponding power of its starting value, in
  natural density. This earlier theorem is described in
  [Tao's paper](https://arxiv.org/abs/1909.03562v7).
- **Tao (2022):** for every function tending to infinity, almost every orbit
  reaches a value below that function of its starting point, in logarithmic
  density. The [paper](https://arxiv.org/abs/1909.03562v7) uses first-passage
  transport and estimates on a 3-adic random walk. It does not prove that
  every orbit reaches one; its almost-all quantifier cannot be dropped.
- **Krasikov–Lagarias (2003):** difference inequalities give a computer-assisted
  lower bound of order `x^0.84` on the number of inputs up to `x` whose orbits
  reach one. See the [authors' paper](https://arxiv.org/abs/math/0205002).
- **Hercher (2023):** any nontrivial cycle must have at least 92 local minima.
  Use the [published article](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html)
  together with its [June 2026 corrigendum](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/corrigendum.pdf),
  which repairs an inequality argument. This addresses cycles rather than
  the possible existence of divergent nonperiodic orbits.
- **Barina's verification project:** the [project status](https://pcbarina.fit.vut.cz/)
  reported all starts below `2075 × 2^60` checked at access time; its log
  dates the `2^71` milestone to 2025-01-15. These external computations are
  not imported as Lean axioms or presented as kernel-checked by this project.

## Reproduction and audit

From the repository root:

```sh
python3 scripts/stopping_atlas.py --check
lake build Collatz.Research.StoppingAtlas.All
python3 scripts/test_stopping_atlas.py
python3 scripts/audit_stopping_atlas.py
bash scripts/check_integrity.sh
# In a full checkout containing the batch history:
python3 scripts/check_stopping_atlas_history.py
```

`manifest.json` records all classes, batch boundaries and source hashes.
`verification.json` records comment-stripped Lean code lines, the axiom
footprint of every new named theorem, independent test totals, and rejected
false controls. The audit excludes its own generated `#print axioms` driver
from code-line accounting. `batch-receipts.json` records each individually
checked batch's source hash and original commit. Exact historical commits
are retained by a merge commit rather than squashing.

The 1000 batches each cover disjoint classes and were built before their
individual commits. This meets the requested commit/line scale using useful
proof-carrying data. It is **not 1000 independent discoveries**, and the
176,000-plus Lean code lines are predominantly generated certificates.
The baseline is `a4bb6ce3d4163f091e7951d976d7073086c94ef1`; all these files
and batch commits are additions after that baseline.
