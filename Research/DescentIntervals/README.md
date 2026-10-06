# Exact first-descent intervals — investigation of 6 October 2026

This investigation adds an executable, sound and complete interval classifier
for exact Collatz stopping times. It also formalizes interval refinement,
finite membership conservation, a cycle-candidate classifier, and the exact
remaining universal-descent obligation. **It does not prove Collatz.**

The starting revision is `ca585a9b42633d89aaee7ba93be2c7cb105feb4b`.
All reported additions and commits are measured against that revision, not
against the much smaller default branch or the repository's historical total.

## Established results and their limits

The following are literature context, not claims newly proved by this patch.
Sources were checked on 6 October 2026.

| Result | What it establishes | What remains |
| --- | --- | --- |
| Terras (1976), independently Everett (1977) | The integers with some iterate smaller than their starting value have natural density one. | A density-zero exceptional set could remain; descent is not the same as reaching one. |
| Krasikov–Lagarias (2003) | Computer-assisted difference inequalities give at least x^0.84 starting integers below x that reach one, for sufficiently large x. | This lower bound does not count every integer. |
| Tao (2019; journal publication 2022) | For every function f(N) tending to infinity, the orbit minimum is at most f(N) for logarithmically almost every N. | This gives neither convergence to one nor a uniform constant bound for every orbit. |
| Hercher (2023, corrected 2026) | The published cycle result requires at least 92 local minima in any nontrivial cycle. | The parameter counts local minima, not the total number of accelerated steps; this does not eliminate all cycles. |
| Barina's verification project | The 2025 milestone verified all starts below 2^71. The project page consulted here reports all starts below 2075 × 2^60. | This is a computational finite range, not a proof for all starts or this repository's Lean-verified range. |

Primary sources:

- [Terras, A stopping time problem on the positive integers](https://eudml.org/doc/205476).
- [Everett, Iteration of the number-theoretic function](https://www.sciencedirect.com/science/article/pii/0001870877900871).
- [Krasikov–Lagarias, Bounds for the 3x+1 Problem using Difference Inequalities](https://arxiv.org/abs/math/0205002).
- [Tao, Almost all orbits of the Collatz map attain almost bounded values, revision 7](https://arxiv.org/abs/1909.03562v7).
- [Hercher's published article](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html) and its [June 2026 corrigendum](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/corrigendum.pdf), which repairs a step in Theorem 21.
- [Barina's live project page](https://pcbarina.fit.vut.cz/) and [2025 publication](https://doi.org/10.1007/s11227-025-07337-0).

No historical priority is claimed for the elementary affine, interval, or
cycle arguments below. The contribution here is the checked integration and
its exact executable certificates within this repository.

## Mathematical development

Use the accelerated map T(n) = n/2 on even inputs and (3n+1)/2 on odd inputs.
It is not the odd-only Syracuse map. Write a starting integer as

    n = 2^k m + r.

The repository's congruence theorem gives, for every j ≤ k,

    T^j(n) = C_j m + b_j,
    C_j = 3^(oddCount r j) 2^(k-j),   b_j = T^j(r).

Exact first descent at k requires every earlier value to be at least n and
the endpoint to be strictly smaller. Thus the full solution set is the
intersection of k prefix affine inequalities and one strict endpoint
inequality. The earlier `FirstDescentClassInterval` theorem proved convexity
of this set. The new classifier computes its sharp boundaries and proves
that they describe every index, including zero and all failures.

### Exact arithmetic solver

For A m+b ≤ C m+d:

- If A≤C and b≤d, every natural index succeeds.
- If A=C and b>d, none succeeds.
- If A<C and b>d, success is exactly m≥(b-d-1)/(C-A)+1.
- If A>C and b≤d, success is exactly m<(d-b)/(A-C)+1.
- If A>C and b>d, none succeeds.

All quotients are natural-number division. Strict endpoint descent is
encoded by adding one to the left constant. Intersections take the maximum
lower bound and the minimum finite upper bound. `none` denotes an infinite
upper bound; inconsistent endpoints denote an empty interval.

`exactInterval_spec` proves, without a convergence assumption,

    (exactInterval k r).Contains m ↔ stoppingTime (2^k*m+r) k.

`canonical_exact_iff` substitutes r=n mod 2^k and m=n/2^k. The classifier also
agrees with the separate orbit-based first-descent Boolean checker.

### Refinement and conservation

For scale s>0 and digit q, refining the class index to s*m+q transports each
boundary t by

    C(t,s,q) = 0 if t≤q, otherwise (t-q-1)/s+1.

Both lower-inclusive and upper-exclusive boundaries obey this same map.
`pullback_spec` proves exact membership transport. `pullback_composition`
proves that two refinements equal the fused refinement at the data level.
For a finite interval [l,u), `refinedMass_conserved` proves that the sum of
child interval sizes over all digits 0≤q<s is exactly u-l, with natural
subtraction handling an empty parent. This is a conservation law: changing
resolution redistributes successful indices without creating new successes
for the same specified stopping time.

### Universal descent

`Covers` says that every n>1 belongs to its canonical exact interval at some
input-dependent depth. `coverage_iff_collatz` proves that this is equivalent
to the Collatz conjecture. Strong induction supplies the forward direction;
a convergent orbit supplies a first descent for the reverse direction.

`finite_depth_incomplete` and `finite_menu_incomplete` prove that no fixed
maximum depth or finite menu of depths establishes coverage. They reuse the
existing all-odd-prefix construction. The missing step is an **unbounded,
input-dependent coverage proof**, not another fixed-depth census.

### Cycle candidates

`periodicInterval` intersects the two affine inequalities that express
T^k(n)=n. At positive depth the slopes 3^a and 2^k are unequal, so
`periodic_index_unique` proves at most one periodic candidate in each dyadic
class. For a contracting slope the exact condition is

    b ≥ r and (2^k-3^a)m = b-r.

The gap must divide b-r. These are exact periodicity statements, not claims
that a candidate has least period k or that all nontrivial cycles are absent.

## Certificates and experiments

The generated atlas exhausts all 1,022 canonical pairs (k,r) with 1≤k≤9 and
0≤r<2^k. It has 100 batches, each covering 10 or 11 distinct classes. Every
class has four theorems: computed interval, infinite-index classification,
base arithmetic, and symbolic endpoint. There are 4,088 generated theorems.
Each batch is compiled before its own commit. Batches are separate reviewable
certificate units, not separate conceptual discoveries.

The generated Lean files contain 19,918 physical lines, including 11,542
nonblank, noncomment code lines. The general proofs, examples, test scripts,
and audit code are additional. This meets the requested 10,000-line minimum
without counting report data, blank lines, or historical source code.

The separate Python census examines all 131,070 canonical classes at depths
1–16. It found only empty sets and unbounded tails; it found no finite
nonempty exact-time interval. That is a finite observation. Whether this
holds at every depth is left as a question; the implementation does not
assume it. No literature-level novelty is claimed for this question.

The direct Python orbit oracle is separate from the affine classifier. Tests
include large integer indices, noncanonical representatives, exact boundary
points, refinement composition and conservation, cycle candidates, and
finite-depth obstructions. Lean also checks infinite families with exact
first-descent times 59 and 65. Three deliberately false Lean certificates
are required to fail, so acceptance is not merely a smoke test.

## Verification result

The new aggregate and its 130 build jobs passed. All 4,153 public theorems
passed the transitive axiom audit: 2,053 use no axioms, and the remaining
footprints contain only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. The source scan found no proof escapes. All three intentionally
false certificates were rejected for falsehood.

All 16 Python test methods passed, comprising 119,634 counted individual
checks plus zero-depth, invalid-input, and census-completeness regressions.
The added development has 20,676 physical Lean lines and 12,101 nonblank,
noncomment Lean code lines, excluding the generated audit commands.
The 100 certificate batches were individually checked before being committed.

## Files and reproduction

- [Arithmetic](../../Collatz/Research/DescentIntervals/Arithmetic.lean): complete affine inequality solver.
- [Classifier](../../Collatz/Research/DescentIntervals/Classifier.lean): exact stopping-time specification.
- [Refinement](../../Collatz/Research/DescentIntervals/Refinement.lean) and [Mass](../../Collatz/Research/DescentIntervals/Mass.lean): boundary transport and conservation.
- [Universal](../../Collatz/Research/DescentIntervals/Universal.lean): the remaining global obligation and finite-depth obstruction.
- [Cycles](../../Collatz/Research/DescentIntervals/Cycles.lean) and [Examples](../../Collatz/Research/DescentIntervals/Examples.lean): periodicity and boundary regressions.
- [manifest.json](manifest.json): every certificate row and batch source hash.
- [python-tests.json](python-tests.json): independent test results and counts.
- [census.json](census.json): finite experimental population data.
- [verification.json](verification.json): aggregate build, all-theorem axiom audit, source hashes, and negative controls.

From the repository root:

```sh
python3 scripts/descent_intervals.py --check
python3 scripts/test_descent_intervals.py
python3 scripts/probe_descent_intervals.py
python3 scripts/audit_descent_intervals.py
```

Regenerate the atlas with `python3 scripts/descent_intervals.py`.
The optional `--commit` flag checks and commits each changed batch, staging
only its explicitly named file. It never pushes or changes the GitHub default
branch. The pinned Lean toolchain and standard Python library suffice.

The targeted verification command builds the new aggregate and all its
imports. It does not certify the repository's separate Mathlib extension or
rebuild every historical target. Verification status is recorded in the
machine-readable report rather than inferred from the presence of source.
