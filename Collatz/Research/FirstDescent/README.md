# Exact first-descent cylinders

This extension proves strict descent on 2,400 infinite odd residue cylinders,
then strengthens each certificate to **exact first descent**: all earlier
accelerated iterates are at least the starting integer. It does not prove
universal descent or the Collatz conjecture. The certificates apply to
`T(n) = n/2` for even n and `(3n+1)/2` for odd n.

## Mathematical development

For a cylinder `n = 2^k m + r`, parity transport gives
`T^k(n) = 3^a m + b`, where `a = oddCount r k` and `b = T^k(r)`.
The endpoint descends for every `m ≥ 0` if `3^a < 2^k` and `b < r`.
Endpoint descent alone does not specify its first occurrence.

`PrefixTransport.lean` supplies the additional criterion. For each `j < k`,
require `2^j ≤ 3^(oddCount r j)` and `r ≤ T^j(r)`. Factor the refined
cylinder as `2^j (2^(k-j) m) + r` and apply the same affine identity.
Both its coefficient and its constant term are non-descending, so its
entire prefix is non-descending. This proves the exact first-descent time
for every member of an infinite class, not just the representative.

`CrossingGaps.lean` also proves that no power of three lies in the relevant
binary crossing intervals at times 3, 6, 9, 11, 14, 17, and 19. This explains
several empty census levels without enumerating residue representatives. It
excludes coefficient first crossings at these times, not later descent.

`first_descent_unique` proves that different exact first-descent times
cannot describe the same start. At equal depths distinct residues are
disjoint by modular arithmetic. The Python probe additionally checks
that no selected binary cylinder is an ancestor of another.

This is a new extension of this repository, using classical parity-word
arithmetic. No historical novelty or solution of an open problem is claimed.

## Results and verification

- 300 batches, 2,400 distinct cylinders, 60,000 generated Lean lines.
- Each batch is kernel checked with `lake env lean` before its own commit.
- 12,012 theorem axiom footprints audited, including 4,800 axiom-free proofs.
- `Exact.lean` upgrades every cylinder to an exact first-descent theorem.
- 14,400 independent affine/descent substitutions, including class indices
  as large as `10^12`, passed.
- 42,185 earlier coefficient/prefix inequalities passed an independent probe.
- The selected disjoint cylinders have density `116407/524288`, about 22.20%
  of all natural integers, or 44.41% relative to odd integers. This is a
  Python-computed rational sum of cylinder densities; the density and
  disjointness census are not analytic Lean theorems.
- Every start from 2 through 500,000 descends within 2,000 accelerated steps
  in the Python experiment. The maximum first-descent time is 173, attained
  by 381,727. This experiment is not a kernel-certified range theorem.
- An independent inverse-tree experiment gives 855 distinct nodes through
  20 inverse steps. Inverse reachability of these nodes does not imply all
  forward orbits enter that tree.

The line count includes generated specialization proofs and documentation;
it is not a count of independent mathematical ideas. All numerical Lean
proofs use kernel `decide`, with no added axioms or native evaluation.

## Literature and alternative approaches

1. [Terras (1976), A stopping time problem on the positive integers](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers)
   develops stopping-time and parity arguments. Density-one finite stopping
   time still permits exceptional integers. Our finite cylinder list cannot
   remove that exceptional-set problem.
2. [Krasikov–Lagarias (2003), Bounds for the 3x+1 Problem using Difference Inequalities](https://arxiv.org/abs/math/0205002)
   gives a computer-assisted lower bound of `x^0.84` for the number of
   integers below x reaching 1, in the large-x regime. Inverse-tree counting
   controls abundance of known predecessors, rather than every orbit.
3. [Tao (2019), Almost all orbits of the Collatz map attain almost bounded values](https://arxiv.org/abs/1909.03562)
   proves orbit minima fall below any function tending to infinity for
   logarithmically almost all starting integers. This does not assert every
   orbit reaches 1. Its abstract also describes Korec's earlier natural-density
   bound for exponents greater than `log(3)/log(4)`.
4. [Simons–de Weger, Theoretical and computational bounds for m-cycles](https://www.deweger.net/papers/%5B35a%5DSidW-3n%2B1-v1.43%5B2007%5D.pdf)
   uses transcendence and computational Diophantine approximation to bound
   hypothetical cycles. Cycle exclusions leave divergent trajectories to
   address; run count m must not be confused with total cycle length.
5. [Lagarias, annotated bibliography 1963–1999](https://arxiv.org/abs/math/0309224)
   provides a broader source map, including stopping-time and cycle methods.

These analytic papers are researched sources, not newly formalized theorems
in this extension. The existing library separately explores ranking
obstructions: a potential monotone in n cannot decrease at every step,
since `T(3) = 5`. Exact first descent avoids the demand for per-step decrease,
but the uncovered cylinders remain an infinite set.

## Reproduction

```sh
python3 scripts/first_descent_atlas.py
python3 scripts/probe_first_descent.py
python3 scripts/certify_exact_first_descent.py
lake build Collatz.Research.FirstDescent.Exact
```

The first command checks all batches and creates commits for changed batches;
unchanged batches are checked again without empty commits. It does not stage
unrelated workspace changes. The other commands reproduce probes and
exact first-descent certification without creating commits.

Read `verification.json`, `experiments.json`, and `audit.log` for the recorded
scope. Universal descent still requires proving that every integer above 1
belongs to a descending class at some finite depth. Neither a large finite
atlas nor a density result supplies that quantifier.
