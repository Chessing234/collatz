# Exact thresholds and an independently checked residue atlas

This work does not prove the Collatz conjecture. Universal eventual descent
is already equivalent to Collatz in `CycleDescentBridge`; a fixed universal
horizon is already ruled out in `UniformCovering`. The new contributions here
are an explicit least-index threshold API, a reproducible collection of
concrete infinite-class certificates, and tests of several descent techniques.
No claim of priority or novelty in the mathematical literature is made.

## Literature boundaries

* Riho Terras, [A stopping time problem on the positive integers (1976)](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers).
  Finite stopping time holds on a set of natural density one. This does not
  give descent for every integer. The affine congruence engine used here
  belongs to the parity-vector approach developed in this literature.
* Krasikov and Lagarias, [Bounds for the 3x+1 problem using difference inequalities](https://arxiv.org/abs/math/0205002).
  Their computer-assisted inequalities prove at least x^0.84 integers below
  x eventually reach 1, for sufficiently large x. This is a different kind
  of result from a finite-horizon residue census.
* Terence Tao, [Almost all orbits of the Collatz map attain almost bounded values](https://arxiv.org/abs/1909.03562), published in 2022.
  For every function f tending to infinity, the orbit minimum is at most
  f(n) for logarithmic-density-almost-all n. The exceptional set cannot be
  discarded to obtain universal descent.
* David Barina's [verification project](https://pcbarina.fit.vutbr.cz/) reports
  verification below 2075 × 2^60 when consulted on 2026-10-05. This is an
  external computational report, not a theorem imported into this Lean atlas.

These major literature theorems are described and sourced, not newly
formalized in this work. All new formal claims listed below are elementary
consequences of the existing congruence engine or kernel computations.

## Exact threshold insight

Write M = 2^k, A = 3^a(r,k), B = T^k(r). The existing engine proves

    T^k(M m + r) = A m + B.

For A < M, set g = M - A. Then strict descent is equivalent to

    B < g m + r.

Its least successful natural index is exactly

    0                         if B < r,
    floor((B-r)/g) + 1        otherwise.

`Core.lean` proves the inequality equivalence and upward closure.
`Threshold.lean` proves the exact cutoff, success at the cutoff, and failure
at every smaller index. Unlike a crude sufficient threshold, this also
certifies the complete finite exceptional part of a contracting class.

For k=8, r=7 the coefficient is 243, modulus 256, and endpoint 8. Thus
T^8(256m+7) < 256m+7 holds exactly when m≥1. The coefficient test passes
at 7, yet 7 itself fails descent at this horizon. This exposes why dropping
the affine offset in a proposed universal descent argument is invalid.

## Other techniques and limits

`Obstructions.lean` proves that no natural-valued nondecreasing potential can
strictly decrease at every accelerated step for every n>1: T(3)=5. It derives
failures for nonnegative affine potentials and natural power potentials.
This does not exclude parity-dependent, nonmonotone, or variable-block
potentials, which remain legitimate directions.

A kernel census gives the complete contracting representative exceptions:

* Depth 8: [0,1,2,7,9,18,19,25].
* Depth 10: [0,1,2].

The census concerns the endpoint at exactly k steps; it does not measure
whether some earlier step descends. Those two properties must not be conflated.
The Python report separately counts classes with no contracting prefix.
At depth 18, 7,495 of 262,144 residues have no contracting prefix.
This finite observation does not establish any limiting density.

`surviving_class` proves that every member 16384m+16383 fails to descend at
step 14. This is a horizon-specific obstruction; it does not imply those
numbers never descend. The atlas leaves many other classes unlisted too.

## Atlas scope and validation

There are 300 batches of eight distinct odd residues modulo 16384. Each
contains three proofs per residue: exact numerical data, an affine orbit
identity for every class index, and strict descent for every index including
zero. Therefore 2,400 disjoint infinite arithmetic progressions are certified.
The 48,300 batch-source lines are generated proof data. They are not 48,300
lines of independently novel mathematics. The small handwritten core carries
the general reasoning. Batch commits correspond to eight checked classes each.

Python independently checks the affine formulas and descent at indices
0,1,2,17,1024,10^12, for 14,400 substitutions. It also tests actual descent
for all starts 2 through 100,000 using a fuel cap of 1,000 accelerated steps.
All pass; the maximal first-descent time is 135, attained at witness 35,655.
Python assertions are empirical checks, not Lean proofs about that interval.

Every numerical Lean certificate uses `decide`, not `native_decide`.
The new source introduces no axioms and contains no `sorry` or `admit`.
The axiom audit records ordinary Lean foundational dependencies, separately
from proof-hole or native-evaluation axioms. Source hashes bind the audit to
the exact files. No unrelated pre-existing workspace edits are committed.

## Reproduction

    python3 scripts/descent_atlas.py --verify
    lake build Collatz.Research.DescentAtlas.All
    lake env lean scripts/audit_descent_atlas.lean

Generation without `--verify` performs the independent Python probes and
recreates batch sources and their hashes. `--commit` verifies each batch before
committing it; use that only when intentionally creating a fresh commit series.
`All.lean` is the explicit atlas entry point and does not require editing the
pre-existing root module. The whole pre-existing project is outside this
validation scope; the atlas and its imported dependency chain are checked.
