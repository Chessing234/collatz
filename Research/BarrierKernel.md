# Anchored barrier investigation — 2026-10-07

The new module `Collatz/Exploration/BarrierKernel.lean` formalizes fixed-barrier
survival, an exact finite-window checker, and cycle extraction. It does not
prove Collatz or claim a new result in the published mathematical literature.
The investigation remains open.

## Mathematical findings

Write `C` for the ordinary map, including its totalization `C(0)=0`.
For a fixed barrier `b`, define

`Survives(b,K,n) := ∀ k≤K, b≤C^k(n)`.

The exact splitting law is

`Survives(b,j+K,n) ↔ Survives(b,j,n) ∧ Survives(b,K,C^j(n))`.

Keeping the same barrier matters. The condition `Survives(n,K,n)` cannot
be treated as forward invariant: `3→10→5` passes the one-step test at 3
and fails the one-step test at 10. The fixed-barrier test at 3 survives
that shift. This rules out an invalid inference from local survivors
to a trapping set; it does not rule out counterexamples to Collatz.

The intersection over all budgets is

`Kernel(b,n) := ∀ k, b≤C^k(n)`.

It is the greatest forward invariant subset of the naturals at least `b`.
For a positive start, membership in `Kernel(2)` is exactly nonconvergence.
Thus proving this kernel empty would still require solving Collatz. Recasting
the question as invariant-set elimination supplies no missing proof by itself.
The attained floor construction in `OrbitFloor.lean` is the diagonal
condition `m>1 ∧ Kernel(m,m)`.

An inclusive prefix confined to `[b,u]` through time `u-b+1` contains
`u-b+2` points among `u-b+1` values. Subtracting `b` and using the project's
pigeonhole theorem yields indices `i<j≤u-b+1` such that

`C^(j-i)(C^i(n)) = C^i(n)` and `b≤C^i(n)`.

This is a closed orbit with positive period. It uses only the finite prefix;
an assumption about future boundedness is unnecessary. The bound is sharp
for arbitrary deterministic maps on an interval; no optimality claim for
the specific Collatz map is made. The recursive Boolean checker is proved
equivalent to every sampled point lying in the interval. Its successful
computation at the stated budget therefore supplies a Lean cycle witness.

## Evidence and limitations

Run `python3 scripts/audit_barrier_kernel.py`. It builds the module, tests
62,208 split windows and 3,456 interval prefixes (68 accepted), audits all
21 theorem axiom footprints, and requires Lean to reject two false interval
certificates. Only `propext`, `Quot.sound`, and `Classical.choice` are permitted
in theorem footprints. The module adds no assumptions about Collatz.

Negative controls include moving the barrier, using too short a prefix, and
the nontrivial ordinary `5n+1` cycle starting at 13. The last control is a
Python experiment on a different map, not a Lean theorem about Collatz.
Independent finite tests are corroboration; the universal results are the
Lean proofs. These reductions are elementary dynamical facts, not established
frontier discoveries. No proportion of code is certified mathematically novel.

## Notable published results checked for context

- Terras and Everett established natural-density-one finite stopping time;
  [Lagarias's survey discussion](https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/node4.html)
  explains the coefficient/actual-stopping distinction. Density one leaves
  a possible exceptional set.
- [Tao's almost-bounded-orbits theorem](https://arxiv.org/abs/1909.03562)
  gives logarithmic-density-one descent below any prescribed function tending
  to infinity. It does not eliminate every positive nonconvergent input.
- [Krasikov and Lagarias](https://arxiv.org/abs/math/0205002) used difference
  inequalities and computer-aided proof to obtain the exponent 0.84 in a
  lower bound for how many starting integers reach 1.
- [Barina's 2025 verification paper](https://d-nb.info/1370796994/34)
  reports verification below `2^71`. This is a published computational bound,
  not a statement about the latest live frontier or a Lean-imported axiom.
- [Lagarias's overview](https://arxiv.org/abs/2111.02635) surveys mathematical
  approaches as of 2010; its arXiv upload in 2021 does not make it a 2021
  account of the state of the art.

These references provide context, not newly verified formalizations of their
complete proofs. Prior repository notes contain further literature and
technique-specific obligations.

## Next research obligations

The bounded-prefix certificate handles a cycle alternative only after a
range certificate is available. An unbounded failed orbit is not excluded.
Candidate advances must supply additional Collatz-specific information:
effective barriers coupled to valuation budgets, sound pruning of modular
classes across shifted windows, or a valid global ranking argument. Each
candidate needs both a proof and countermodel tests before it is promoted
from an experiment. Merely increasing a fixed horizon cannot empty the
all-horizon kernel. The passage atlas separately formalizes the remaining
unbounded descent obligation.

The baseline has 1,606,846 tracked Lean lines across 5,758 files and 3,651
commits before this addition. History contains 1,000 passage certificate
batch commits. These exceed the requested numerical thresholds in the
existing project, but generated certificates and audit commands must not
be counted as independent discoveries. The 50% novelty requirement is not
established, and "all possible techniques" has no finite exhaustive audit.

## Collatz-specific interval capacities

The follow-up modules `IntervalCapacity.lean` and `TwoStepCapacity.lean`
replace the raw interval width with the exact number of sources that
survive one or two transitions. These are additional proved structural
findings. Mathematical priority or frontier novelty is not established.

For positive `b`, one-step sources split into two disjoint bands:

- Even sources `2q` with `b≤q≤⌊u/2⌋`.
- Odd sources `2q+1` with `⌊b/2⌋≤q<⌊(u+2)/6⌋`.

Let `E=max(⌊u/2⌋+1-b,0)` and
`O=max(⌊(u+2)/6⌋-⌊b/2⌋,0)`. The exact one-step capacity is `M₁=E+O`.
Lean proves an explicit bijection between viable states and integers
`0≤r<M₁`, including empty bands and reversed intervals. A prefix confined
to `[b,u]` through time `M₁+1` yields a repeated state by time `M₁`.
The extra endpoint checks the successor of the final source. It cannot
simply be omitted: in `[1,2]`, `M₁=1` and the prefix `2→1` has no repetition.

Above `u≥3b+1`, the exact rounding correction is

`6M₁ + 9b + 3(u mod 2) + ((u+2) mod 6) = 4u + 8 + 3(b mod 2)`.

Below that threshold, `u≤3b`, every viable source is even. Three consecutive
orbit points cannot all lie in `[b,u]`: two viable even sources would force
the first point to be at least `4b`, contradicting the cap. Lean proves
`intervalCheck b u 2 n = false` for all `b>0`, `u≤3b`, and `n`.

Two-step sources split into three disjoint families:

- `4q` with `b≤q≤⌊u/4⌋`.
- `4q+2` with `⌊b/2⌋≤q<⌊(u+2)/6⌋`.
- `2q+1` with the same bounds as the preceding family.

The equal sizes of the latter two families follow from the forced halving
after odd expansion. If an odd source and its expansion are in the
interval, the next halved value is at least the source and no greater
than the expansion. The exact two-step capacity is therefore

`M₂=max(⌊u/4⌋+1-b,0)+2O`.

Lean proves the compact bijection, `M₂≤M₁`, and cycle extraction from
an interval prefix through time `M₂+2`, with repetition by time `M₂`.
For `[100,1000]`, the raw budget is 901, the one-step budget 519, and
the two-step budget 387. These are sample-budget reductions; no runtime
benchmark or asymptotic improvement is claimed.

Run `python3 scripts/audit_interval_capacity.py`. Independent direct-map
enumeration checks both exact bijections on 12,080 intervals, including
174,725 one-step and 98,403 two-step viable states. It checks 3,675
remainder identities and 5,065 accepted cycle prefixes for each budget.
The audit inspects every named theorem's axiom footprint and requires
Lean to reject four false formulas/certificates. The earlier barrier
audit is rerun to verify the shared audit helper. CI runs both audits.

The obstruction remains an unbounded orbit or an unknown large cycle.
These capacities do not provide a global upper bound on a failed orbit,
and no finite interval census eliminates all intervals. A promising next
experiment is to study higher-step capacity with a sound symbolic-interval
enumerator, measuring whether the additional pruning justifies its cost.
Any claim that the capacity eventually vanishes requires a new argument;
the exact formulas above do not imply it.
