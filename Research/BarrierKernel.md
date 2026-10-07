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
