# First passage through 2,592 steps and the depth-fifteen atlas

This development enlarges the repository's certified first-crossing horizon
from 1,538 to **2,592** and classifies all **32,768** dyadic residue classes at
depth fifteen. It also formalizes deterministic timing constraints and exact
finite-window counts. **The Collatz conjecture remains unproved.** These are
new repository developments; no historical mathematical priority is claimed.

## Mathematical statements

Use the accelerated map `T(n)=n/2` for even `n` and `(3n+1)/2` for odd `n`.
Let `a(n,k)` count odd steps among the first `k` iterates. A first coefficient
crossing at `k` means `3^a(n,k)<2^k`, with the reverse weak inequality at
every earlier index.

1. **Conditional descent for unbounded inputs.** For every `n>1`, a first
   coefficient crossing at `k≤2592` implies `T^k(n)<n`. The theorem does not
   assert that every input has such a crossing. Coefficient first crossing
   and actual first descent agree throughout this horizon.
2. **Exceptional range.** Every integer `2≤n<330588` has first-crossing
   descent by step 164. The input 270271 attains step 164. The old checked
   range is reused, and 113 new interval blocks verify the additional inputs.
3. **Interval shape.** At any depth `k≤2592`, every representative's exact
   stopping indices are either empty or an upward tail. Thus any bounded
   nonempty interval must occur later than the new horizon.
4. **Deterministic timing.** A first crossing at `k+1` has a unique possible
   odd-step count because the band `[2^k,2^(k+1))` contains at most one power
   of three. Conversely, equal odd counts at first crossing imply equal
   crossing times. Conversely, every occupied band is realized as a first
   crossing by arbitrarily large positive integers: a word of initial ones
   followed by zeros supplies the construction. This completely classifies
   possible coefficient first-crossing times at unbounded depths. The same
   characterization holds for actual stopping through 2592. Existence at
   each feasible time is distinct from existence for every starting integer.
5. **Forbidden time.** No natural input has exact accelerated stopping time
   fourteen. The coefficient exclusion is unconditional in the starting
   value; the actual-stopping exclusion uses the certified crossing bridge.
6. **Complete depth-fifteen census.** Exactly 173 classes have first descent
   at fifteen; the other 32,595 classes do not have first descent at fifteen.
   Each of the 173 successful canonical classes contains every natural
   index `m`, with input `32768*m+r`; every such path has nine odd steps.
   Earlier or later stopping remains possible in the other classes.
7. **Counts at every cutoff.** If `C(N)` counts exact first descent at fifteen
   in `[2,N+2)`, then

   ```
   |32768*C(N) - 173*N| ≤ 5638935.
   ```

   Lean states the absolute-value estimate as two natural-number
   inequalities and proves a quotient–remainder decomposition. The numerator
   is checked in a separate counting computation, in addition to the class
   certificates. Dividing the error by `32768*N` shows the exact-time
   density `173/32768`; Lean also derives this rational natural-density statement using
   arbitrarily fine integer precision, and proves exact counts on all
   complete periods.

`Horizon.lean`, `Timing.lean`, `FeasibleTimes.lean`, `Counting.lean` and
`Census.lean` contain these
endpoints. Each generated class has four further theorems: interval bounds,
exact stopping classification for every index, base arithmetic, and the
symbolic affine iterate for every index. The Python generator supplies
candidates; ordinary Lean kernel checking establishes their truth.

## Progress toward a solution

The purpose is to close universal descent, rather than maximize certificate
volume. `SolutionBridge.lean` proves that the original Collatz conjecture is
**equivalent** to the following remaining target:

```
For every n>1 with no coefficient first crossing by 2592,
there is an input-dependent k>2592 with T^k(n)<n.
```

This is `ResidualCoverage`; it is a definition of the open obligation, not a
proved assertion that it holds. An explicitly stated stronger arithmetic
condition, `ResidualGapCoverage`, would supply a first crossing with

```
a(n,k)*3^a(n,k) < 3*(2^k-3^a(n,k))*n.
```

The file proves that this condition would solve Collatz without any fixed
bound on `k`. It also extracts a surviving never-descending witness from a
hypothetical failure of Collatz, and proves that **every certified finite
crossing window leaves an input uncovered**. Consequently, increasing a
fixed horizon or exhausting a finite atlas can never be the entire closing
argument. The concrete mathematical advance here is the larger certified
part of the crossing-to-descent law and the explicit residual research target;
the two universal residual propositions remain open.

## The next arithmetic obstruction

The inherited gap checker needs

```
a*3^a < 3*(2^k-3^a)*N
```

for every light pair. The largest required threshold through 2592 is 330588,
attained at `(k,a)=(1539,971)`. The next record is `(2593,1636)`, requiring
583015. Lean proves both failure at the current threshold and the exact next
threshold. **Failure of this sufficient inequality is not an orbit
counterexample.** Improving the additive correction bound or enlarging the
verified exceptional range are concrete next experiments.

## Notable results and literature status

Primary sources were checked on 2026-10-06. These literature statements are
attributed context, not newly formalized proofs of the cited papers.

- **Terras and Everett:** finite stopping time holds for a set of natural
  density one. [Lagarias's survey](https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/node4.html)
  explains the parity-vector argument and the finite difference between
  coefficient and actual stopping at fixed depth.
- **Korec:** exponents greater than `log(3)/log(4)` give an almost-everywhere
  power bound in natural density. The precise comparison with later work
  is stated in [Tao's paper](https://arxiv.org/abs/1909.03562v7).
- **Tao:** the minimum orbit value is below any prescribed function tending
  to infinity for almost every start in logarithmic density. This does not
  establish convergence for every start. The 2019 preprint was published
  in 2022; version 7 is dated 2026-07-16 and records corrections, including
  the statement of Lemma 7.9. See the [primary record](https://arxiv.org/abs/1909.03562v7).
- **Barina:** the [2025 computational paper](https://d-nb.info/1370796994/34)
  reports verification below `2^71`. This is the published range cited here,
  not a claim that it is the latest live project frontier. No external
  computation is imported into our proofs as a trusted assumption.
- **Hercher:** the [2023 cycle paper](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html)
  states that a nontrivial cycle needs at least 92 local minima. The symbol
  `m` counts local minima, not odd terms. Its [June 2026 corrigendum](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/corrigendum.pdf)
  repairs an inequality in Theorem 21; cite it alongside the original.
- **Rozier and Terracol:** [Paradoxical behavior in Collatz sequences](https://arxiv.org/abs/2502.00948v5),
  published in Discrete Mathematics in 2026, distinguishes later paradoxical
  behavior from the first-stopping conjecture. Version 5 fixes an appendix
  lemma. We do not import its claims as axioms.
- **Withdrawn work:** [arXiv:2605.13886](https://arxiv.org/abs/2605.13886v2)
  was withdrawn on 2026-05-20 to avoid duplication. It is recorded as
  withdrawn and is not used as independent corroboration or a priority claim.

## Techniques and unresolved proof obligations

The requested examination of “all possible techniques” has no finite
exhaustive meaning. The following routes are connected to concrete modules;
the table identifies the missing inference instead of declaring success.

| Route | Formal or experimental material | Remaining obligation |
|---|---|---|
| Strong induction and descent | `CoefficientDescent.Universal` | Produce descent for every `n>1` |
| Affine parity words and modular sieves | New depth-fifteen atlas, `DescentIntervals.Classifier` | Cover realizable paths at unbounded depths |
| First passage and Diophantine gaps | New horizon and next record threshold | Prove crossing existence and unbounded crossing-to-descent transfer |
| Exact combinatorial counting | New numerator and finite error bars | Density one cannot exclude every exceptional input |
| Probability and moments | Existing `ParityMoments`, independent binary-word enumeration | Justify deterministic conclusions on every integer orbit |
| Inverse trees and difference inequalities | Existing tree and inverse-interval certificates | Establish coverage rather than a lower population bound |
| Cycle arithmetic | Existing cycle, S-unit and frontier modules | Exclude all nontrivial cycles; divergence is a separate case |
| Potentials and ranking functions | Existing `BlockPotential`, height obstruction modules | Construct a globally valid decrease witness |
| 2-adic and symbolic dynamics | Existing parity/congruence modules and Mathlib inverse-boundary work | Control positive integer realizability; incompatible completions do not give a contradiction |
| Automated search and certificates | New deterministic generator, independent checks, negative controls | Bounded search does not prove universal termination |

The separate Mathlib package and historical paper-statement modules retain
their own scope. This audit covers the new addition and its imported
proof dependencies. It does not re-prove every cited literature result.

## Reproduce and audit

```sh
python3 scripts/passage_atlas.py --check
lake build Collatz.Research.PassageAtlas.All
python3 scripts/test_passage_atlas.py
python3 scripts/audit_passage_atlas.py
bash scripts/check_integrity.sh
# Full history is needed for commit provenance:
python3 scripts/check_passage_atlas_history.py
```

`manifest.json` records every class and source hash. `verification.json`
records code lines after removing comments and blank lines, an axiom audit of
all named new theorems, independent tests and rejected false certificates.
The audit driver is excluded from line counts. `batch-receipts.json` records
successful per-batch builds and their distinct commits; historical source
hashes and reachability are checked by the history verifier.

The 1,000 certificate commits cover disjoint new classes after baseline
`c96b95946b896306b1252b553781ef270bb3f32d`. The large code volume is predominantly
generated proof-carrying data, not 1,000 independent discoveries. Exact commit
objects are preserved when the PR is merged. All resulting work belongs on
`main`, with the temporary PR branch removed after merging.
