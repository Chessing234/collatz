# A sharp linear bound from a finite phase certificate

Research date: 2026-09-28. The result is a uniform accumulator bound with an
optimal additive constant. It does not prove universal descent or Collatz.
Historical priority is not established; the literature audit is below.

## The theorem

Let `T(n)` be `n/2` for even `n`, and `(3n+1)/2` for odd `n`. Let `a(n,i)`
count odd inputs in the first `i` steps, and define the integer accumulator by

\[
2^kT^k(n)=3^{a(n,k)}n+C(n,k).
\]

Suppose every proper prefix is coefficient-heavy:

\[
2^i\le 3^{a(n,i)}\qquad(0\le i<k).
\]

Then, writing `a=a(n,k)`, the new formalization proves

\[
\boxed{108C(n,k)\le(27a+11)3^a},
\qquad
C(n,k)\le\left(\frac a4+\frac{11}{108}\right)3^a.
\]

Both `n` and `k` are unbounded. The prefix hypothesis is essential: it
implies no descent before step `k`, and must not be inferred merely from
observing no descent before that step.

The intercept `11/108` is optimal with slope `1/4` fixed. The actual orbit

\[
11\to17\to26\to13\to20\to10
\]

has first coefficient crossing at step five, `a=3`, and `C=23`. Hence it
attains equality: `108*23=(27*3+11)*27`.

## The device

The existing Beatty envelope is

\[
f(i)=\lfloor i\log_2 3\rfloor,\quad B_0=0,\quad
B_{i+1}=3B_i+2^{f(i)}.
\]

Proper-prefix heaviness bounds the time of the `(i+1)`st odd input by `f(i)`.
Consequently `C(n,k) <= B_a`. This positional envelope is prior mathematics.

Instead of bounding every term separately, retain its phase

\[
r_i=\frac{2^{f(i)}}{3^i}\in(1/2,1],\qquad
F(r)=\begin{cases}4r/3&r\le3/4,\\2r/3&r>3/4.\end{cases}
\]

The endpoint convention is `F(3/4)=1`. For every admissible phase, the sum
of twelve consecutive phases is strictly less than nine. The Lean proof
checks twelve intervals using integer linear inequalities. It quantifies
over arbitrary integer numerator and denominator, so it applies again
at every later phase; this is not a check of twelve starting integers.

Independently, exact rational interval calculations give the sharper value

\[
\max_{1/2<r\le1}\sum_{i=0}^{11}F^i(r)
=\frac{2349463}{262144}
=9-\frac{9833}{262144},
\]

attained at `r=177147/262144`. The Lean proof needs only the strict bound
by nine. The exact supremum calculation is separately recorded in the
probe output and is not advertised as a Lean theorem.

The remaining initial prefixes, of lengths zero through eleven, satisfy

\[
\sum_{i<a}r_i-\frac{3a}{4}\le\frac{11}{36},
\]

with equality only at `a=3`. Grouping an arbitrary length into an initial
remainder followed by twelve-term blocks proves

\[
108B_a\le(27a+11)3^a.
\]

Equality occurs precisely at `a=3`; every complete block introduces strict
slack. A finite phase partition has therefore supplied a bound at all lengths.
The Lean code represents `f` and the phase update with natural numbers and
integer comparisons, without real logarithms or floating-point arithmetic.

The strengthened device also works from **every rational initial phase**:
the same twelve-region partition certifies the short remainder bound uniformly,
giving, for every `r` in `(1/2,1]` and every natural `k`,

\[
\sum_{i=0}^{k-1}F^i(r)\le\frac{3k}{4}+\frac{11}{36}.
\]

This is `phase_global_bound`, stated with natural numerator and denominator
in Lean. In particular, `bcap_window_bound` gives every shifted window:

\[
108B_{s+k}\le108\,3^kB_s+(27k+11)3^{s+k}.
\]

No special starting phase or finite horizon is needed for this endpoint.

## Consequence for descent

If `k` is the first coefficient crossing, so that also `3^a<2^k`, then

\[
(27a+11)3^a<108(2^k-3^a)n
\quad\Longrightarrow\quad T^k(n)<n.
\]

Equivalently, failure to descend there forces

\[
108(2^k-3^a)n\le(27a+11)3^a.
\]

This improves the earlier closed-form numerator `a*3^a/3` when `a>=2`.
It also proves a stronger version of the previously only experimentally
checked quarter-slope majorant in `RealizableBound.lean`.

The exact envelope `B_a` remains sharper. This result supplies a concise
formula and a reusable phase certificate; it does not improve an exclusion
already computed using exact `B_a`. It neither proves that every starting
integer has a coefficient crossing nor removes the additive-gap condition
at a crossing. No new cycle-length record is claimed.

## Novelty audit

The following primary sources were inspected, with targeted searches for the
specific constants, the envelope recurrence, heavy prefixes, and phase bounds.

| Source | Existing content | Relation to this result |
|---|---|---|
| Halbeisen and Hungerbühler, *Optimal bounds for the length of rational Collatz cycles* (1997), Lemmas 4–5 and Section 3 | Affine-numerator majorization, balanced extremizers for a cyclic maximum-minimum problem, and bounds using short word blocks. | Establishes substantial prior art for positional extrema and block arguments. We do not claim those ideas as new. |
| Rozier and Terracol, *Paradoxical behavior in Collatz sequences*, v5 (2026-05-17), Lemmas 2.3, 2.5, Theorem 2.4, and Appendices A–C | Parity-vector majorization and remainder extrema; the mean remainder over all parity vectors is `j/4`. | That is an average under different quantifiers and normalization; it does not itself prove this worst-case heavy-prefix bound. The updated appendices do not supply this bound. |
| Collag3n, public post dated 2025-10-15, post 5 | The exact recurrence `B_(i+1)=3B_i+2^floor(i log2 3)` and a coarse bound, with a warning about the needed prefix condition. | Direct prior publication of the envelope; this is a primary discussion, not a refereed result. |
| Niu, *Parity vectors and paradoxical sequences in the accelerated Collatz map*, arXiv:2605.13886v1, withdrawn in v2 on 2026-05-20 | Fixed-length residue-class enumeration and finite-length counting/density estimates. The author withdrew it to avoid duplicating Rozier–Terracol. | Inspected as a search lead, not independent authority. No equivalent sharp envelope bound was identified. |

Sources:

- [Halbeisen–Hungerbühler paper](https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf).
- [Rozier–Terracol v5](https://arxiv.org/html/2502.00948v5).
- [Public envelope recurrence, post 5](https://forum.collatzworld.com/t/cycle-lengths-and-member-sizes-when-k-ceiling-x-log-3/135/5).
- [Niu v1](https://arxiv.org/html/2605.13886v1) and
  [withdrawal notice](https://arxiv.org/abs/2605.13886).

No equivalent `a/4+11/108` inequality or this exact twelve-step certificate
was located in the inspected sources. The defensible claim is a newly
derived and formalized explicit refinement relative to that search and to
the current repository. This is not proof of historical priority, nor an
external expert review. The envelope, rotation viewpoint, and general idea
of passing from uniform block bounds to arbitrary lengths are not claimed
as inventions. No first-ever Lean formalization claim is made.

## Artifacts and verification

- `Collatz/Strategy/BeattyBlockPotential.lean`: uniform phase certificate,
  arbitrary-phase and arbitrary-length bounds, shifted windows, equality
  characterization, and optimal intercept.
- `Collatz/Strategy/BeattyDescentBound.lean`: actual-orbit bound, conditional
  descent criterion, and a sharp actual-orbit witness.
- `scripts/probe_beatty_block_potential.py` and
  `Research/BeattyBlockPotentialProbe.json`: independent exact arithmetic
  checks, interval maxima, and counterexamples to shorter uniform blocks.
- `scripts/generate_beatty_phase_certificate.py --check`: reproduces the
  checked-in phase proofs. The generator has no trusted role in the proof;
  Lean checks the resulting inequalities and the covering case split.
- `scripts/audit_beatty_block_potential.lean`: prints the axiom dependencies
  of twenty theorem endpoints and the exact principal theorem types.

Verification completed on the final sources:

- `LEAN_NUM_THREADS=2 lake build Collatz.Strategy.BeattyDescentBound` passed
  (64 jobs); the final phase module and its orbit application were both rebuilt.
- `LEAN_NUM_THREADS=2 lake env lean scripts/audit_beatty_block_potential.lean`
  passed. All twenty endpoints use only `propext`, `Classical.choice`, and
  `Quot.sound`, or no axioms. No added mathematical axioms or proof placeholders.
- Generator reproduction and independent exact-rational probes passed.
- `git diff --check` and explicit whitespace checks of the new untracked
  sources passed.
- The broader `scripts/check_integrity.sh` run was stopped after approximately
  eight minutes during rebuilding of unrelated existing certificates under
  memory pressure. The full build and subsequent script stages are incomplete,
  not passed. Its log is `Research/BeattyBlockPotentialIntegrity.txt`.

The successful target build and axiom audit are recorded in
`Research/BeattyBlockPotentialBuild.txt` and
`Research/BeattyBlockPotentialAxioms.txt`. Finite exploratory output does not
substitute for the universal Lean proofs. A separate agent reviewed the proof
and interval arithmetic; this is internal checking, not external peer review.
