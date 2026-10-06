# A near-return device for Collatz correction sequences

Developed and Lean-verified 2026-09-28. The targeted build and all 18 theorem
axiom audits passed; only Lean's standard classical foundations occur.
Evidence is recorded in `ProofAtlasAttack/verification/shadow-window-report.json`.
This is not a proof of the Collatz conjecture. Historical priority remains
unconfirmed after the targeted literature comparison below.

## What the device adds

A short near-return in a real correction sequence forces a rational
approximation with a denominator bounded by the length of the return window.
Clearing these denominators, then using the integrality of the Collatz trace,
gives an explicit bound on how long such near-returns can occur in every
window. Consequently, a compatible infinite correction sequence cannot
approach **any finite set of real levels**, even with arbitrary switching
between irrational levels. This strengthens the earlier exclusions of fixed
periods and fixed rational grids.

The core is finite algebra. It does not use reciprocal summability, density
estimates, an assumed divergent orbit, or a transfer of limits between real
and 2-adic topologies.

## Exact hypotheses and statements

Let integer values \(x_i>0\), positive integer exponents \(a_i\ge1\), and real
corrections \(E_i\) satisfy

\[
2^{a_i}x_{i+1}=3x_i+1,
\qquad
2^{a_i}E_{i+1}=3E_i-1.
\]

Every odd Collatz trace satisfies the first identity. The finite theorem
also allows a slightly more general last step, whose endpoint need not be
odd. On an infinite integer trace the identity forces every \(x_i\) odd and
each division exponent to be maximal. The second defines a compatible
correction; it is a substantive hypothesis, not a claim about arbitrary
real sequences.

For a finite trace through index \(L+r\), assume \(1\le E_i\le M\), where

\[
M\ge1,\qquad C\in\mathbb N,\quad C\ge3M,\qquad
Q_r=(3^r)!,\qquad
\eta_{r,M,C}=\frac1{12Q_r C^r(M+1)}.
\]

**Finite window theorem.** If

\[
Q_r(x_0+M)+1\le2^L,
\]

then some \(i\le L\) has

\[
\boxed{\quad
|E_{i+k}-E_{i+j}|>\eta_{r,M,C}
\quad\text{for all }0\le j<k\le r.
\quad}
\]

Thus a sufficiently long trace contains \(r+1\) consecutive correction
values that are pairwise separated at the explicit scale.

**Finite dictionary theorem.** If every correction through time \(L+r\)
lies within \(\eta_{r,M,C}/2\) of one of \(r\) fixed real numbers, then

\[
\boxed{\quad 2^L<Q_r(x_0+M)+1.\quad}
\]

The dictionary may contain irrational numbers, and the choices of dictionary
entries may vary arbitrarily with time. The result bounds a specific kind
of finite approximation certificate, not Collatz stopping times. Constants
are deliberately conservative; factorial denominator clearing is not claimed
optimal.

**Infinite consequences.** Under the same all-time recurrence hypotheses:

- If \(1\le E_i\le M\), every tail contains the separated window above.
- Without any upper bound on \(E_i\), provided \(E_i\ge1\), every fixed finite
  set \(F\subset\mathbb R\) has a positive distance \(\varepsilon_F\) such
  that arbitrarily late \(E_i\) are farther than \(\varepsilon_F\) from every
  member of \(F\).

The second statement follows by splitting into an eventually bounded tail
and arbitrarily large excursions above the finite dictionary. In particular,
no such correction can converge in distance to a fixed finite set. For a
bounded correction, standard compactness then implies infinitely many
accumulation points. The accumulation-point reformulation is a mathematical
consequence; the formal endpoint is the explicit finite-set escape statement.

The previous canonical boundary \(E_i=B(x_i)-x_i\) on a hypothetical positive
injective orbit satisfies the displayed recurrence and \(E_i\ge1\), by the
earlier `ShadowOscillation` results. The new Lean modules prove the more
general recurrence statements directly. Their targeted verification does not
rebuild the large historical boundary/summability development.

## Proof of the new near-return step

Write \(c_i=2^{a_i}\). Define integer products and offsets by

\[
P_0=1,\quad R_0=0,\qquad
P_{t+1}=P_tc_t,\quad R_{t+1}=3R_t+P_t.
\]

The exact block identity is

\[
P_tE_t=3^tE_0-R_t.
\]

Suppose \(j+p\le r\), \(p>0\), and

\[
|E_{j+p}-E_j|\le\eta,\qquad C^r\eta<1.
\]

Let \(P,R\) be the product and offset of the return block starting at \(j\).
Then \(R\ge1\), \(P\le C^p\), and

\[
PE_{j+p}=3^pE_j-R.
\]

The integer \(D=3^p-P\) must be positive. Otherwise, using \(E_j\ge1\), the
last identity and the near-return estimate imply

\[
1\le R\le P\eta\le C^r\eta<1,
\]

a contradiction. Set

\[
q=3^jD,\qquad m=P_jR+DR_j.
\]

Both are integers, \(m\ge0\), and

\[
0<q\le3^r,\qquad
qE_0-m=P_jP(E_{j+p}-E_j).
\]

Therefore

\[
\boxed{\quad |qE_0-m|\le C^r\eta,\qquad1\le q\le3^r.\quad}
\]

This estimate works for general positive integer coefficients \(c_i\le C\);
the powers of two enter the next step through integer Collatz divisibility.

## From near-returns to an integer obstruction

Every denominator \(q\le3^r\) divides \(Q_r=(3^r)!\). Thus a near-return in
each window starting at \(i=0,\ldots,L\) puts \(Q_rE_i\) within

\[
Q_rC^r\eta=\frac1{12(M+1)}<\frac1{6(M+1)}
\]

of some nonnegative integer \(m_i\).

The earlier rational-grid lemma now applies. Rounding the correction
recurrence produces the exact integer identity

\[
2^{a_i}m_{i+1}+Q_r=3m_i.
\]

Adding it to \(Q_r\) times the Collatz recurrence, with

\[
b_i=Q_rx_i+m_i>0,
\]

gives \(2^{a_i}b_{i+1}=3b_i\). Coprimality forces \(2^L\mid b_0\), whereas
the rounding bound gives \(b_0<Q_r(x_0+M)+1\). This proves the length barrier.
Pigeonhole then gives the finite-dictionary version.

## Checks against overstatement

The exact-arithmetic probe constructs genuine finite integer trajectories
with prescribed periodic valuation words and perturbed rational corrections.
It checks the anchor identity with nonzero errors, not only exact periodic
returns. It also checks a finite trace for which the separated-window length
hypothesis actually holds. Results are in `ShadowWindowProbe.json`.

Integrality matters: positive **real** traces can follow a two-level
correction forever. For repeating coefficients \(2,4\), the correction
alternates between \(5,7\); the corresponding real \(3x+1\) trace remains
positive but need not stay integral. The probe checks this countermodel.

No argument here proves that the correction of a hypothetical divergent
integer orbit approaches a finite set. Infinite-complexity corrections remain
possible under the proved restrictions. Thus this is an obstruction and a
finite certificate bound, not universal descent or a Collatz proof.

## Novelty comparison

The exact separated-window criterion and finite-dictionary length bound were
developed in this attempt. The targeted search found no exact antecedent.
That is **not verification of historical priority**: the result should be
treated as a candidate original formulation pending expert review and a
broader literature search.

Known ingredients and close comparisons include:

| Source | Relevant prior work | Distinction from the present statement |
|---|---|---|
| [Bernstein–Lagarias, 1996](https://websites.umich.edu/~lagarias/doc/bernstein.pdf) | 2-adic conjugacy and parity coding | Does not supply the displayed real near-return/diversity bound. |
| [Rozier, 2019; revised 2025](https://arxiv.org/abs/1805.00133) | Inverse parity formulas and affine Euclidean embeddings | An established source for affine coding; its embedding differs from this compatible correction. |
| [Rozier–Terracol, 2026](https://arxiv.org/abs/2502.00948) | Finite affine corrections and coefficient/stopping-time distinctions | The accumulated correction and its control are prior ingredients, not new claims here. |
| [Dubickas, 2005](https://arxiv.org/abs/math/0512314) | Infinitely many fractional-power limit points, with specified exceptions | A close conceptual precedent with a constant multiplier; our recurrence has variable \(3/2^{a_i}\), an integer trace, and an explicit finite-window conclusion. |
| Existing local `ShadowLattice` | Finite rational-grid length barrier | Reused explicitly. Four extracted lemmas are not counted as new mathematical contributions. |

Searches included combinations of “Collatz correction limit points”,
“Collatz shadow rational recurrence”, “Collatz consecutive separated bounded
correction”, “3x+1 finite set real correction”, and related finite-state and
quantization terminology. Research-code and informal matches were inspected
as leads, not accepted as independent correctness evidence. The papers above
were used for comparison; none is an assumed theorem in the new Lean proof.

## Formal files

- `ShadowReturnArithmetic.lean`: products, offsets, and the rational anchor.
- `ShadowGridCore.lean`: four existing grid lemmas extracted without the large
  historical import graph; attribution is explicit in the file.
- `ShadowWindowDiversity.lean`: denominator clearing and the finite window bound.
- `ShadowQuantization.lean`: finite dictionary bound and infinite consequences.

All four files are in `ProofAtlasAttack/CollatzTargetDensity`. The new proof
depends on Mathlib and the displayed recurrence hypotheses. It introduces no
axiom asserting a Collatz estimate or any unproved mathematical result.

Reproduce the targeted build and transitive axiom audit from `ProofAtlasAttack`:

```sh
LEAN_NUM_THREADS=2 python3 scripts/verify_shadow_window.py
```

The audit covers every theorem in these four modules: 18 endpoints, including
four attributed grid lemmas reused from the earlier work. It checks the
pinned dependency revisions, rejects proof placeholders and added axioms in
the source, and records source fingerprints alongside the compiler output.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted in the
transitive axiom footprints. This is a targeted audit, not a replay of every
historical theorem in the repository.

The separate exact probe is `python3 scripts/shadow_window_probe.py` from the
repository root. Its current run checked 321 periodic/perturbed anchors (210
with nonzero error), 23 additional qualifying anchors from 5,000 random
finite recurrences, and 466 genuine integer Collatz steps. Experiments are
not assumptions in the Lean proofs.
