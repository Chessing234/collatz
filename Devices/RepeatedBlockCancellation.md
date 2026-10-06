# Uniform cancellation in repeated Collatz blocks

Research note, 28 September 2026.

**Status:** a proved, core-only Lean device for exact cycle arithmetic. This is
not a proof of Collatz. The underlying affine and commutator algebra is prior
art. The uniform cancellation corollary below was developed and formalized in
this session; its historical novelty is **not established** by the literature
search. It is a modest arithmetic tool, not a demonstrated major breakthrough.

## 1. The question that led to the device

The existing `ResidualComposition` module gives a counterexample to computing
the reduced denominator of a concatenated word solely from the reduced
denominators and shapes of its two pieces. The missing information includes
the relative positions of their rational fixed points.

Instead of guessing a composition rule for reduced denominators, retain the
cross-determinant of the numerator–gap pairs. Its magnitude need not be small
for arbitrary words. The useful fact is that **its odd part is unchanged by
prepending arbitrarily many copies of one reference block**. This gives a
certificate of fixed size for an infinite family.

## 2. Definitions and conventions

Use the shortcut Collatz map

\[
T(n)=\begin{cases}n/2& n\text{ even},\\(3n+1)/2&n\text{ odd}.
\end{cases}
\]

A word is read from left to right; `0` means the even branch, `1` the odd
branch. For a finite word \(w\), put

\[
B_w=2^{|w|},\qquad A_w=3^{a(w)},\qquad G_w=B_w-A_w.
\]

Here \(a(w)\) counts ones, and the affine numerator is defined by

\[
C_\varnothing=0,\quad C_{w0}=C_w,\quad
C_{w1}=3C_w+2^{|w|}.
\]

If an actual orbit follows \(w\), then
\(B_wT^{|w|}(n)=A_wn+C_w\). An integer cycle with this word therefore
requires \(G_w\mid C_w\). The Lean theorem `follows_affine` proves the
connection to the actual deterministic map.

**All gaps in this note are signed integers.** There is no assumption that the
individual blocks contract. For nonempty words the gap is odd. The reduced
denominator of the rational fixed-point candidate is

\[
q_w=\frac{|G_w|}{\gcd(C_w,G_w)}.
\]

## 3. The fixed certificate

Fix words \(u,v\), and define

\[
D(u,v)=G_uC_v-C_uG_v,\qquad w_k=u^kv.
\]

The familiar append laws are

\[
C_{uw}=A_wC_u+B_uC_w,\qquad
G_{uw}=A_wG_u+B_uG_w.
\]

Taking their cross-determinant cancels the terms containing \(A_w\):

\[
G_uC_{uw}-C_uG_{uw}
=B_u(G_uC_w-C_uG_w).
\]

Induction gives the exact transport identity

\[
\boxed{G_uC_{w_k}-C_uG_{w_k}=2^{k|u|}D(u,v).}
\]

Let \(d_k=\gcd(C_{w_k},G_{w_k})\). It divides the left side. Since a nonempty
\(w_k\) has odd gap, \(d_k\) is odd, and the power of two on the right can be
cancelled. Consequently

\[
\boxed{d_k\mid D(u,v).}
\]

This is `cancellation_dvd_defect`. It holds for every \(k\), provided
\(w_k\ne\varnothing\), including when \(D=0\). If \(D\ne0\), it yields

\[
d_k\le |D|,\qquad \boxed{q_{w_k}|D|\ge |G_{w_k}|}.
\]

Thus \(|G_{w_k}|>|D|\) excludes every integer fixed point for that word.
These conclusions are `cancellation_le_defect`, `denominator_lower_bound`,
and `excludes_integral_fixed_point`.

## 4. An exact formula, with an essential hypothesis

If \(u\ne\varnothing\) and \(\gcd(G_u,G_v)=1\), then

\[
\boxed{\gcd(C_{w_k},G_{w_k})=\gcd(D(u,v),G_{w_k}).}
\]

Proof: the append law and coprimality with two imply
\(\gcd(G_u,G_{w_k})=\gcd(G_u,G_v)=1\). Taking gcd with \(G_{w_k}\)
in the transport identity, and cancelling both invertible factors
\(G_u\) and \(2^{k|u|}\), proves the formula. This is `exact_cancellation`.

Since

\[
G_{w_k}=B_u^kB_v-A_u^kA_v,
\]

the cancellation factor can be computed using modular exponentiation modulo
the fixed integer \(|D|\), without constructing the growing word or its
numerator. The closed gap formula is also proved in Lean. No claim about
general orbit convergence follows from this compression.

The coprimality assumption cannot be dropped: for \(u=11,v=001,k=1\), the
actual cancellation gcd is 1 while \(\gcd(D,G_{uv})=5\). This counterexample
is kernel-checked as `coprime_hypothesis_needed`.

## 5. A finite calculation excludes an infinite tail

Suppose \(G_u\ge0\), \(v\ne\varnothing\), and \(D\ne0\). Once a single
integer \(K\) satisfies \(G_{w_K}>|D|\), every \(k\ge K\) is excluded.
Indeed, for positive \(G_w\),

\[
G_{uw}=A_wG_u+B_uG_w\ge G_w.
\]

The theorem `tail_exclusion` proves this implication for all later counts.
It leaves the existence of such a threshold as a hypothesis, rather than
silently treating it as a proved bound for all possible block pairs.

For a complete example, take \(u=0011\), \(v=11\). Then

\[
(C_u,G_u)=(20,7),\quad(C_v,G_v)=(5,-5),\quad D=135.
\]

At \(k=1\), \((C,G)=(260,-17)\), so there is no integer fixed point.
At \(k=2\), \((C,G)=(5780,295)\), and \(295>135\). The tail theorem
therefore excludes every \(k\ge2\) at once. The theorem
`example_no_actual_cycle` concludes that **no natural-number Collatz cycle
has parity word \((0011)^k11\) for any \(k\ge1\)**.

This example demonstrates the certificate; no novelty is claimed for the
exclusion of this particular simple family.

## 6. Stronger extension: two independent repetition counts

The suffix need not be fixed. Define the homogeneous geometric sum

\[
S_u(k)=\sum_{i=0}^{k-1} A_u^{k-1-i}B_u^i,\qquad S_u(0)=0.
\]

The formal definition uses the equivalent recurrence
\(S_u(k+1)=A_u^k+B_uS_u(k)\). Induction proves

\[
C_{u^k}=C_uS_u(k),\qquad G_{u^k}=G_uS_u(k).
\]

For \(w=u^kv^\ell\ne\varnothing\), let \(d=\gcd(C_w,G_w)\).
The one-block theorem, with suffix \(v^\ell\), gives
\(d\mid D(u,v)S_v(\ell)\). Rotating the two repeated pieces leaves this
cancellation gcd unchanged: the elementary identity

\[
B_xC_{yx}=A_xC_{xy}+C_xG_{xy}
\]

allows cancellation of the power of two \(B_x\), in either direction.
Applying the same bound to \(v^\ell u^k\) gives
\(d\mid D(u,v)S_u(k)\). Taking their gcd yields

\[
\boxed{\gcd(C_{u^kv^\ell},G_{u^kv^\ell})
\mid |D(u,v)|\gcd(S_u(k),S_v(\ell)).}
\]

This is `two_block_cancellation`. It requires neither coprime block gaps nor
contracting blocks, and applies to every pair of repetition counts. If the
two geometric sums are coprime and \(D\ne0\), the fixed bound \(d\le|D|\)
survives while **both** repetition counts vary (`two_block_coprime_bound`).

In particular, a genuine integer cycle with this word must satisfy

\[
\boxed{|G_{u^kv^\ell}|\mid |D(u,v)|\gcd(S_u(k),S_v(\ell)).}
\]

The direct bridge is `two_block_actual_cycle_constraint`. This separates the
arithmetic obstruction into the fixed mismatch between the two blocks and
the common factors introduced by their repetition counts. It does not prove
that the latter gcd is small for arbitrary inputs. Such a bound would be a
substantive additional number-theoretic task.

## 7. Limits and the novelty audit

- When \(D=0\), the blocks share the same projective numerator–gap data, and
  the upper bound is unavailable. In particular, \(D(u,u)=0\). Repetitions
  of a genuine cycle are correctly retained.
- For unrestricted pairs, \(|D(u,v)|\) can grow with the words. There is no
  uniform bound here covering all possible cycle words.
- The result concerns cycles, not divergent aperiodic orbits. It does not
  establish universal descent, or solve either remaining general obstruction.

Primary sources inspected during this session:

1. [Halbeisen and Hungerbühler, *Optimal bounds for the length of rational
   Collatz cycles*](https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf),
   §2, equation (4), Lemma 2, and §5, Lemma 9. These contain the classical
   affine concatenation formula and gcd relations among rotated numerators.
2. [Trümper (2014), *The Collatz Problem in the Light of an Infinite Free
   Semigroup*](https://doi.org/10.1155/2014/756917), §3.2 and §4, especially
   equation (75) and Lemmas 2–3. The numerator–gap cross-determinant and
   pure-repetition algebra are already present there. Renaming that
   determinant would not constitute new mathematics.
3. [Zemyan (2020), *Cyclemaster Matrices and Collatz Cycles*](https://math.colgate.edu/~integers/u82/u82.pdf),
   Theorems 1 and 8 and §3.3. This provides prior determinant-divisibility
   obstructions, using cyclemaster matrices rather than the fixed two-block
   certificate used here.

Additional searches included “Collatz cycle concatenation words determinant
gcd fixed points resultant”, “Collatz repeated block denominator”,
“Collatz bounded cancellation”, and “Collatz coprime concatenation cycles”.
Searches also covered “Collatz cycles geometric sums gcd blocks” and “Collatz
two blocks gcd”. The inspected passages did not explicitly state the exact
fixed-suffix gcd formula of §4 or the two-repetition divisibility certificate
of §6. This is a limited search result, **not proof of historical
priority**. The formula is an elementary corollary of known algebra and may
exist elsewhere or be considered implicit. No independent expert review has
been obtained. The defensible contribution is the explicit cancellation
certificate and its verified implementation in this repository.

## 8. Reproduction and verification

Source: `Collatz/Strategy/RepeatedBlockCancellation.lean`.

```
lake build Collatz.Strategy.RepeatedBlockCancellation
lake env lean scripts/audit_repeated_block_cancellation.lean
python3 scripts/probe_repeated_block_cancellation.py
bash scripts/check_integrity.sh
```

The targeted build and endpoint axiom audit passed. The main endpoints
use only `propext` and `Quot.sound`; the explicit coprimality counterexample
uses no axioms. There is no Mathlib import, added axiom, unfinished proof, or
native-decision shortcut in this module.

The independent finite regression checks **841,756** instances: all nonempty
binary \(u\) of length at most 7, all binary \(v\) of length at most 7, and
\(0\le k\le12\), excluding the empty resulting word. Of these, 716,865 satisfy
the coprime-gap hypothesis and pass the exact formula. There are 1,036 direct
word-reconstruction checks. A further **184,512** direct-word checks cover
the two-block theorem for nonempty blocks of length at most 5 and
\(0\le k,\ell\le6\), \(k+\ell>0\); 121,484 also exercise the nonzero-defect,
coprime-geometric-sum bound. These tests supplement the quantified Lean proofs.

The repository-wide integrity script was attempted but stopped during
expensive rebuilds of older modules (`VerifiedRung8917`, `TreeCertificate3`,
`GapPrimes`, `StairGeneric`, and `PosLadder`). It did **not** complete and is
not reported as a pass. Focused compilation and the endpoint audit are the
verification evidence for this result.

Saved evidence is in `Research/RepeatedBlockCancellationAxioms.txt`,
`Research/RepeatedBlockCancellationProbe.json`, and
`Research/RepeatedBlockCancellationIntegrity.txt`.
