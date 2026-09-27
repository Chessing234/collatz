# Collatz predecessor density in every class modulo 2^p 3^q

**Verified in Lean on 2026-09-08.** The package build, source-hash checks,
transitive axiom audit, and modulus-72 examples passed. All audited
endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

This is an extension of the repository's all-target predecessor-density
theorem. It does not prove Collatz. The sibling and parity identities used
below are classical; historical priority for their density consequence has
not been established. The substantial analytic input remains Lech Mazur's
imported positive-density machinery, as adapted in
[AllTargetDensity.md](AllTargetDensity.md).

The unrestricted all-target theorem and its counterexample-density
consequence also appear in Mazur's September 6 manuscript
[*Positive Lower Density of Collatz Predecessors*](https://www.proofatlas.ai/formalizations/positive-lower-density-collatz-predecessors/),
located in a literature check on 2026-09-08. No novelty claim is made here
for that baseline result or for the progression extension.

## Exact statement

Let C be the ordinary Collatz map, with C(n)=n/2 for even n and C(n)=3n+1
for odd n. For a>0, p,q≥0, m=2^p 3^q, and 0≤r<m, define

\[
P_{a,m,r}(X)=\#\{n:0<n<X,\ n\equiv r\pmod m,
                  \ \exists k\ge0,\ C^k(n)=a\}.
\]

The extension proves

\[
\bigl(\exists c>0\;\exists X_0\;\forall X\ge X_0,
             \quad P_{a,m,r}(X)\ge cX\bigr)
\quad\Longleftrightarrow\quad 3\nmid a.
\]

The quantifiers over the target and modulus are unbounded. This is an
asymptotic result for each fixed progression, not a check of finitely many
starting values. The constant and threshold can depend on a,p,q,r.
For purely ternary moduli, the proof also gives positive density when the
starting integers are required to be odd.

The literal Lean interface uses the ordinary map and `Nat.count`:
[positive_density_in_progression_iff](../ProofAtlasAttack/CollatzTargetDensity/ResiduePublic.lean).
For example, for each of the 72 classes modulo 72, a positive proportion
of all positive integers belong to that class and reach 1.

## The arithmetic and counting argument

Write S for the odd-only Syracuse map, obtained by removing all factors
of two from 3n+1. Put

\[
g_t=\frac{4^t-1}{3},\qquad
J_t(n)=4^tn+g_t=(3n+1)g_t+n.
\]

For odd n, J_t(n) is odd, and

\[
3J_t(n)+1=4^t(3n+1),\qquad S(J_t(n))=S(n).
\]

For Q=3^q, the numbers g_t with 0≤t<Q permute the residues modulo Q.
One way to see injectivity is the identity

\[
v_3(4^d-1)=v_3(d)+1\qquad(d>0).
\]

Multiplication by 3n+1 is invertible modulo Q. Consequently, for every
input n and every residue r, there is t(n)<Q such that J_t(n)≡r mod Q.
This is a deterministic statement about every n; it assumes no random
distribution of orbit residues.

For n<X, the selected output is below 4^Q X. Selection can create
collisions, so counting the inputs as distinct outputs would be incorrect.
Instead retain the label t(n). The map

\[
n\longmapsto(t(n),J_{t(n)}(n))
\]

is injective, because each fixed J_t is injective. Each output has at most
Q labels. Thus, whenever all selected siblings of a source set A belong
to a destination set B,

\[
\#(A\cap[0,X))\le Q\,
\#\{y<4^QX:y\in B,\ y\equiv r\pmod Q\}.
\]

If A has lower density witnessed by c, the destination class has lower
density witnessed by c/(2Q4^Q), with a sufficiently large threshold. The
factor 2 pays for rounding arbitrary cutoffs down to a multiple of 4^Q.
The explicit bound is weak, but positive for every fixed q. The counting
and rounding statements are proved in
[CountTransport.lean](../ProofAtlasAttack/CollatzTargetDensity/CountTransport.lean)
and [TernarySpread.lean](../ProofAtlasAttack/CollatzTargetDensity/TernarySpread.lean).

### Handling the zero-step exception

The predecessor set of an arbitrary target is not automatically closed
under siblings: a target reaches itself in zero steps, whereas a sibling
only merges after the first odd step. This matters for a potentially
nonperiodic target.

The proof therefore chooses an odd d prime to 3 that reaches a, and an
odd seed prime to 3 with S(seed)=d. The existing analytic theorem supplies
positive density of odd n with S^k(n)=seed. For every such n,

\[
S^{k+1}(J_t(n))=d,
\]

including k=0. All siblings consequently reach a. This yields the ternary
density theorem without assuming the target periodic or convergent.
See [ResidueDensity.lean](../ProofAtlasAttack/CollatzTargetDensity/ResidueDensity.lean).

## Pullback to mixed moduli

Let T be the accelerated map: n/2 when n is even and (3n+1)/2 when n is
odd. Fix the desired residue u=r modulo m=2^p3^q. Let v=T^p(u), and let
s be the number of odd branches in this prefix. The classical affine
parity formula gives, for every z≥0,

\[
T^p(u+2^p3^qz)=v+3^{s+q}z.
\]

Apply the ternary theorem to predecessors of a in the class
v modulo D=3^{s+q}, and discard the finite interval y<v. Their density
remains positive. Every remaining y has a unique nonnegative integer
z=(y-v)/D, and the map

\[
y\longmapsto u+m\frac{y-v}{D}
\]

is injective on this source set. Its output lies in the desired class
modulo m and reaches y in p accelerated steps, hence reaches a under C.
For y<X the output is below (u+m+1)X, so the counting transport applies
again. The formal proof also checks positivity of the output, including
the boundary case u=0.

This is the argument in
[MixedResidueDensity.lean](../ProofAtlasAttack/CollatzTargetDensity/MixedResidueDensity.lean).
For the converse, if 3 divides a, its predecessors are exactly 2^j a.
That entire set has zero lower density, so no subset in a residue class
can have positive lower density.

## Consequence for a possible counterexample

If even one positive integer fails to reach 1, a positive target a prime
to 3 also fails to reach 1. Every predecessor of a is then a
counterexample. The theorem implies that counterexamples have positive
lower density in **every** fixed class modulo 2^p3^q.

Consequently Collatz is equivalent to this condition for **any one**
fixed such class: for every ε>0 and every initial cutoff X₀, there is
X≥X₀ with X>0 for which fewer than εX counterexamples below X lie in
that class. This is the checked theorem
`collatz_iff_sparse_bad_in_one_mixed_class`.

The sparse condition is unproved. Positive density of successful inputs,
even in every residue class, does not rule out positive density of
unsuccessful inputs in those same classes. Nor does the argument give
equidistribution, a uniform c/a bound, constants uniform as the modulus
grows, or coverage of moduli containing other primes.

## Attribution and verification

The analytic foundation and its source pins are documented in the
[package README](../ProofAtlasAttack/README.md). The all-target theorem
was already present before this extension. The new work here is the
formal density transport, the progression-level classification, and the
single-class counterexample criterion. The arithmetic ingredients are
not claimed as discoveries.

[Wirsching's paper](https://www.math.uni-bielefeld.de/baake/algdyn/posden.pdf)
studies the stronger program of uniform positive predecessor density and
its relation to ternary residue distributions. The present constants
do not establish that uniform program. The source searches made during
this work are insufficient to establish historical novelty.

Reproduce the proof and transitive axiom audit from `ProofAtlasAttack`:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
lake env lean Verification/ResidueDensity.lean
```

The literal statements and modulus-72 positive and negative examples are
in [Verification/ResidueDensity.lean](../ProofAtlasAttack/Verification/ResidueDensity.lean).
Build status and allowed-axiom evidence are recorded by the verifier in
[verification/local-report.json](../ProofAtlasAttack/verification/local-report.json).
