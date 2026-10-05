# Four-moment obstruction for modular Collatz cuts

Date: 2026-09-28.

**Status:** a new derivation in this workspace, with a Lean-kernel-checked theorem for every prime above 7. Historical novelty remains unconfirmed. This is a theorem about finite modular graphs, not a proof of the Collatz conjecture.

## The theorem

Let p > 7 be prime. Form the modular Collatz multigraph on Z/pZ, with one edge of each colour from z to z/2 and from z to (3z+1)/2. Count crossing edges in both directions, keeping the two colours and all parallel edges separate. Loops never cross a cut.

For every subset S with 2 ≤ |S| ≤ p−2,

\[
\boxed{|\partial S|\ge 4.}
\]

Equivalently, a nonempty proper subset with exactly two crossing edges has size 1 or p−1. There is no upper bound on p in the proof. The lower bound is sharp: S={1,2} modulo 11 has four crossing edges. The prime exclusions are necessary: S={1,2} modulo 5 and S={3,5,6} modulo 7 each have two crossing edges despite having at least two vertices on each side. These three examples are also checked in Lean.

The algebraic device works more generally in rings with zero divisors. Put D(z)=2z and A(z)=(3z+1)/2. For a modulus m coprime to 6, if |∂S|=2 and q=|S|, then

\[
\begin{aligned}
 A(S)=S &\Longrightarrow 5q(q^2-1)\equiv0\pmod m,\\
 D(S)=S &\Longrightarrow 21q(q^2-1)\equiv0\pmod m.
\end{aligned}
\]

At least one of those two invariance conditions must hold. Consequently every such cut satisfies

\[
\boxed{105q(q^2-1)\equiv0\pmod m.}
\]

These are necessary conditions, not sufficient descriptions of cuts at composite moduli.

## The device: eliminate the interior using power sums

For a finite set and a permutation, the number of entering edges equals the number of leaving edges. Thus a two-edge boundary for D and A consists of one invariant branch and one branch that replaces exactly one member x of S by one member y outside S. Reversing the even branch from z/2 to D(z)=2z does not change its crossing-edge count.

The key idea is to evaluate low-degree polynomials on S. A branch preserves most of the set, so the change in a sum collapses to the two boundary values x and y. Invariance under the other branch supplies equations for the interior moments. Eliminating the moments and boundary values leaves a polynomial constraint on the cardinality q.

### Odd branch invariant: four moments give coefficient 5

Translate coordinates by +1, the known conjugacy that moves the odd branch's fixed point −1 to zero. Write

\[
 P_j=\sum_{z\in S}(z+1)^j,\quad P_0=q,\quad X=x+1,\quad Y=y+1.
\]

Since A(S)=S, multiplication of its image by 2 gives

\[
 (3^j-2^j)P_j=0.
\]

For j=1,2,3,4 this means

\[
 P_1=0,\qquad 5P_2=0,\qquad 19P_3=0,\qquad65P_4=0.
\]

In these translated coordinates doubling becomes z↦2z−1. The single exchange therefore gives

\[
\begin{aligned}
Y-X &=P_1-q,\\
Y^2-X^2 &=3P_2-4P_1+q,\\
Y^3-X^3 &=7P_3-12P_2+6P_1-q,\\
Y^4-X^4 &=15P_4-32P_3+24P_2-8P_1+q.
\end{aligned}
\]

All equations here are ring equations; no division by a potentially noninvertible coefficient occurs in the formal proof.

Set d=Y−X and s=X+Y. The first two equations imply d=−q and 5q(s+1)=0. Combining the first three yields

\[
95q(q^2-1)=0.
\]

This cubic calculation alone loses information in characteristic 19. The fourth equation repairs that loss: combining 7 times the fourth exchange equation with 32 times the third cancels P₃. After multiplying by 65, P₂ and P₄ also vanish. The identity obtained is

\[
65\bigl(7(Y^4-X^4)+32(Y^3-X^3)+25q\bigr)=0.
\]

Using d=−q and 5q(s+1)=0 in this equation gives

\[
1170q(q^2-1)=0.
\]

Finally, 37·95−3·1170=5, so an integer linear combination yields

\[
\boxed{5q(q^2-1)=0.}
\]

The fourth moment supplies real extra information. Modulo 19, the artificial data

\[
q=2,\ X=10,\ Y=8,\ P_1=P_2=0,\ P_3=12
\]

satisfy all the displayed equations through degree three, but violate 5q(q²−1)=0. Lean verifies this example. It is an example in the relaxed system of moment equations, **not** an actual set or a Collatz counterexample. Thus the stronger conclusion cannot follow from those cubic equations alone.

### Doubling branch invariant: three moments give coefficient 21

Use unshifted moments Mⱼ=Σzʲ. Doubling invariance gives

\[
 M_1=0,\quad3M_2=0,\quad7M_3=0.
\]

For the single exchange under A, multiplying through by powers of 2 gives

\[
\begin{aligned}
2(y-x)&=q,\\
4(y^2-x^2)&=5M_2+q,\\
8(y^3-x^3)&=19M_3+27M_2+q.
\end{aligned}
\]

With d=y−x and s=x+y, elimination gives

\[
3q(2s-1)=0,\qquad21q(12s^2+q^2-4)=0.
\]

Multiplying the first equation by 21(2s+1) gives 21q(12s²−3)=0. Subtraction yields

\[
\boxed{21q(q^2-1)=0.}
\]

For prime p>7 the coefficient 105 is nonzero, so the combined obstruction forces q=0,1,−1 in Z/pZ. When 0<q<p this is precisely q=1 or p−1. A common invariant set would have q=0 already from its first moments; hence no nonempty proper cut has zero crossing edges. Each branch contributes an even number. Excluding both zero and two proves the bound four.

## Exact formal scope

- `Collatz/Strategy/BoundaryMoments.lean`: permutation invariance and affine expansion of power sums; the two elimination lemmas; derivation from exact multiset identities; the first-moment common-invariance obstruction. The elimination lemmas hold in **any commutative ring**.
- `Collatz/Strategy/BoundaryCuts.lean`: a cut boundary is the size of the symmetric difference between a duplicate-free vertex list and its image. For a permutation this is precisely the number of entering plus leaving edges. The file proves the one-exchange decomposition from the boundary count and derives the uniform annihilator. Its ring hypotheses are an inverse of 2 and injectivity of multiplication by 3.
- `Collatz/Strategy/PrimeBoundary.lean`: specializes to `Fin p`; proves the needed arithmetic from the usual prime definition `2 ≤ p ∧ ∀ d, d ∣ p → d=1 ∨ d=p`; proves `two_boundary_cardinality`, `zero_boundary_impossible`, and `four_le_boundary`.
- `scripts/audit_boundary_moments.lean`: audits 15 named endpoints and kernel-checks the exceptional primes, sharp example, cubic relaxation at 19, and an unbounded-prime instance.

The formal graph definition uses the branch permutations directly. The independent probe additionally compares its boundary counts with the original accelerated Collatz rule on inputs 0,…,2m−1. The repository's separate `PeriodicDefectMinimum.defectCount` definition is not used as the statement of this theorem.

## Prior-art and novelty audit

The following primary sources and specified sections were inspected on 2026-09-28:

1. [Karras and de Weger, *Determinants of modular Collatz graphs and variants*, arXiv:2601.15463v1](https://arxiv.org/html/2601.15463v1), §§2.1, 2.4, 2.6.3 and 2.7.1. The branch permutations, loops, connectivity, branch cycle structure, and determinant methods are established background. The inspected sections do not state the four-moment boundary obstruction or the prime two-edge-cut cardinality theorem.
2. [Monks, Monks, Monks and Monks, *Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph*, arXiv:1204.3904](https://arxiv.org/html/1204.3904), §3 and the modular graph discussion. In particular, the +1 conjugacy and permutation-group approach are prior art; they are not claimed as inventions here. Its sufficient-set and back-tracing results have a different conclusion from a classification of minimum cut sizes.
3. [Laarhoven and de Weger, *The Collatz conjecture and De Bruijn graphs*, arXiv:1209.3495](https://arxiv.org/html/1209.3495), §§1–2. The modular graph construction and the structure at powers of two are prior art. The present theorem concerns prime moduli above 7.

Additional searches combined “Collatz” and “modular Collatz” with “power sums”, “two-edge”, “edge-cut”, “minimum cuts”, “edge connectivity”, and “super-edge”. No exact antecedent was identified. Searches were also made for the coefficient/boundary formulation. An Andaloro directed-graph paper was located, but its text could not be inspected reliably; it is not counted as reviewed coverage.

Power sums, finite-set moment methods, permutation boundary conservation, and elimination of polynomial equations are standard mathematics. The candidate contribution is their **specific application and explicit elimination here**, including removal of the characteristic-19 obstruction and the resulting uniform prime cut theorem. The report does not claim a new general moment method.

**Novelty verdict:** no matching theorem or proof was found in this bounded source comparison. That makes this a candidate research contribution, not verified historical priority. Equivalent results under different terminology, general affine-graph theorems, unindexed work, and unpublished results have not been ruled out. No external expert review occurred. Lean checks mathematical deductions from the exact hypotheses; it does not establish novelty or significance.

## Verification

The targeted build and the audit pass. The 15 audited endpoints depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The new sources contain no `sorry`, added axioms, Mathlib imports, or `native_decide`.

The independent probe examined all two-edge cuts for 83 moduli coprime to 6 from 5 through 251, including 52 primes. It also exhaustively checked 665,760 subsets across the applicable moduli at most 19. It found zero failures. These computations are supporting checks, not premises of the unbounded theorem. Output is saved in `Research/BoundaryMomentsProbe.json`.

Reproduce the mathematical audit with:

```text
lake build Collatz.Strategy.PrimeBoundary
lake env lean scripts/audit_boundary_moments.lean
python3 scripts/boundary_moments_probe.py
```

Repository-wide integrity status is recorded separately in `Research/BoundaryMomentsVerification.txt` so a pre-existing build or scan problem cannot be confused with the new theorem's verification.

## What this does and does not resolve

This supplies a concrete obstruction to almost invariant residue sets and a uniform theorem about finite modular Collatz graphs. It strengthens structural information beyond plain connectedness.

It does **not** show that every positive integer reaches a smaller integer, exclude all nontrivial integer cycles, or exclude divergent integer orbits. A modular graph contains both branch choices at each odd-modulus residue. A particular integer orbit follows a parity-determined path through it. A lower bound on the number of available boundary edges does not force that orbit to traverse one of them. Establishing an appropriate connection to actual trajectories remains a separate unresolved step.
