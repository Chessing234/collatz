# Sharp cut rigidity at prime-power moduli

Date: 2026-09-28.

Status: Lean-checked extension of the workspace's existing prime-modulus theorem. Historical novelty remains unconfirmed. This is not a proof of Collatz.

## Statement and conventions

Let p > 7 be prime, k ≥ 1, and m = p^k. On Z/mZ use the two branch permutations

\[
D(z)=2z,\qquad A(z)=(3z+1)/2.
\]

Division by 2 denotes multiplication by its modular inverse. For a subset S define

\[
b_f(S)=|S\setminus f(S)|+|f(S)\setminus S|,
\qquad b(S)=b_D(S)+b_A(S).
\]

These count entering and leaving edges together, preserving branch colours and parallel-edge multiplicity. Reversing the usual even branch z/2 to 2z leaves its crossing count unchanged.

**Theorem.** If 2 ≤ |S| ≤ m−2, then b(S) ≥ 4. This is sharp for every such m: S={1,2} has b(S)=4.

A related precise classification is: if 0 < |S| < m and b(S)=2, then |S|=1 or m−1. This classifies possible cardinalities, not all subsets attaining two.

## What is added here

The existing `BoundaryMoments`, `BoundaryCuts`, and `PrimeBoundary` modules already supply the ring-valued four-moment obstruction and the prime case. This extension supplies a proof over prime-power rings, where the field cancellation used for primes is invalid. It also proves a uniform sharpness witness. The arithmetic principle used is standard coprimality; no new general theorem about local rings is claimed.

The device is to retain the full modulus in the moment obstruction instead of merely reducing it modulo p. Reducing modulo p would give only |S| ≡ 0,1,−1 (mod p), allowing many interior cardinalities. The argument below gives the much stronger alternatives modulo p^k.

## Proof

Write q=|S|. Because each branch is a permutation, |S\f(S)|=|f(S)\S|; hence each b_f(S) is even.

First suppose b(S)=2. One branch preserves S and the other exchanges exactly one element. The previously formalized ring-valued moment elimination gives

\[
105q(q^2-1)=0\quad\text{in }\mathbb Z/m\mathbb Z.
\]

This is an imported **proved lemma**, `BoundaryCuts.two_boundary_annihilator`, not an assumed conjecture. Its derivation and exact moment equations are documented in `Research/BoundaryMoments.md` and formalized in `BoundaryMoments.lean`. Its coefficients are 5 for invariance under A and 21 for invariance under D; multiplying the applicable identity gives the common coefficient 105.

Since p>7, gcd(p^k,105)=1. Consequently

\[
p^k\mid(q-1)q(q+1).
\]

At most one of q−1,q,q+1 is divisible by p: otherwise p divides a nonzero difference of size 1 or 2, contradicting p>7. Every other factor is therefore coprime to p, and hence coprime to p^k. Euclid's lemma cancels those coprime factors from the divisibility above. Thus

\[
p^k\mid q-1\quad\text{or}\quad p^k\mid q
\quad\text{or}\quad p^k\mid q+1.
\]

For 0<q<p^k, the middle alternative is impossible. In the first alternative, 0≤q−1<p^k forces q=1. In the last, 0<q+1≤p^k forces q+1=p^k. This proves the two-edge cardinality assertion at every exponent k, without an induction on k or cancellation of arbitrary nonzero ring elements.

Next suppose b(S)=0. Both D and A preserve S, so B=D∘A, given by B(z)=3z+1, also preserves S. Put M=Σ_{z∈S}z in Z/mZ. Invariance gives

\[
2M=M,\qquad 3M+q=M.
\]

The first equation gives M=0 and the second then q=0 in Z/mZ, contradicting 0<q<m. This excludes zero boundary.

Since b(S) is even, excluding zero and two proves b(S)≥4 whenever 2≤q≤m−2.

For sharpness, let S={1,2}. We have D(S)={2,4} and A(S)={2,7/2}. For m>7, neither 4 nor 7/2 equals 1 or 2 modulo m: the latter equalities would imply 7≡2 or 7≡4. Thus each image shares exactly one vertex with S. Each branch contributes two crossings, so b(S)=4. Also 2≤|S|≤m−2.

## Why the prime-power hypothesis matters to this proof

At m=143=11·13 and q=12,

\[
q(q^2-1)=12\cdot143\equiv0\pmod{143},
\]

but q is none of 0,1,−1 modulo 143. Here different prime factors divide different consecutive factors. Lean checks this algebraic counterexample. It is **not** a subset with two crossing edges and does not refute a possible graph theorem for composite moduli. It shows exactly why this cardinality argument does not extend unchanged to arbitrary products of distinct primes.

## Formal endpoints and reproducibility

All new declarations are in `Collatz.Strategy.PrimePowerBoundary`:

- `power_divides_one_of_three`: the prime-power divisibility lemma.
- `obstruction_cardinality`: roots of the moment obstruction in the proper cardinality range.
- `two_boundary_cardinality`: two crossings force a singleton side.
- `zero_boundary_impossible`: no nonempty proper common invariant set.
- `four_le_boundary`: the unbounded prime-power cut theorem.
- `pair_boundary_sharp`: the witness {1,2} for every modulus >7 with an inverse of 2.
- `prime_power_sharp`: sharpness at all prime powers in the theorem.

The Lean set representation is a duplicate-free list. `four_le_boundary` assumes `L.Nodup`, `2≤L.length`, and `L.length+2≤p^k`, along with primality and p>7. The type requires `NeZero (p^k)`. The boundary theorem has no finite search bound. The sharpness corollary explicitly assumes k>0.

Reproduce with:

```text
lake build Collatz.Strategy.PrimePowerBoundary
lake env lean scripts/audit_prime_power_boundary.lean
```

Logs are `Research/PrimePowerBoundaryBuild.txt` and `Research/PrimePowerBoundaryAudit.txt`. The audit prints the dependencies of seven endpoints and checks an actual square-modulus example and the composite algebraic obstruction using kernel-evaluated `decide`.

## Bounded novelty review

Primary sources inspected on 2026-09-28 include:

1. [Karras and de Weger, Determinants of modular Collatz graphs and variants](https://arxiv.org/html/2601.15463v1), particularly the graph definition, connectedness, and odd-modulus structure. Their construction and branch structure are prior art. The inspected material does not state the prime-power two-crossing cardinality theorem proved here.
2. [Monks, Monks, Monks and Monks, Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph](https://arxiv.org/html/1204.3904), particularly the graph-deletion criteria and modular folding discussion. These concern sufficient sets and cycle survival, rather than the exact cut bound here.

Searches combined Collatz/modular Collatz with prime powers, two-edge cuts, edge connectivity, restricted edge connectivity, boundary, isoperimetric, and moments. No exact antecedent was located. This does not exclude equivalent affine-graph results, different terminology, inaccessible or unindexed literature, or unpublished work. No external expert review has occurred.

**Verdict:** a verified extension in this workspace and a candidate specific research contribution; historical novelty is not verified. The coprimality argument itself is elementary established mathematics. The achievement is a sharp structural theorem over infinitely many non-field moduli, not a revolutionary new general technique.

## Relation to the conjecture

These graphs contain both possible branches at each residue. Integer trajectories choose a branch according to parity. Four available crossing edges do not force a particular integer trajectory to cross any of them. This theorem does not prove universal descent, convergence, absence of integer cycles, or absence of divergent trajectories.
