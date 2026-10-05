# Periodic defect transport and a finite amplification certificate

Date: 2026-09-28. Status: **kernel-checked structural theorems; historical novelty not established; no Collatz convergence proof.**

## Result

Let \(T(n)=n/2\) for even \(n\), and \(T(n)=(3n+1)/2\) for odd \(n\).
Let \(f:\mathbb N\to\{0,1\}\) have a specified positive period \(m\), with \(3\mid m\).
Set

\[
 D_k=\#\{0\le n<2^{k+1}m:f(T^{k+1}n)\ne f(T^kn)\},
 \qquad
 C=\#\{0\le n<2m:3\nmid n,\ f(Tn)\ne f(n)\}.
\]

These are counts in specified expanding ranges, not counts in least periods.
The following statements have been proved in core Lean:

1. **Exact transport:** \(D_1=D_0+3\#\{n<2m:n\equiv2\pmod3,\ f(Tn)\ne f(n)\}\).
2. **Sharp two-step increment:** \(D_{2k}\ge D_0+3kC\) for every \(k\ge0\).
3. **Uniform exponential amplification:** \(D_{4k}\ge4^kC\) for every \(k\ge0\).
4. **Plateau criterion:** the following are equivalent:
   - \(D_2=D_0\);
   - the sequence \(D_k\) is bounded;
   - \(C=0\);
   - \(f(Tn)=f(n)\) for every \(n\) not divisible by three.
   In that regime \(D_k=D_0\) for every \(k\). Otherwise \(C\ge1\), so \(D_{4k}\ge4^k\).

Thus there is no unbounded-but-subexponential regime for these specified defect towers.

The complementary case \(3\nmid m\) has the exact formula \(D_k=2^kD_0\), also formalized, using the checkout's pre-existing mass-conservation theorem. Consequently `defect_dichotomy_all` proves **at every positive period** that either \(D_k=D_0\) for all \(k\), or \(D_{4k}\ge4^k\) for all \(k\). The exact-doubling case is a routine consequence of known modular balance, not claimed as a new ingredient.

The coefficient three in (2) is attained by the Boolean label \(f(n)=1[n\equiv1\pmod9]\): \(D_0=C=3\) and \(D_2=12\). The bounded regime is genuinely possible for a nonconstant label: \(f(n)=1[3\mid n]\) has \(D_k=1\) for all \(k\). Both examples are Lean-checked.

## The reusable device

The main reusable output is `finite_certificate_amplifies`, not just a particular numerical bound. For a nonnegative integer-valued periodic weight \(g\), define

\[
 C_k(g;M)=\sum_{\substack{0\le n<2^kM\\3\nmid n}}g(T^kn).
\]

Define transfer weights recursively by

\[
 W_0(n)=1[3\nmid n],\qquad
 W_{j+1}(n)=W_j(2n)+
 \begin{cases}3W_j((2n-1)/3),&n\equiv2\pmod3,\\0,&\text{otherwise}.\end{cases}
\]

Here the coefficient three counts modular repetitions. It does **not** assert that an integer has three odd predecessors under \(T\).

**Finite-certificate theorem.** If

\[
 W_b(r)\ge A\,1[3\nmid r]\quad(0\le r<3^{b+1}),
\]

then for **every** period \(M\) divisible by three, every nonnegative integer-valued \(M\)-periodic \(g\), and every \(k\ge0\),

\[
 C_{bk}(g;M)\ge A^k C_0(g;M).
\]

This is an implication from a finite table to an unbounded family of theorems, proved in Lean. The finite table is the certificate premise; it is not a substitute for the implication proof.

### Why finite checking is sufficient

The proof has four parts:

1. Splitting a sum into even and odd inputs proves the weighted duality identity. The odd input contribution runs through one residue class modulo three, with three repetitions.
2. Induction gives period \(3^{b+1}\) for \(W_b\) and the exact identity \(C_b(g;M)=\sum_{n<M}W_b(n)g(n)\) whenever \(3^{b+1}\mid M\).
3. For an arbitrary \(3\mid M\), temporarily use the larger period \(3^bM\). It satisfies the divisibility requirement. Both core counts are multiplied by exactly \(3^b\), so cancellation proves the original-period inequality. No equidistribution assumption is needed.
4. Reapply the bound to \(g\circ T^{bk}\), whose specified period is \(2^{bk}M\). This proves the result for all \(k\).

Lean evaluates the \(b=4,A=4\) table on `Fin 243` using `decide`. The table theorem has **no axiom dependencies**. The multiplier four is optimal for this four-step pointwise certificate: \(W_4(4)=4\). A three-step certificate cannot amplify strictly, since \(W_3(7)=1\). For arbitrary nonnegative weights, the four-step multiplier is attained by \(g(n)=1[n\equiv4\pmod{243}]\), with \(C_0=1,C_4=4\); this is also Lean-checked. Optimality is **not** claimed for the smaller class of Boolean-label defect weights or for the asymptotic rate.

The Boolean specialization uses \(g(n)=1[f(Tn)\ne f(n)]\), of period \(2m\). `labelPulls_orbit`, `error_pulls`, and `defectTower_eq_massTower` verify that the formal counts really are the orbit-defined counts above.

## Scope and unresolved step

This gives an effective test for stability of periodic label errors and a method for certifying quantitative instability. It does not make an integer orbit descend.

Every four pullbacks multiply the specified range length by sixteen, while the proved lower bound multiplies the core error count by four. After normalization, this bound decays by a factor four per block; it is not a positive limiting density estimate. In particular, it supplies neither orbit-by-orbit hitting, convergence to one, nor exclusion of cycles or divergent orbits. The statement that every integer \(n>1\) eventually reaches a smaller integer has not been proved.

## Novelty review

Verdict: **independently derived and newly formalized here, but not verified historically novel.** The closest inspected sources already contain the principal ingredients. The particular finite-certificate/defect-dichotomy package is a candidate formulation, not an established breakthrough.

- [Karras and de Weger, *Determinants of modular Collatz graphs and variants*, arXiv:2601.15463v1](https://arxiv.org/html/2601.15463v1), §2.1: the modular indegrees are one or four when the modulus is divisible by three. Our one-step identity is a direct weighted consequence of these known multiplicities; it should not be advertised as new. The reviewed portions also discuss modular graph structure. No unrestricted strong-connectivity assertion from this paper is used in our proof.
- [Leventides and Poulios, *Koopman operators and the 3x+1-dynamical system*, arXiv:2010.12987](https://arxiv.org/pdf/2010.12987), introduction and §§4–6, especially Theorem 5.4: composition operators and growth of inverse-image multiplicities are established approaches. Their operator norms concern sequence spaces and integer preimage counts. Our expanding periodic-range counts are different objects, but that difference does not establish a new method.
- [Krasikov and Lagarias, *Bounds for the 3x+1 Problem using Difference Inequalities*, arXiv:math/0205002](https://arxiv.org/pdf/math/0205002), introduction, Proposition 2.1 and Theorem 2.2: finite systems indexed by ternary residues and feasible certificates yield rigorous exponential lower bounds. Thus the broad finite-certificate-to-growth strategy is old. Their bounds concern inverse orbits below a size threshold; ours concern periodic errors on expanding ranges and do not improve their results.
- [Monks, Monks, Monks and Monks, *Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph*, arXiv:1204.3904](https://arxiv.org/html/1204.3904), introduction, Theorem 4.1 and graph sections: pruning multiples of three and modular back-tracing are standard. Their bound in Theorem 4.1 counts odd inverse branches, not the total number of accelerated steps.
- [Béhani, *Linear dynamics of an operator associated to the Collatz map*, arXiv:2303.03203](https://arxiv.org/abs/2303.03203), introduction and Proposition 2.1 screened: another operator-theoretic precedent, in a different function-space setting. This was a targeted inspection, not an exhaustive review of the paper.

Searches included `Collatz periodic defect amplification`, `Collatz pullback bounded periodic`, `Collatz transfer periodic functions`, `Collatz Koopman variation`, `Collatz modular boundary`, and `Collatz inverse trees difference inequalities`. No exact statement of this package was located in the inspected material. Keyword failure is not priority evidence, and equivalent formulations or further literature may supersede it. No external mathematical review has been obtained.

Within this checkout, the pre-existing `PeriodicDefectMinimum` supplies periodic defect counts and finite-sum infrastructure. `TreeStochastic` and `TreeBalance` already develop related inverse-tree transfer and certificate ideas; they address different counting functions. Concurrent workspace additions, including `PeriodicBranchEmbedding`, are not claimed as work authored by this change and are not dependencies of these two new modules.

## Formal endpoints and verification

- `Collatz/Strategy/PeriodicDefectTransport.lean`: exact transport, linear growth, orbit bridges, boundedness and plateau criteria.
- `Collatz/Strategy/PeriodicDefectAmplification.lean`: weighted duality, period inflation/cancellation, finite-certificate interface, exponential bound and dichotomy.
- `scripts/audit_periodic_defect_transport.lean`: 23 theorem axiom reports plus concrete examples and sharpness witnesses.
- `scripts/probe_periodic_defect_transport.py`: independent forward-orbit regression tests, not a proof.

The narrow build and new audit passed on Lean 4.33.0-rc1. Axiom reports contain only `propext`, `Quot.sound`, and, for some endpoints, `Classical.choice`; there are no added axioms or proof placeholders. The finite table itself has no axioms. Existing periodic-rigidity and variation-stability audits also passed.

The independent probe passed for all 4,680 Boolean labels of periods 3, 6, 9, and 12, at scales 0 through 8; 60 have constant towers. It also checked exact doubling for all 1,462 labels of periods 1, 2, 4, 5, 7, 8, and 10, for 6,142 labels altogether. It separately enumerated forward orbits to verify all 243 columns of the four-step transfer matrix. See [audit output](PeriodicDefectTransportAudit.txt) and [probe output](PeriodicDefectTransportProbe.json).

Reproduce:

```sh
lake build Collatz.Strategy.PeriodicDefectAmplification
lake env lean scripts/audit_periodic_defect_transport.lean
python3 scripts/probe_periodic_defect_transport.py
lake env lean scripts/audit_periodic_rigidity.lean
lake env lean scripts/audit_periodic_variation_stability.lean
bash scripts/check_integrity.sh
git diff --check
```

The full-repository integrity run was interrupted after approximately nine minutes while rebuilding older numerical certificates. A second full build was concurrently compiling some of the same files, so this task's duplicate build was stopped; the other build was left alone. The saved [integrity log](PeriodicDefectTransportIntegrity.txt) is partial, and the full check is **not reported as passed**. The new targeted proofs and audits above completed independently. A direct scan of the two new proof modules and their audit found no proof-escape tokens. `git diff --check` passed. No full-repository integrity conclusion follows from these targeted checks.
