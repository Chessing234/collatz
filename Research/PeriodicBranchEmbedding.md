# Four explicit inverse branches amplify periodic Collatz errors

Research record, 28 September 2026.

**Status:** the general arithmetic theorem and its application to periodic
Boolean labels are proved in Lean. Historical novelty is **not established**.
The exact statement below was not located in the inspected primary sources.
It is a candidate contribution built from established modular and inverse-branch
ideas, not a proof of the Collatz conjecture.

## The mathematical device

Use the accelerated map

\[
T(n)=\begin{cases}n/2&n\text{ even},\\(3n+1)/2&n\text{ odd}.\end{cases}
\]

Let \(P>0\), \(3\mid P\), and let \(w:\mathbb N\to\mathbb N\) be
\(P\)-periodic. Define the weighted count away from multiples of three by

\[
C_k(P,w)=\sum_{\substack{0\le n<2^kP\\3\nmid n}}w(T^k(n)).
\]

The principal theorem is

\[
\boxed{C_4(P,w)\ge4C_0(P,w),\qquad
C_{4j}(P,w)\ge4^jC_0(P,w)\quad(j\ge0).}
\]

There is no bound on the period, depth, or values of the nonnegative integer
weight. The coefficient 4 is optimal for this class of weights. Three steps
cannot give any universal coefficient greater than 1.

The device is a uniform embedding of four inverse branches that avoid
multiples of three. A residue-level obstruction therefore has many distinct
antecedents when the period is refined. This supplies a quantitative test for
whether errors in a periodic candidate invariant can remain bounded.

## Explicit proof

First suppose \(9\mid P\). Fix \(0\le v<P\), \(3\nmid v\), and write
\(v=3q+b\), where \(b\in\{1,2\}\). Direct calculation gives

\[
\begin{aligned}
T^4(16q)&=q,\\
T^4(16q+4)=T^4(16q+5)&=3q+1,\\
T^4(16q+8)=T^4(16q+10)&=3q+2.
\end{aligned}
\]

Choose the offset \(r\) from this table:

| \(v\bmod9\) | 1 | 2 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|
| \(r\) | 4 | 8 | 4 | 10 | 5 | 8 |

Then \(3\nmid(q+r)\), and the four integers

\[
16v,\quad16q+r,\quad16(q+P/3)+r,\quad16(q+2P/3)+r
\]

are distinct, lie below \(16P\), are not divisible by 3, and all satisfy
\(T^4(n)\equiv v\pmod P\). Distinct target residues have disjoint fibers.
Weighting each target by \(w(v)\) and summing proves the fourfold inequality.

For a period divisible by 3 but not necessarily by 9, apply this proof at
period \(9P\). Both weighted counts repeat nine times; cancel the common
factor. Finally apply the fourfold inequality successively to
\(w\circ T^{4j}\), of period \(2^{4j}P\), to obtain the exponential bound.

Sharpness is witnessed by the periodic weight
\(w(n)=\mathbf1_{n\equiv7\pmod9}\). Direct, kernel-checked evaluation gives

\[
C_0(9,w)=1,\qquad C_3(9,w)=1,\qquad C_4(9,w)=4.
\]

Sharpness here concerns arbitrary weights. No optimality claim is made after
restricting weights to errors of Boolean labels.

## Consequence for approximate invariants

Let \(f:\mathbb N\to\{0,1\}\) have a prescribed period \(m>0\) with
\(3\mid m\). Put

\[
\delta_f(n)=\mathbf1_{f(T(n))\ne f(n)},\qquad f_k=f\circ T^k,
\]

\[
D_k=\#\{0\le n<2^{k+1}m:f_k(T(n))\ne f_k(n)\},\qquad
A=\#\{0\le n<2m:3\nmid n,\ \delta_f(n)=1\}.
\]

The error indicator has period \(2m\), and
\(\delta_{f_k}=\delta_f\circ T^k\). Hence

\[
\boxed{D_{4j}\ge4^jA.}
\]

Together with the transport lemmas in `PeriodicDefectTransport`, this gives
exactly two regimes:

* If \(A=0\), then \(D_k=D_0\) for every \(k\).
* If \(A>0\), then \(D_{4j}\ge4^j\) for every \(j\).

Moreover, the two-step comparison decides the regime: \(D_2=D_0\) if and
only if the entire sequence is constant; otherwise \(D_2>D_0\) and the
exponential lower bound applies. The two-step test and stable case use the
existing transport module; the explicit four-branch argument supplies the
exponential bound.

Examples at \(m=3\), for depths 0 through 8:

| Label | Error counts \(D_0,\ldots,D_8\) |
|---|---|
| \(f(n)=\mathbf1_{3\mid n}\) | 1, 1, 1, 1, 1, 1, 1, 1, 1 |
| \(f(n)=\mathbf1_{n\equiv1\pmod3}\) | 3, 6, 15, 30, 63, 126, 255, 510, 1023 |

These are counts in the **prescribed expanding periods**, which need not be
least periods. The sampling interval grows by 16 every four steps. A lower
bound growing by 4 does not imply that the fraction of errors increases.
Nor does it imply that every integer orbit encounters an error, descends,
or reaches 1. No step transfers a modular counting result into universal
positive-integer convergence.

## Lean endpoints and provenance

New source in this research pass:
`Collatz/Strategy/PeriodicBranchEmbedding.lean`.

| Endpoint | Content |
|---|---|
| `choose_branch` | Explicit choice by the target modulo 9 |
| `four_preimages` | Four distinct antecedents at every period divisible by 9 |
| `core_fourfold` | Fourfold weighted amplification for every positive period divisible by 3 |
| `core_exponential` | Iteration for every natural depth parameter |
| `defect_exponential` | Application to actual Boolean-label errors |
| `two_step_test` | Stable versus exponential regime, distinguished after two compositions |
| `transfer_sharp` | Exact weight counts 1, 1, 4 at depths 0, 3, 4 |
| `fourfold_optimal` | Every universal four-step integer coefficient is at most 4 |
| `three_steps_insufficient` | Every universal three-step integer coefficient is at most 1 |

The namespace is `Collatz.PeriodicBranchEmbedding`. This module imports the
concurrently developed `PeriodicDefectTransport` definitions and transport
results. It does not import `PeriodicDefectAmplification`: that separate
workspace module proves amplification by transfer-weight certificates. The
two proofs share background definitions but use different main arguments.
The separate module's results are not claimed as code authored in this pass.

The source uses Lean core only. The axiom audit checks the actual theorem
dependencies: only standard Lean `propext`, `Quot.sound`, and, for the label
corollaries, `Classical.choice` occur. The exact sharpness calculation needs
no axioms. No unproved Collatz hypothesis is assumed.

## Novelty audit

The following primary sources were inspected on 28 September 2026. These are
specific comparisons, not a claim to have read the entire Collatz literature.

| Source and inspected material | Established overlap | Boundary of the present candidate |
|---|---|---|
| [Applegate and Lagarias, *Density Bounds for the 3x+1 Problem I: Tree-Search Method*](https://websites.umich.edu/~lagarias/doc/applegateI.pdf), introduction, §2 and four-step branching discussion | Pruned inverse trees, weights counting odd steps, uniform block-growth iteration, and branching within four steps | This is close prior art for the main mechanism. Our periodic weighted count is a different quantity, but its inequality may be an elementary consequence of this framework. The argument is not an improvement to their integer-preimage bounds. |
| [Monks, Monks, Monks and Monks, 2012](https://arxiv.org/html/1204.3904), introduction, §4.1, §5.2 and §6.1 | Pruning multiples of three, inverse arithmetic progressions and modular graphs | These foundations are prior art. The displayed uniform weighted four-step inequality was not found in the inspected material. |
| [Laarhoven and de Weger, 2013](https://www.deweger.net/papers/%5B52%5DLdW-CollBruijn-IndagMath%5B2013%5D.pdf), §2–3 and graph discussion | Collatz graphs at powers of two, line graphs, De Bruijn structure and path counts | Graph refinement and counting are prior art. Our bound concerns periods with a factor of three and weights away from multiples of three. |
| [Neklyudov, 2021/2022](https://arxiv.org/html/2106.11859), introduction, Proposition 4.2 and §5 | Coefficient pullback, expansive operators and transport of weighted arithmetic progressions | Composition and transfer operators are not new. This source prevents claiming the underlying operator as an invention. The present finite-period lower bound was not located. |
| [Alegría, Morales, Muñoz and Poblete, 2025](https://arxiv.org/html/2511.17650), §1.1–1.3 and §2.1–2.2 | Collatz coefficient pullback on sequence spaces, norm estimates and the adjoint | Another direct precedent for the operator viewpoint. No claim is made that error transport introduces this viewpoint. |
| [Karras and de Weger, 2026](https://arxiv.org/html/2601.15463v1), §2.1 and §2.6.4 | Modular indegrees and three-to-one odd-branch fibers when the modulus is divisible by three | The triple-preimage mechanism is known. The four selected branches and weighted iteration are an elementary use of that mechanism; absence of the exact theorem here does not establish priority. |
| [Reyes Jiménez, 2026](https://arxiv.org/html/2606.02621), §2 and §3.4 | Modulo-six graph paths, the component avoiding multiples of three, and residue-avoidance counts | The transient/core separation and graph counting are established ideas. This work uses a different counting question from periodic-label errors. |
| [Kohl, GAP RCWA documentation](https://stefan-kohl.github.io/rcwa/doc/chap7.html), §7.17 | Exact images and preimages of residue classes under powers of the accelerated map | Computational arithmetic-progression decomposition is prior art, not a novel device by itself. |

Targeted searches included combinations of `Collatz`, `periodic functions`,
`invariance defects`, `pullback`, `bounded`, `fourfold`, `four-step`,
`preimages`, `modular graph`, and `exponential growth`. No exact match for
the displayed theorem was located. Search-result absence is weak evidence:
the same statement could occur in another notation, an older source, or as
an unstated consequence of a known theorem.

**Novelty conclusion:** a checked candidate formulation and explicit proof,
with substantial known ingredients, including a close classical four-step
branching precedent. The broad device is not established as new; at most the
precise periodic-error formulation and explicit embedding remain candidates.
Historical priority and publishable
significance remain unverified. No external mathematical referee has reviewed
this result. Lean verifies the stated theorem, not its novelty or importance.

## Reproduction and validation

Run from the repository root:

```text
lake build Collatz.Strategy.PeriodicBranchEmbedding
lake env lean scripts/audit_periodic_branch_embedding.lean
python3 scripts/probe_periodic_branch_embedding.py
lake build Collatz
bash scripts/check_integrity.sh
git diff --check
```

The independent finite probe checks 7,650 explicit branch constructions,
the four-step fiber bound at all 100 positive periods divisible by 3 up to
300, and all 584 Boolean labels of periods 3, 6 and 9. These experiments
passed. Universal quantifiers are justified by the Lean proofs, not by the
finite probe.

Validation observed in this pass:

* Targeted build: **passed**, 71 jobs.
* New audit: **passed**, including 12 axiom-footprint checks and examples from
  both the stable and growing regimes.
* Existing periodic rigidity and variation audits: **passed**.
* Independent finite probe: **passed**.
* `git diff --check`: **passed**.
* Full repository build: **not completed/verified in this pass**. Shared
  repository-wide builds were rebuilding older large certificates. The new
  theorem's targeted build and import audit completed independently.
* Source-only execution of the repository integrity scan: **failed on the
  existing bibliography string** at
  `Collatz/Papers/Journal_10_5281_zenodo_18928635.lean:23`. The scanner matches
  the word `sorry` inside a quoted paper title. This is an observed false
  positive, not a proof hole in the new module. The full integrity workflow
  is consequently not reported as passing.

Recorded outputs are `PeriodicBranchEmbedding.build.log`,
`PeriodicBranchEmbedding.audit.log`, `PeriodicBranchEmbedding.probe.json`,
`PeriodicBranchEmbedding.rigidity-audit.log`,
`PeriodicBranchEmbedding.variation-audit.log`, and
`PeriodicBranchEmbedding.source-integrity.log` in this directory.
