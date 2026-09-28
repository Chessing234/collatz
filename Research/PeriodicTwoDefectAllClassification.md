# Two-defect rigidity at every modulus divisible by three

Date: 2026-09-28.

**Status:** the classification and sharp bound below are proved in Lean. They are new to this checkout beyond its pre-existing odd-modulus theorem. A targeted literature review did not locate the exhaustive classification, but historical priority is **not established**. This is a finite structural result, not a solution of Collatz or an established breakthrough on convergence.

## Exact theorem

Use the accelerated Collatz map

\[
T(n)=\begin{cases}n/2&n\text{ even},\\(3n+1)/2&n\text{ odd}.\end{cases}
\]

Let \(m>0\) be divisible by three, and let \(f\) be a label with period \(m\). For Boolean labels write

\[
D_m(f)=\#\{0\le n<2m:f(T(n))\ne f(n)\}.
\]

**Classification.** There are exactly two defective input classes if and only if the label has one of the following forms, with two distinct values \(A,B\):

| Condition | Residues with value A modulo m | All other residues | Defective inputs modulo 2m |
|---|---|---|---|
| \(6\mid m\) | \(0,m/2\) | B | \(m/2,3m/2\) |
| \(9\mid m\) | \(m/3,2m/3\) | B | \(m/3,5m/3\) |

Both families exist when \(18\mid m\). There are no two-defect labels at odd multiples of three not divisible by nine. No bound on \(m\), its prime factors, or its power of two is imposed. The statement is also proved for labels valued in any Lean `Type`, using an exact residue-pair predicate in place of a Boolean sum. In particular, the two-defect hypothesis itself forces the label to take just two values.

**Least-period refinement.** The first family has period \(m/2\), so it disappears if \(m\) is required to be the least positive period. The second family has least positive period exactly \(m\). Thus, at the least period, there is a single possible family, and it exists exactly at multiples of nine, even or odd.

The first family is a repeated one-defect label at a smaller period. Its existence is not the substantive discovery. The substantive extension is the proof that no other patterns emerge through an arbitrary number of modulus doublings.

## Sharp separation bound

For every \(m>0\) divisible by three, every period-\(m\) Boolean label satisfying

\[
3\nmid a,\quad 3\nmid b,\quad f(a)\ne f(b)
\]

obeys

\[
\boxed{D_m(f)\ge 3.}
\]

This is sharp **for every such modulus**: the label \(f(n)=\mathbf1_{n\equiv1\pmod m}\) distinguishes 1 and 2 and has defective input classes exactly \(1,2,m+1\pmod{2m}\).

These are cuts in the full modular multigraph, with parallel edges counted separately. This does not assert an edge-connectivity value for the induced graph after deleting multiples of three. Nor does it classify arbitrary pairs of deleted edges, which might include a bridge and an irrelevant edge.

## Proof of the new even-modulus step

Write the upper modulus as \(2M\), with \(3\mid M\). View its vertices as the input-indexed edges of the graph modulo \(M\). The existing arithmetic `composable_lift` theorem realizes every pair of composable lower edges by an upper transition. The new proof uses this explicit arithmetic fact, not an unproved graph identification.

At each lower vertex \(v\), the two outgoing edges have indices \(v\) and \(v+M\). If \(v\not\equiv2\pmod3\), it has one incoming edge. If \(v\equiv2\pmod3\), it has four incoming edges; the proof explicitly constructs three, which is enough. All incoming/outgoing combinations are upper transitions.

Assume only two upper transitions change labels.

1. **A vertex with at least three incoming edges cannot have different outgoing labels.** If its two outgoing labels differed, every incoming edge would disagree with at least one, giving at least three distinct changing transitions.
2. **A nonuniform incoming fibre forces smaller period.** Suppose two incoming edges at \(v\) have different labels. Each outgoing edge disagrees with at least one of them, consuming both allowed changes at \(v\). Hence no other vertex has an outgoing split. The split is also impossible at \(v\), by step 1. Therefore \(f(v)=f(v+M)\) everywhere, so \(f\) has period \(M\). Its two upper defects are repetitions of exactly one lower defect. The pre-existing all-modulus one-defect classification gives the half-modulus family.
3. **Uniform incoming fibres descend through T.** Otherwise define \(g(v)\) as the common incoming label, using the canonical even incoming edge. Then \(f(n)=g(T(n))\). Each upper error maps to a lower error, and every lower error lifts along the canonical even edge. Thus there are at most two lower errors. If there were only one, the existing one-defect theorem places it at input class \(M\); that target has a unique incoming upper edge, contradicting the existence of two distinct upper errors. Consequently \(g\) has exactly two errors.
4. **Induct on the modulus.** Apply the classification at \(M\). Pulling either classified pattern back through \(T\) again yields one of the same two families, because their exceptional vertices are divisible by three and have unique even preimages.

At odd moduli, the proof imports the checkout's existing `PeriodicTwoDefectOdd.two_defect_classification`. This dependency is essential and is not work newly produced in this task. That theorem itself relies on fibre transport, doubling rigidity, and the earlier periodic invariant theorem.

For the sharp bound, zero defects force constancy, one defect only separates the zero residue, and the classification above shows that two defects cannot distinguish any two nonmultiples of three. The singleton-one label supplies the matching upper bound.

## Formal endpoints

Source: [PeriodicTwoDefectAll.lean](../Collatz/Strategy/PeriodicTwoDefectAll.lean).

- `descent_dichotomy`: the new modulus-halving mechanism.
- `two_defect_classification`: complete equivalence for arbitrary labels, assuming positive period divisible by three.
- `count_eq_two_iff`: equivalence of the exact residue-pair formulation with the repository's actual Boolean `defectCount`.
- `counted_classification`: the counted theorem.
- `exists_two_iff`: existence precisely when \(6\mid m\) or \(9\mid m\), under \(3\mid m\).
- `half_shape_positions`, `third_shape_positions`: exact error locations.
- `third_shape_least_period`, `least_period_classification`: the primitive-period refinement.
- `two_defects_constant_off_three`: constant labels on all integers not divisible by three.
- `sharp_core_minimum`: lower bound three and an attaining witness for every admissible modulus.

The module is imported by `Collatz.lean`. It adds no dependency on Mathlib and no assumptions about convergence, finite computation, or published Collatz bounds.

## Prior-art audit

The review on 2026-09-28 inspected the following primary-source material:

1. [Karras and de Weger, *Determinants of modular Collatz graphs and variants*, arXiv:2601.15463v1](https://arxiv.org/html/2601.15463v1), especially §§2.1, 2.4, 2.6.1, 2.6.3–2.6.4. The degree counts, two outgoing edges, unique even predecessors, odd-branch fibres, and modulus-doubling matrix structure are known. Those facts are not novelty claims here. The inspected sections do not give the exhaustive two-error classification or the modulus-halving dichotomy for cut labels.
2. [Monks, Monks, Monks, and Monks, *Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph*, arXiv:1204.3904](https://arxiv.org/html/1204.3904), §6.1, Proposition 6.1, and §6.2, Proposition 6.2. These give modular branch structure and criteria using vertex deletion and surviving directed cycles. They do not state the two-edge-boundary classification inspected here.
3. [Laarhoven and de Weger, *The Collatz conjecture and De Bruijn graphs*, arXiv:1209.3495](https://arxiv.org/html/1209.3495), the introduction and §2. The power-of-two De Bruijn correspondence and modular viewpoint are prior art. Our moduli are multiples of three, so a theorem exclusively about binary De Bruijn graphs is not automatically this theorem.
4. The primary paper *The Restricted Edge-Connectivity of de Bruijn Undirected Graphs* was screened through its [indexed PDF text](https://citeseerx.ist.psu.edu/document?doi=7e8047c167e0eba4e1efa28c3d3421987ef995b2&repid=rep1&type=pdf), and the line-digraph chapter by Xu was screened through its [indexed excerpt](https://staff.ustc.edu.cn/~xujm/Chapter17_06.pdf). These concern different graph families or cuts/connectivity notions, and the latter excerpt assumes a balanced digraph. The modular graphs at multiples of three are not balanced. This was an excerpt review, not a complete review of either work.

5. [Laarhoven, *The 3n + 1 conjecture*, bachelor thesis (2009)](https://thijs.com/docs/bsc09-thesis.pdf), contents, modular-graph introduction (§4.1.1), and line-digraph definitions and lemmas (§4.1.3). The text explicitly specializes to powers of two after the introduction. Full-text keyword searches for “cut” and “connectivity” returned no matches in the extracted PDF. The thesis was screened, not reviewed in full.

Search formulations included: `Collatz modular graphs minimum edge cuts two edge connectivity`, `Collatz periodic invariant functions rigidity modular graph cuts`, `"Collatz" "edge connectivity"`, `"Collatz" "two-edge"`, `"Collatz" "edge cut"`, `"Collatz" "restricted edge"`, `"Collatz" "two-defect"`, `"Collatz" "edge boundary"`, and `"line digraph" "edge cuts" degree`.

A result using “two-defect” in a width-two survivor/carry system also appeared. Its indexed abstract describes a different defect parameter and character-sum problem; it was not treated as evidence for or against the graph-cut classification. Search hits making unverified global Collatz claims were not used as mathematical premises.

**Verdict:** no exact prior statement was found in this bounded search and the inspected sections. The theorem is a candidate structural contribution. Absence from these sources is not proof of historical priority; equivalent formulations, unpublished results, and unstated consequences remain possible. There has been no external expert review in this task. The sharp bound and least-period statement are consequences of the classification, not separate claims of major novelty.

## Relation to the Collatz conjecture

The result describes how small an edge boundary can be in a finite residue model and exactly where the two smallest nonzero boundaries can lie. It improves the checkout's prior lower bound for labels separating nonzero residues from two to three when both integers are nonmultiples of three.

It does not supply a decreasing unbounded potential, exclude a nontrivial positive cycle, or exclude a divergent trajectory. The density of defective input classes among integers does not imply that every Collatz orbit visits them. No missing bridge from this finite classification to global convergence has been proved.

## Reproduction and evidence

Lean: `leanprover/lean4:v4.33.0-rc1`.

```sh
lake build Collatz.Strategy.PeriodicTwoDefectAll
lake env lean scripts/audit_periodic_two_defect_all.lean
lake env lean scripts/audit_periodic_rigidity.lean
python3 scripts/two_defect_all_probe.py --max-modulus 303
bash scripts/check_integrity.sh
git diff --check
```

The new audit checks theorem axiom footprints, evaluates both families directly using the original Collatz map, tests an excluded candidate, and instantiates the nonexistence and least-period results. The finite probe checks every multiple of three through 303 by edge deletion and multigraph bridge enumeration, with a separate enumeration of all Boolean partitions modulo complementation for moduli 3, 6, 9, 12, 15, and 18. It also checks every displayed defect location and the sharp singleton-one witness. These experiments are not assumptions in Lean.

Evidence files:

- [Targeted build](PeriodicTwoDefectAllBuild.txt)
- [Theorem axiom audit](PeriodicTwoDefectAllAxioms.txt)
- [Existing periodic theorem regression audit](PeriodicTwoDefectAllRegression.txt)
- [Independent finite checks](PeriodicTwoDefectAllProbe.json)
- [Repository integrity run](PeriodicTwoDefectAllIntegrity.txt)

The targeted build, all 20 axiom footprints and audit examples, existing periodic regression audit, all 101 finite cases, and `git diff --check` have passed. The targeted build and axiom audit were also rerun successfully after the request to prove the full conjecture. The full-repository integrity run was interrupted before completion; its saved output is a partial log, not evidence of a successful full-repository check.

The subsequent examination of the missing global step is recorded in [FullConjectureAttempt.md](FullConjectureAttempt.md). No proof of the Collatz conjecture has been obtained.
