# Two-defect rigidity for odd modular Collatz graphs

Date: 2026-09-28.
Status: kernel-checked structural theorem; candidate mathematical novelty after a bounded prior-art search. Not a proof of the Collatz conjecture. Historical priority and independent expert review remain unestablished.

## The theorem

Use the accelerated map

\[
T(n)=\begin{cases}n/2,&n\text{ even},\\(3n+1)/2,&n\text{ odd}.\end{cases}
\]

Let \(m>0\) be odd and divisible by 3. Let \(f\) be any periodic label of period \(m\), taking values in any type. Count the input residue classes \(0\le n<2m\) for which \(f(T(n))\ne f(n)\).

**There are exactly two defective input classes if and only if \(9\mid m\) and there are distinct labels \(A,B\) such that**

\[
f(n)=\begin{cases}
B,&n\equiv m/3\text{ or }2m/3\pmod m,\\
A,&\text{otherwise}.
\end{cases}
\]

**The two defective input classes are exactly**

\[
n\equiv m/3,\quad 5m/3\pmod{2m}.
\]

The formal parameterization is \(m=3h\), with \(h>0\) and \(3h\) odd. The arithmetic condition in Lean is `h % 3 = 0`. The labels in the conclusion are explicitly `f h` and `f 1`, whose inequality is proved. The theorem assumes neither doubling invariance nor a bound on the modulus. No convergence hypothesis is used. The given period need not initially be a least period.

Examples: at modulus 9 the exceptional vertices are 3 and 6 and the error inputs modulo 18 are 3 and 15. At modulus 27 the exceptional vertices are 9 and 18 and the error inputs modulo 54 are 9 and 45. At moduli 3, 15, 21, 33, and every odd multiple of 3 not divisible by 9, there is no two-defect label.

For Boolean labels this classifies bipartitions whose edge boundary has size exactly two in the modular multigraph. Parallel edges are counted separately and loops never cross a cut. This is **not** a classification of all pairs of edges whose deletion disconnects the graph: such a pair could contain an already existing bridge and an unrelated edge.

## Formal endpoints

- `Collatz.PeriodicTwoDefectOdd.two_defect_classification`: the complete equivalence, with precisely two distinct defective residue classes expressed by an existential pair and an exact biconditional for every natural input.
- `Collatz.PeriodicTwoDefectOdd.positions_of_two`: the explicit input classes directly from the two-defect hypothesis.
- `Collatz.PeriodicTwoDefectOdd.exists_two_iff_nine`: a Boolean two-defect label exists exactly when the odd modulus is divisible by nine. This also establishes uniform attainability.
- `Collatz.PeriodicTwoDefectOdd.doubling_invariant`: doubling invariance follows from the two-defect hypothesis.
- `Collatz.PeriodicTwoDefect.two_defects_iff_all`: the intermediate affine classification under doubling invariance.

Sources: [affine proof](../Collatz/Strategy/PeriodicTwoDefect.lean), [Collatz proof](../Collatz/Strategy/PeriodicTwoDefectOdd.lean), [audit](../scripts/audit_periodic_two_defect.lean).

The main theorem formalizes “exactly two” by specifying both distinct residue classes and proving that they exhaust the defect predicate. It does not use an unexplained graph library cardinality. A separate concrete test evaluates the repository's `defectCount` at modulus 9 and obtains 2 in the kernel.

## Proof mechanism

1. **Eliminate even defects.** A label cannot change exactly once around a doubling cycle. Thus if there were an even defect, both defects would have to be even. With all odd edges preserving the label, the three-to-one odd branch forces period \(m/3\). Every defect would then repeat in three distinct classes modulo \(2m\), contradicting the budget of two. Consequently \(f(2n)=f(n)\) everywhere.

2. **Pass to the affine branch.** On odd inputs, doubling invariance identifies a Collatz defect with \(f(3n+1)\ne f(n)\). Because the modulus is odd, each input residue modulo \(m\) has exactly one odd lift modulo \(2m\). The two Collatz errors therefore become two distinct affine errors.

3. **Put both errors in one fibre.** Write \(m=3h\). The inputs \(d,d+h,d+2h\) have the same affine image. If the two errors lay in different fibres, each would be the unique differently labelled point in its fibre. Doubling transports this configuration. If a transported exceptional point were regular, both its mates would have to be defective, contradicting their assumed placement in different fibres. The two exceptional residues would thus form a doubling-invariant two-element set. For an odd modulus this forces the pair \(\{h,2h\}\), which lies in a single fibre: a contradiction.

4. **Locate that fibre.** In the unique nonuniform fibre, a defective point differs from a regular mate. Doubling preserves that inequality, so the doubled fibre must again be the unique nonuniform fibre. Its residue modulo \(h\) is fixed by doubling and hence is zero. The possible errors are now among \(0,h,2h\). Since \(f(h)=f(2h)\), their affine-defect statuses agree. Exactly two errors therefore means precisely \(h,2h\).

5. **Force divisibility by nine.** Set \(g(n)=f(3n+1)\). It has period \(h\) and is doubling-invariant. Its only possible changes along the affine branch go *to* \(f(1)\). If \(3\nmid h\), the Boolean indicator of \(g(n)=f(1)\) is a forward-closed label on a balanced modular graph. The repository's mass-conservation theorem makes entries equal exits. There are no exits, so there are no defects, and periodic rigidity makes the indicator constant. But one of \(h,2h\) is \(1\pmod3\), providing a preimage with value \(f(h)\ne f(1)\). This contradiction proves \(3\mid h\).

6. **Repair the two points.** Now the affine image never enters \(h\) or \(2h\), since both are divisible by 3. Replacing their labels by \(f(1)\) produces a label invariant under both branches. Existing periodic rigidity makes it constant. Thus the original label has exactly the displayed form.

7. **Prove the converse and recover edge positions.** Doubling swaps the two exceptional classes, while the affine branch leaves their union and never enters it. There are precisely two errors. Their odd lifts modulo \(6h\) are \(h\) and \(5h\).

The fibre-transport argument and the forced period reduction are the substantive classification steps. Existence of the displayed example alone is elementary and is not the candidate novelty claim.

## Prior-art audit and limits

The closest inspected sources were:

- [Karras and de Weger, *Determinants of modular Collatz graphs and variants* (2026), §§2.1, 2.4, 2.6–2.7](https://arxiv.org/html/2601.15463v1). This supplies degree counts, loops, multiple edges, connectivity, permutation descriptions, and the three-to-one odd-branch fibres. Those ingredients are prior art. The inspected sections do not state the exhaustive two-defect classification above.
- [Monks, Monks, Monks, and Monks, *Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph* (2012), §§6.1–6.2](https://arxiv.org/html/1204.3904). Proposition 6.1 describes the colored modular graphs and their branch cycles and trees. Proposition 6.2 studies vertex deletion and sufficient sets. These are related graph tools, not the two-edge-boundary classification proved here.
- [Laarhoven and de Weger, *The Collatz conjecture and De Bruijn graphs* (2012)](https://arxiv.org/html/1209.3495). Its principal finite-graph classification concerns powers of two. Its generalizations also explain why finite graph structure by itself need not distinguish the convergence behavior of different affine maps.

Additional discovery searches included `Collatz modular graph minimum edge cut`, `Collatz two-edge`, `Collatz two defects`, `Collatz edge cuts`, `Collatz cutsets`, and `modular Collatz graphs connectivity cuts bridges`. Search results included unrelated graph theory, repository reports, and unverified claimed Collatz proofs. Those were not treated as mathematical evidence. The 2009 Laarhoven thesis was additionally screened at its contents and modular-graph introduction; this was not a full thesis review. One older presentation link could not be fetched and is not counted as inspected evidence.

**Novelty verdict:** new to this checkout, and the exact classification was not found in the inspected primary-source sections or targeted discovery searches. It is a **candidate new structural theorem**, not verified historical priority. The elementary building blocks are known. No external mathematician has reviewed this proof or novelty claim in this session. A literature search cannot establish that a theorem has never appeared under another formulation or as an unstated corollary.

## What this does and does not solve

It resolves the two-defect classification for all odd moduli divisible by three, extending the checkout's earlier one-defect classification. It identifies the next possible small boundary after the zero-residue bridge.

It does not cover even moduli or odd moduli coprime to three. It does not exclude nontrivial positive integer cycles or divergent integer trajectories. No reduction from either missing Collatz assertion to this finite classification has been proved. Accordingly this is not an established breakthrough on the conjecture itself.

## Verification

Lean version: `leanprover/lean4:v4.33.0-rc1`, core-only project.

The targeted build and dedicated axiom audit pass. The inspected theorem footprints are subsets of `propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms, admissions, `sorry`, `native_decide`, or Mathlib imports in the new modules.

The independent [probe](../scripts/two_defect_probe.py) enumerates all size-two bipartition boundaries by deleting each edge and finding bridges in the resulting multigraph. For the 51 odd multiples of three from 3 through 303, every answer agrees with the theorem; [results](PeriodicTwoDefectProbe.json). These finite computations are not premises of the proof.

Commands:

```sh
lake build Collatz.Strategy.PeriodicTwoDefectOdd
lake env lean scripts/audit_periodic_two_defect.lean
python3 scripts/two_defect_probe.py --max-modulus 303
bash scripts/check_integrity.sh
git diff --check
```

Repository-wide proof-escape scan: reproduced the existing false positive at
`Collatz/Papers/Journal_10_5281_zenodo_18928635.lean:23`. The matched token occurs
inside a bibliographic citation string, not a proof. The scanner strips comments
but not string literals. This file was not modified. No other matches were found.

Final verification status:

- New-module build: passed (72 build jobs including dependencies).
- Dedicated audit: passed, including ten axiom-footprint checks and the concrete
  modulus-9 and modulus-15 examples; [axiom output](PeriodicTwoDefectAxioms.txt).
- Existing periodic-rigidity regression audit: passed after its targeted dependency
  build (71 jobs). An initial attempt lacked a built dependency; that was resolved
  by the targeted build, not by changing any theorem.
- Independent finite probe: 51 moduli checked, zero discrepancies.
- `git diff --check` and whitespace checks on the new files: passed.
- Full-library build: **not completed**. The first run was interrupted under
  resource pressure. A retry with `LEAN_NUM_THREADS=2` was also stopped while
  rebuilding expensive pre-existing numerical certificates. No full-library
  success is claimed. All build processes started for these broad attempts were
  stopped; no continuing background verification is implied.
- Repository-wide integrity: **not green**. In addition to the incomplete broad
  build, its proof-escape scan independently reproduces the citation-string false
  positive described above. The new modules are not implicated in that match.

The main library now imports the new result. Mathematical verification here is
supported by the completed targeted builds and audits, not by a claimed successful
rebuild of every unrelated module in the repository.

Workspace boundary: `Collatz/Strategy/PeriodicTwoDefectAll.lean` appeared
concurrently during the final status check. It was not created or edited in this
work, is not imported by this change, and is excluded from these verification
and novelty claims. The completed result reported here remains the odd-modulus
classification.
