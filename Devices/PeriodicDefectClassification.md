# Single-defect rigidity for modular Collatz labels

Research note, 2026-09-14.

This note records a complete classification derived and formalized during this
session. It concerns all moduli, not a bounded computational experiment.
It is a candidate research contribution: the exact classification was not
located in the literature checks described below, but historical priority has
not been established. It does not prove the Collatz conjecture.

## The classification

Let

\[
T(n)=\begin{cases}n/2&n\text{ even},\\(3n+1)/2&n\text{ odd}.\end{cases}
\]

For a Boolean label \(f:\mathbb N\to\{0,1\}\) of period \(m>1\), define

\[
D_m(f)=\#\{0\le n<2m:f(T(n))\ne f(n)\}.
\]

**Theorem.** \(D_m(f)=1\) if and only if \(3\mid m\) and, for two distinct
labels \(A,B\),

\[
f(n)=\begin{cases}A&m\mid n,\\ B&m\nmid n.\end{cases}
\]

The unique defective input class is then \(n\equiv m\pmod{2m}\).

The endpoint is
[`one_defect_iff_all`](../Collatz/Strategy/PeriodicSingleDefectAll.lean).
The arithmetic statement uses equality to `f 0` and `f 1`, so no existence of
unspecified labels or ambiguity about their distinctness is hidden.

The theorem also classifies the bridges of the underlying undirected modular
multigraph: there are no bridges if \(3\nmid m\), and otherwise its sole bridge
is the transition indexed by \(m\), separating the zero vertex from all other
vertices. Parallel edges are counted separately and loops are retained. The
Lean endpoint is the equivalent label/cut formulation, rather than a graph
library definition of a bridge.

## Exact minimum and a sharp inequality

The classification is accompanied by an optimization theorem:

\[
\min_{f\text{ nonconstant, of period }m}D_m(f)
=c_m:=\begin{cases}1&3\mid m,\\2&3\nmid m.\end{cases}
\]

This is [`minimum_defects`](../Collatz/Strategy/PeriodicDefectMinimum.lean).
The divisibility indicator attains the minimum for every \(m>1\), and its
least positive period is exactly \(m\).

For any natural-number-valued periodic potential \(F\), the same module proves

\[
\sum_{0\le n<2m}|F(T(n))-F(n)|\ \ge\ c_m(F(b)-F(a))
\quad\text{whenever }F(a)\le F(b).
\]

Thus the total variation is at least \(c_m\) times the oscillation of \(F\).
Every nonnegative integer height is attained sharply by
\(F(n)=H\mathbf 1_{m\mid n}\). The formal endpoints are
`variation_lower_bound` and `variation_sharp`. These statements are formalized
for natural-valued potentials; this note does not claim a Lean theorem for
arbitrary real-valued functions.

## Proof of the minimum and variation bound

A periodic invariant is constant, as proved in
[the earlier rigidity module](../Collatz/Strategy/PeriodicRigidity.lean).
Therefore a nonconstant label has at least one defect. The defect predicate
has period \(2m\), because shifting the input by \(2m\) shifts the output by
\(m\) or \(3m\).

When \(3\nmid m\), the odd-edge target map
\(i\mapsto3i+2\pmod m\) is a permutation. The even-edge targets run through all
residues as well. Hence, for any numerical residue label, its sum over all
edge sources equals its sum over all edge targets. For a Boolean label this
means the number of entries into its support equals the number of exits.
Consequently its defect count is even, and a nonconstant label has at least
two defects. This is formalized as `mass_conservation`, `entries_eq_exits`,
and `defects_twice_exits`.

The zero-residue indicator has exactly one exiting edge, indexed by \(m\).
When \(3\mid m\), there is no odd edge entering zero and its total defect
count is one. Otherwise conservation supplies exactly one entering edge too.

For the numerical inequality, apply the Boolean bound to the threshold
labels \(\mathbf1_{F(a)+t<F(n)}\), for
\(0\le t<F(b)-F(a)\). Each is nonconstant. A given edge changes at no more
thresholds than the absolute difference between its endpoint values.
Interchanging two finite sums gives the result. The integer coarea identity
is separately proved as `threshold_sum`.

## Why a single defect is rigid

The classification requires more than the lower bound. Its proof has two parts.

**Odd moduli.** Doubling is a permutation modulo an odd modulus. A periodic
label with a single defective edge must be invariant under doubling: a cycle
of that permutation cannot contain exactly one change of label. Formally,
we use a positive power of 2 congruent to 1 and show that, after the alleged
unique change, the old label could never be recovered.

Now write \(m=3h\). Doubling invariance turns the odd branch into the affine
identity \(f(3n+1)=f(n)\), with one exceptional residue \(d\). The three inputs
\(d,d+h,d+2h\) have the same affine image modulo \(m\). The last two are
regular, so they have the same label; the label at \(d\) differs. Doubling
preserves this pattern, making \(2d\) the unique exceptional member of another
three-element fiber. Since there is only one exceptional residue globally,
\(2d\equiv d\pmod m\), forcing \(d=0\).

Replace the label at zero by the label at 1. The resulting label is invariant
under both branches, hence constant by periodic rigidity. Therefore every
nonzero residue originally had the label of 1. The actual odd defective input
class is \(m\pmod{2m}\). These steps are formalized in
[`PeriodicSingleDefect.lean`](../Collatz/Strategy/PeriodicSingleDefect.lean).

**Even moduli.** Write the modulus as \(2M\). An input class modulo \(2M\)
represents an edge of the graph at modulus \(M\). Two such edges are composable
precisely when an actual input modulo \(4M\) realizes their transition. The
explicit arithmetic lift is `composable_lift`.

Suppose the label on these edges has just one changing transition
\(e_0\to e_1\). At each lower vertex there are two outgoing edges. Choose one
different from \(e_1\). Every incoming edge must share its label. This makes
the label of an incoming edge depend only on its target vertex. Define the
induced vertex label using the canonical incoming even edge:

\[
g(v)=f(2(v\bmod M)).
\]

The only defect of \(g\) is the lower edge \(e_1\). Induction on the modulus
therefore identifies \(e_1=M\), and all nonzero lower vertices have one label.
When \(3\mid M\), the only lower edge entering zero is its zero loop. It
follows that the only exceptional upper vertex is also zero, and the unique
upper defective input is \(2M\). This proves the even case without a bound
on the number of factors of 2. The formal reduction is
`descend_single_defect`, followed by `all_single_defect`.

## Experiments and verification

The bridge pattern was first tested with
[`modular_defect_probe.py`](../scripts/modular_defect_probe.py), retaining
parallel edges and comparing every modulus from 2 through 2,000. It found
no counterexamples. This finite experiment motivated the proof; it is not
used as a premise of any theorem. The all-modulus classification above now
replaces that experimental conjecture with a checked statement.

All four Lean modules are imported by the main library. Verification commands:

```sh
lake build Collatz
lake env lean scripts/audit_periodic_rigidity.lean
bash scripts/check_integrity.sh
git diff --check
```

The dedicated audit covers 23 endpoints across the rigidity, minimum,
variation, and classification proofs. Their foundational dependencies are
subsets of `propext`, `Quot.sound`, and `Classical.choice`. No conjecture,
experimental result, additional axiom, `sorry`, or `native_decide` is used.

## Prior work, novelty, and limits

The framework is classical. [Laarhoven and de Weger (2012)](https://arxiv.org/abs/1209.3495)
study modular Collatz graphs and their binary De Bruijn structure.
[Monks et al. (2012)](https://arxiv.org/abs/1204.3904) study modular graph
structure, groups, and sufficient sets. [Karras and de Weger (2026)](https://arxiv.org/abs/2601.15463)
study determinants and the structure of modular Collatz graphs, including
the three-to-one affine fibers for odd moduli divisible by 3. The elementary
fiber structure and the modular graph viewpoint are not claimed as new.

The exact defect minimum is a short consequence of rigidity and conservation.
The more substantive candidate contribution is the complete single-defect
classification, particularly the argument transporting a unique exceptional
fiber under doubling and the reduction between successive even moduli.
Targeted searches and the inspected sources did not reveal this exact
classification or the stated sharp variation inequality. That is evidence
for further novelty review, not proof of historical priority.

The earlier equivalence between Collatz and eventual periodicity of its basin
is also a consequence of stronger known work: [Kenneth M. Monks (2006)](https://monks.scranton.edu/files/pubs/SufficiencyRev4.pdf)
proved that every arithmetic progression is sufficient. This equivalence
should be treated as a formalization/corollary, not as the novel contribution.

These results solve an extremal question about finite residue models. They do
not exclude an infinite positive orbit that never reaches 1, do not exclude a
nontrivial integer cycle, and do not justify transferring statements about
residue graphs to individual infinite trajectories. A breakthrough on the
conjecture itself remains unestablished.
