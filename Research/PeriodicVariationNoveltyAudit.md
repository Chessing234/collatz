# Novelty audit: periodic Collatz variation stability

Audit date: 2026-09-16.

## Verdict

Historical novelty is **not verified**. No exact prior statement of the
all-modulus inequality or one-defect classification was located in this audit.
That is a search outcome, not a priority claim.

The new variation module is a direct discrete-coarea corollary of the
repository's earlier all-modulus one-defect classification. Its equality and
near-equality conclusions are immediate consequences of that bound. It is
therefore inappropriate to describe this module as an independent structural
breakthrough on Collatz. The plausible mathematical novelty candidate is the
underlying classification of all one-edge cuts, whose priority remains open.
The Lean implementation is a concrete contribution to this checkout; no claim
that it is the first formalization worldwide has been established.

## Exact reduction: where any mathematical novelty must lie

Let G_m be the undirected multigraph obtained from the 2m directed residue
edges n mod m -> T(n) mod m, retaining multiplicities. Loops contribute zero.
Let W be the nonzero residues. For a vertex function f, define V as its edge
total variation, R as its full range, and S as its range on W.

The inequality V >= R+S for all natural-valued f is equivalent to these cut
bounds:

1. Every nonempty proper cut has at least one edge.
2. Every cut that separates two vertices of W has at least two edges.

Necessity: apply the inequality to a cut indicator. Its R is one. Its S is one
exactly when the cut splits W, and otherwise S is zero.

Sufficiency: for each integer threshold t, the indicator 1_{f>t} has a nonempty
proper cut for exactly R thresholds. It splits W for exactly S thresholds.
The elementary identity |x-y| = sum_t |1_{x>t}-1_{y>t}|, summed over edges,
gives V >= R+S. This is discrete coarea, not a new proof technique.

Thus the inequality is a numerical reformulation of connectivity plus the
absence of a one-edge cut splitting W. Combining this with the explicit
boundary size of {0} (one if 3 divides m, two otherwise) gives exactly the
prior one-defect classification.

For 3 not dividing m, the existing stronger bound V >= 2R already implies
V >= R+S, since S <= R. For 3 dividing m, the new term S records how many
threshold cuts fail to have the unique one-edge-cut shape. The equality
classification V=R and the consequence S<=E when V<=R+E add no independent
structural input. The nested-spike examples establish sharpness but do not
change this dependency assessment.

These are deductions made in this audit, not claims that the cited papers
state the exact Collatz inequality.

## Primary-source comparison

| Source inspected | Relevant content | What it does not establish for this audit |
| --- | --- | --- |
| Laarhoven and de Weger, *The Collatz conjecture and De Bruijn graphs*, arXiv:1209.3495, 2012; journal 2013, Section 2 | Modular residue graphs; dyadic De Bruijn identification and line-graph viewpoint | The inspected section does not state our arbitrary-modulus one-edge-cut classification or variation inequality |
| Monks, Monks, Monks and Monks, *Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph*, arXiv:1204.3904, 2012; journal 2013, Sections 3, 6, 7 | Affine permutation groups for moduli coprime to six; graph-based sufficiency criteria and dyadic folding | These results must not be conflated with a classification of every undirected one-edge cut at every modulus |
| Karras and de Weger, *Determinants of modular Collatz graphs and variants*, arXiv:2601.15463v1, January 2026, Sections 2.1, 2.4, 2.6 | Same residue-edge convention with multiplicity; indegrees; even-modulus reduction; three-to-one odd branch for odd moduli divisible by three | No exact one-edge-cut or total-variation classification was located in the inspected structural sections |
| Ben-Ameur, Bianchi and Jakubowicz, *Robust Consensus in Distributed Networks using Total Variation*, arXiv:1309.7264, 2013, Section III-C, Lemma 1 | Explicit graph coarea formula expressing total variation as an integral of cut perimeters | Supplies the general method, not the Collatz-specific cut bound |
| Chambolle, Giacomini and Lussardi, *Continuous limits of discrete perimeters*, ESAIM M2AN 44 (2010), 207-230, equations (1.4), (1.7), Section 3 | Generalized coarea and the relation to the established Lovasz extension | Confirms that lifting cut bounds to variation bounds is established methodology |

Links:

- [Laarhoven–de Weger](https://arxiv.org/html/1209.3495v1)
- [Monks et al.](https://arxiv.org/html/1204.3904)
- [Karras–de Weger](https://arxiv.org/html/2601.15463v1)
- [Ben-Ameur–Bianchi–Jakubowicz](https://arxiv.org/pdf/1309.7264)
- [Chambolle–Giacomini–Lussardi](https://www.numdam.org/article/M2AN_2010__44_2_207_0.pdf)

A source-scope caution: Lemma 3 in the inspected Karras–de Weger v1 states
strong connectivity without a modulus restriction, but its argument uses
inverses of both 2 and 3. It cannot justify that claim when 3 divides N:
for N=3 no nonzero vertex reaches zero. I therefore did not use its wording
as evidence that our multiple-of-three cut classification was already proved.
This observation concerns that particular statement and scope, not an audit
of the paper's determinant results.

## Search coverage and limits

Searches included combinations of Collatz/modular Collatz graphs with
edge connectivity, minimum cut, bridges, bridgeless, cut edges, one-edge,
single defect, total variation, periodic invariants and oscillation; the exact
Lean identifiers were also queried. Primary texts above were compared with
the local theorem statements rather than relying on titles or snippets.
Results about probability-measure total variation or the Collatz-Wielandt
formula concern different objects and were not treated as matches.

This was a targeted public-web and primary-source audit, not an exhaustive
MathSciNet/zbMATH review, full citation-network search, or external expert
assessment. No researcher was contacted. No numerical novelty probability is
justified. A future priority claim should focus on the all-modulus bridge
classification and obtain expert review of that exact statement.

## Defensible description

“A Lean-verified coarea consequence of an all-modulus classification of
one-defect periodic Collatz labels, including sharp examples and a uniform
near-equality estimate. Historical priority for the underlying classification
has not been established.”
