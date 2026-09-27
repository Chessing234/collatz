# Sharp stability for periodic Collatz potentials

Status: proved in Lean core; a finite modular result. Historical novelty is
unestablished. This does not prove the Collatz conjecture or exclude an
unbounded orbit or a nontrivial positive cycle.

## Statement

Use the accelerated map T(n)=n/2 for even n and T(n)=(3n+1)/2 for odd n.
Let m>1 and let f : Nat -> Nat have period m. Write

- R = max f - min f (over one period),
- S = max_{1 <= r < m} f(r) - min_{1 <= r < m} f(r),
- V = sum_{0 <= n < 2m} |f(T(n))-f(n)|.

Then

    V >= R + S.

The Lean statement `variation_stability` is slightly more general: given
indices a,b,u,v with f(a) <= f(u),f(v) <= f(b) and u,v nonzero modulo m,

    V >= f(b)-f(a) + |f(u)-f(v)|.

Selecting indices attaining the two extrema gives the displayed range theorem.
There is no coprimality restriction on m and m need not be a least period.
The sum counts residue edges with multiplicity; it is not a time average along
an individual Collatz orbit.

## Exact and approximate equality

For nonconstant f, `optimal_iff` proves

    V = R  iff  3 divides m and f is constant on every nonzero residue.

Both directions are proved. The zero-residue value may lie above or below the
common value. `spike_variation` calculates the exact variation of these
potentials at all moduli: R if 3 divides m, and 2R otherwise.

`near_optimal_uniform` proves a quantitative repair statement: if V <= R+E,
then any two nonzero residues have values differing by at most E. In particular,
replacing their values by f(1), while retaining f(0) on the zero residue,
changes each value by at most E.

## Sharpness

For every natural H, take period six and the residue values

    r:     0  1  2  3  4  5
    f(r): 2H  0  0  H  0  0

Then R=2H, S=H and V=3H. The three nonzero edge contributions occur at
n=3,6,9 in [0,12), each with magnitude H. The family is checked symbolically
for arbitrary H by `stability_sharp`. Consequently neither coefficient in
R+S can be increased while retaining the other coefficient and requiring the
bound uniformly over all moduli. The stronger theorem `nested_spikes_variation` constructs the same equality
family at every modulus m divisible by six: set f(0)=2H, f(m/2)=H, and set
all other residue values to zero. It proves V=3H symbolically for arbitrary
m=2M with M>1 and 3 dividing M. Thus the strengthened inequality is sharp
at each such modulus.

## Proof mechanism and dependency boundary

For each threshold t between min f and max f, consider the Boolean cut
1_{f(n)>t}. Every nonconstant periodic cut has at least one defect. The existing
all-modulus one-defect classification says that a cut with exactly one defect
must separate zero from all nonzero residues. Therefore a threshold separating
two nonzero residues has at least two defects. Summing over thresholds counts
R mandatory defects plus S additional defects. Discrete coarea bounds this
sum by V. This uses and extends the repository's earlier `PeriodicDefectMinimum`
and `PeriodicSingleDefectAll` results; it is not an independent new proof of
those results.

This explains rigidity of nearly optimal periodic potentials. It does not
supply a decreasing potential along every orbit. In particular, summing
absolute edge changes supplies no sign information and no orbit distribution
estimate. Those gaps remain.

## Literature scope

The [novelty audit](PeriodicVariationNoveltyAudit.md) compares the exact
statement with modular-graph and graph-total-variation literature. Historical
novelty remains unverified. More specifically, the variation inequality is a
direct discrete-coarea consequence of the earlier one-defect classification;
it supplies no independent structural theorem beyond that classification.
The equality and near-equality results are corollaries. Priority for the
underlying all-modulus one-edge-cut classification remains unresolved.
This result should not be described as a breakthrough on global convergence.

## Reproduction

    lake build Collatz.Strategy.PeriodicVariationStability
    lake env lean scripts/audit_periodic_variation_stability.lean
    lake env lean scripts/audit_periodic_rigidity.lean
    bash scripts/check_integrity.sh
    git diff --check

The new theorem axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`; `stability_sharp` needs only `propext` and `Quot.sound`.
No Mathlib, admitted proofs, custom axioms, or native-decision trust shortcut
are used. The module is imported by the root `Collatz.lean`.

## Verification outcome for this change

- The new module and the root library build successfully.
- The new axiom audit and the existing periodic axiom audit pass.
- The repository integrity script completes its build, then stops on a false
  positive in a pre-existing bibliographic string in
  `Collatz/Papers/Journal_10_5281_zenodo_18928635.lean:23`. That string contains
  the words "axioms" and "sorry" in a paper title; the script strips comments
  but not strings. The whole integrity script therefore does not pass, and
  its later checks were not reached.
- Global `git diff --check` reports pre-existing whitespace in
  `Papers/README.md` and `Papers/index.md`. The changed root import passes the
  targeted whitespace check; the three new files have no trailing whitespace.
- Pre-existing files and edits are preserved, except for adding the new import
  to the already-modified root `Collatz.lean`.
