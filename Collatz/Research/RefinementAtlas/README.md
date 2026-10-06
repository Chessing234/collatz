# Sharp refinements and bounded adaptive descent

This extends the repository's existing descent atlas. It does **not** prove
universal descent or the Collatz conjecture. No claim of literature-level
novelty is made: these are additional formal consequences and computational
certificates within this project.

## Established results guiding the search

* **Terras (1976), independently Everett (1977):** the positive integers whose
  orbits eventually drop below their starting values have natural density one.
  This permits an exceptional set of density zero; universal descent requires
  ruling out every exception. See [Lagarias's survey, stopping times](https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/node4.html).
* **Krasikov–Lagarias (2003):** difference inequalities and computer-aided proof
  give at least x^0.84 integers below x whose forward orbits contain 1, for
  sufficiently large x. This counts convergence to 1, rather than merely a
  decrease below the initial state. See [the original paper](https://arxiv.org/abs/math/0205002).
* **Tao (2019; published 2022):** for every function f(N) tending to infinity,
  almost every positive starting integer in logarithmic density has an orbit
  minimum below f(N). This does not establish convergence to 1 or a uniform
  bound on all orbit minima. See [the original paper](https://arxiv.org/abs/1909.03562).
* **Barina (2025):** published computational verification extends convergence
  below 2^71. This is a finite verification result, not an infinite theorem.
  See [the author's project](https://pcbarina.fit.vut.cz/) and
  [the publication record](https://www.fit.vut.cz/research/result/c197809/.en).

Those four large results are researched context, **not newly formalized here**.
The Lean modules below formalize exact local arithmetic and an obstruction to
one family of universal-descent techniques.

## Exact cutoff transport

Use the repository's half-step map T(n)=n/2 for even n and (3n+1)/2 for odd n.
This is not the odd-only Syracuse map. On a cylinder n=2^k*m+r,

    T^k(n) = 3^a*m+b,
    a = oddCount r k,  b = T^k(r).

When g=2^k-3^a>0, strict descent is exactly b<g*m+r. The existing
`DescentAtlas.threshold` is the least successful m. Write this threshold as t.
Refining the class index to s*m+q, with s>0, gives the exact transported cutoff

    C(t,s,q) = 0                        if t <= q,
               (t-q-1)/s + 1            otherwise.

Division here is natural-number division. `Transport.lean` proves the sharp
criterion, the zero-cutoff characterization, and the composition law

    C(C(t,s,q),u,v) = C(t,s*u,s*v+q).

The law is useful when a residue search refines in multiple stages: its final
exception threshold is independent of whether those stages are fused.

## Exception conservation

For canonical refinement digits 0<=q<s, write t=s*u+v with 0<=v<s.
`Histogram.lean` proves

    C(t,s,q) = u+1  if q<v,
               u   otherwise.

Every two subcylinders therefore differ by at most one exceptional index.
Summing over the digits gives exactly t. This is a precise limitation of
resolution-only refinement: it partitions the original finite exceptions,
while stronger orbit information is needed to discharge them. Here an
"exception" means failure of strict descent **at the specified horizon**;
it does not mean failure of eventual convergence.

For t=1, every nonzero digit clears the exception, and the zero digit retains
one. `Core.lean` proves this specialization directly.

## Bounded adaptive rank obstruction

`AdaptiveObstruction.lean` constructs, for any m>0 and K>0,

    n = 2^K*(2*m)-1 > 1.

For every 1<=j<=K it proves

    T^j(n)+1 = 3^j*2^(K-j)*(2*m),
    T^j(n)>n,  T^j(n) mod m = n mod m.

Thus a rank nondecreasing with the integer inside each residue class cannot
strictly decrease on all inputs, even when a stopping rule examines the entire
integer and chooses any positive horizon bounded by K. This includes every
natural-valued rank a*n+correction(n mod m), with nonnegative a.

The theorem makes no claim about unbounded stopping rules, about ranks that
can decrease within a residue class, or about arbitrary Collatz potentials.
It supplies a necessary design constraint, not a counterexample to Collatz.

## Certificates and experiments

The generator produces 300 batches, each containing three distinct contracting
base cylinders and seven proved facts per cylinder: exact parity/endpoint data,
positive gap, sharp cutoff, two refined endpoint formulas, the zero-digit sharp
cutoff, and unconditional descent in the nonzero digit. It includes every
positive-cutoff cylinder in its depth-2-through-12 census before choosing other
cylinders. The selected cylinders have cutoff zero or one; each such fact is
checked by Lean, rather than inferred from a numerical trend.

These generated files are a certificate atlas, not 300 independent mathematical
ideas. `verification.json` records every selected cylinder and file hash.
`experiments.json` records independent dynamics tests, deterministic arithmetic
and histogram tests, and a complete canonical-residue census through depth 18.
In that finite census every observed contracting cutoff is at most one. That
observation is not asserted for all depths and is not a hypothesis in any proof.

The Python tests and the Lean kernel check serve different purposes: Python
finds and cross-checks candidates; ordinary Lean `decide` proves their closed
numerical facts. No `native_decide`, unfinished proof, or new axiom is used.

## Reproduce

From the repository root:

```sh
python3 scripts/refinement_atlas.py
python3 scripts/test_refinement_transport.py
python3 scripts/audit_refinement_atlas.py
```

The optional `--commit` flag on the generator commits each batch only after its
Lean check succeeds. It stages only the generator's explicitly named files.
The audit builds the aggregate module and prints axiom dependencies for every
public theorem in this atlas. Its report is `audit.json`; full diagnostic
outputs are `build.log` and `axioms.log`.

## Checked results for this run

* 300 individually checked and committed certificate batches.
* 43,200 generated Lean certificate lines.
* 6,323 public theorems passed the transitive axiom audit.
* 10,800 cylinder tests, 100,000 arithmetic/composition tests, 10,000 histogram
  tests, and 33,792 simultaneous-return tests passed independently.
* The aggregate build and source-integrity checks passed.
* Dependencies are only Lean's standard logical axioms: `propext`,
  `Classical.choice`, and `Quot.sound`; there are no added mathematical axioms.

Existing uncommitted research elsewhere in the repository was preserved.
