# Exact boundary coordinates and quantitative shadow rigidity

Research attempt, 2026-09-12. This is a structural result about hypothetical
divergent trajectories, **not a proof of the Collatz conjecture**. Historical
novelty has not been established. The formal verification record is described
below; no empirical statement is used as a proof assumption.

## Main mathematical result

Let

\[
x_k=S^k(n),\qquad S(x)=\frac{3x+1}{2^{a(x)}},\qquad a(x)=v_2(3x+1),
\]

where \(n\) is a positive odd integer and the orbit is injective. Using the
repository's existing reciprocal-summability theorem, define

\[
B(n)=n\exp\left(\sum_{j\ge0}\log\left(1+\frac1{3S^j(n)}\right)\right),
\qquad E_k=B(x_k)-x_k.
\]

For **every** positive integer \(p\) and every \(N\), there is a \(k\ge N\) with

\[
\boxed{\quad |E_{k+p}-E_k|\ge \frac1{6+4\cdot3^p}.\quad}
\]

Consequently, \(E_{k+p}-E_k\) cannot tend to zero for any fixed positive
period \(p\). This conclusion does **not** require a global bound on \(E_k\).
It rules out approach to a periodic pattern in absolute error, including a
constant additive correction. It does not rule out arbitrary nonperiodic
behavior.

Lean endpoints:

- `ShadowRigidity.unconditional_shift_separation`
- `ShadowRigidity.no_asymptotic_shadow_period`

## Why the argument works

Write \(A_k=\sum_{j<k}a(x_j)\) and \(w_k=2^{A_k}/3^k\). Splitting the
convergent correction series at an arbitrary orbit point gives

\[
w_k B(x_k)=B(n),\qquad
2^{a(x_k)}B(x_{k+1})=3B(x_k),\qquad
\frac{B(x_k)}{x_k}\longrightarrow1.
\]

The relative normalization uniquely determines this multiplicative coordinate
along the orbit. Subtracting the actual integer recurrence gives

\[
2^{a(x_k)}E_{k+1}=3E_k-1.
\]

The inverse-series identity gives
\(E_0=\sum_{j\ge0}2^{A_j}/3^{j+1}\ge1\), since \(A_j\ge j\).
The same bound holds at every shifted start.

Now suppose all sufficiently late \(p\)-step shadow differences have size
less than \(\delta=1/(6+4\cdot3^p)<1\). The finite inverse-series budget gives

\[
2^{a(x_k)+\cdots+a(x_{k+p-1})}E_{k+p}\le3^p E_k.
\]

Because \(E_{k+p}\ge1\) and \(E_k<E_{k+p}+1\le2E_{k+p}\), every division
coefficient in such a block, in particular its first one, is less than
\(C=2\cdot3^p\). This obtains a coefficient bound without assuming the
shadow itself is bounded.

Set \(c=2^{a(x_k)}\), \(d=2^{a(x_{k+p})}\). Subtract the two one-step
shadow recurrences. Since \(E_{k+p+1}\ge1\),

\[
|d-c|\le3|E_{k+p}-E_k|+c|E_{k+p+1}-E_{k+1}|
<(3+C)\delta=\tfrac12.
\]

The coefficients are integers, so they are equal. Thus the actual valuation
sequence is eventually \(p\)-periodic.

Finally, two odd integer starts with identical infinite valuation sequences
are equal. The Lean proof establishes this using equality of their finite
2-adic inverse sums and uniqueness of the limit in **one** topology. Applied
to \(x_N\) and \(x_{N+p}\), it gives a repeated orbit point, contradicting
injectivity. No real limit is transferred into the 2-adic topology.

## Additional checked targets

The implementation also establishes:

- An arbitrarily late shadow drop of at least \(2/3\). An infinite tail of
  valuation-one steps would force every power of two to divide the fixed
  integer \(x_N+1\), so valuations at least two recur. Each forces this drop.
- If \(E_k\le M\) everywhere, with \(M\ge1\), then
  \[
  x_k\ge\frac nM\left(\frac{3M}{3M-1}\right)^k.
  \]
  Lean states the equivalent inequality without dividing by powers. Thus
  bounded shadow implies exponential escape; exponential escape is not
  excluded by this result.
- For a bounded shadow, a second shift-separation bound
  \(1/(6(M+1))\), independent of the proposed period.

## Rational grids and a finite length barrier

The rational-grid extension excludes more than repeating patterns. If
\(1\le E_k\le M\), then for every integer \(q>0\) and every tail there is a
\(k\) such that

\[
|qE_k-m|\ge\frac1{6(M+1)}\qquad\text{for every integer }m\ge0.
\]

The lattice points may be chosen nonperiodically. If all errors were smaller,
rounding would turn the shadow recurrence into an exact integer recurrence.
Adding it to \(q\) times the actual orbit recurrence would give positive
integers \(b_k\) with \(2^{a_k}b_{k+1}=3b_k\). Every power of two would then
divide \(b_0\), which is impossible.

There is also a **finite** version, `ShadowLattice.finite_grid_barrier`.
For any finite integer trajectory and any compatible real shadow with
\(1\le E_i\le M\), if all \(L+1\) shadow values through time \(L\) are
within \(1/(6q(M+1))\) of a fixed grid \(q^{-1}\mathbb Z\), then

\[
\boxed{\quad 2^L<q(x_0+M)+1.\quad}
\]

This last theorem assumes no infinite orbit or summability: its hypotheses
are the displayed finite recurrences, bounds, and approximation inequalities.
It is a length bound for a particular type of shadow certificate, not a bound
on arbitrary Collatz stopping times.

## Finite-prefix stress test

[`shadow_prefix_probe.py`](../scripts/shadow_prefix_probe.py) constructs
positive odd integer seeds realizing prescribed finite valuation words,
then checks each step by exact integer arithmetic. Rational shadow values
are assigned by backward propagation from a **prescribed terminal value**.
They are not claimed to equal the actual infinite-orbit boundary.

The word \((1,1,1,1,2)\) has the exact block identity

\[
64x_{k+5}=243x_k+211.
\]

Its periodic shadow starts at \(211/179\) and has phases
\(211/179,227/179,251/179,287/179,341/179\), all strictly between one and two.
The probe realizes 1, 4, 16, and 64 repetitions with actual integer trajectory
prefixes. It also checks a 64-block Thue--Morse choice of runs of four or five
valuation-one steps, with every assigned shadow between one and two.
The total is 777 exactly checked steps. See
[`ShadowPrefixProbe.json`](ShadowPrefixProbe.json).

These checks prevent an invalid strengthening: a long finite periodic shadow
prefix does not itself give a cycle certificate. The new theorem is about
every sufficiently late point of an infinite orbit.

## Scope and remaining obstacle

This work supplies a legitimate route from real estimates to exact integer
constraints under a specific recurrence hypothesis. It does not establish
that a hypothetical divergent orbit has that hypothesis. In particular,
bounded nonperiodic shadows and unbounded shadows remain possible within the
proved restrictions. Nontrivial cycles are a separate unresolved case.

The coordinate \(B\) uses the entire future orbit. Its definition is not an
effective procedure for proving descent. Lean's total definition of an
infinite sum outside the summable case must not be used to extend these
identities to arbitrary orbits.

Prior context includes [Lagarias's overview](https://arxiv.org/abs/2111.02635)
and [Garcia and Tal's 1999 paper](https://doi.org/10.4064/aa-90-3-245-250).
The existing reciprocal-summability and inverse-boundary developments are
reused here; they are not new contributions of this attempt. The short
literature search does not establish priority for the new formulation.

## Formal files and reproduction

From `ProofAtlasAttack`, build the extension and inspect the transitive axioms:

```sh
LEAN_NUM_THREADS=2 lake build +CollatzTargetDensity:olean
LEAN_NUM_THREADS=2 lake env lean Verification/ShadowRigidity.lean
```

The new modules are `ValuationRecurrence`, `BoundaryLinearization`,
`ShadowOscillation`, `ShadowGrowth`, `ShadowRigidity`, and `ShadowLattice`.
The audit file lists all 38 new theorem endpoints. The complete targeted
verification can also be run with `LEAN_NUM_THREADS=2 python3 scripts/verify_shadow.py`.
Verification status and source fingerprints are recorded in
`verification/shadow-report.json`. This targeted audit builds the full package
and checks the new endpoints; it does not rerun every historical endpoint audit.
