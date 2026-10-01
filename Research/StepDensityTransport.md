# Fixed orbit windows preserve density one; infinite windows need not

The new Lean results concern the actual accelerated Collatz map. Pulling a
natural-density-one predicate back through any fixed number of iterations
preserves density one. A finite intersection of these pullbacks also has
density one, so the property holds at every state in any fixed finite orbit
window for almost every starting value.

The number of iterations must remain fixed in this conclusion. The proof
supplies the explicit finite count bound

    count{n<N : P(T^k(n))} ≤ 2^k · count{m<3^k N : P(m)}.

Both constants grow with k. This estimate alone does not preserve an
asymptotic density bound when k is unbounded or selected separately at each
input by a stopping rule.

## The finite counting argument

The accelerated map has branches T(2n)=n and T(2n+1)=3n+2. Thus its pullback
count below 2N splits exactly into the target count below N plus the target
count along 3n+2 for n<N. Selecting one entry per block cannot exceed the
count over the full interval, giving the coarse bound

    count{n<N : P(T(n))} ≤ 2 · count{m<3N : P(m)}.

Induction gives the displayed k-step bound. Applied to the complement of a
density-one predicate, this proves density-one preservation. A separate
finite-union estimate for complementary sets proves closure under finite
intersections.

## An empty countable intersection inside Collatz

Let W_K(n) mean that every state T^j(n), for 0≤j≤K, has finite stopping time.
Here finite stopping means some later iterate drops strictly below that
state; the descent may occur outside the window of length K.

The proved Terras density theorem and fixed-window transport imply

    for every fixed K, DensityOne(W_K).

Nevertheless, the intersection over all K is empty. If every visited state
had a later strict descent, strong induction on the starting value could
follow the next descent to a smaller instance of the same impossible
property. Lean proves, for every n, that some visited state has no finite
stopping time.

For familiar convergent orbits that state is 1: its orbit stays in the 1–2
cycle and never drops below 1. The argument does not prove that the state is
always 1. Identifying every positive never-dropping state with 1 is the
separate universal-descent problem described by
[NeverDrops](../Collatz/Strategy/NeverDrops.lean).

This gives an actual Collatz example in which every finite-window property
has density one but no starting value has all the properties simultaneously.
It explains why one cannot simply replace “every fixed K, almost every n”
with “almost every n, every K.” It does not rule out arguments with additional
uniform control, and it does not contradict the goal of reaching 1.

## Verification

The two modules build, eighteen theorem endpoints pass the standard axiom
audit, and the full main-library integrity check passes with the new results.
An independent probe checks 6,006 exact branch counts, 6,006 one-step count
bounds, 16,968 stride bounds, and 1,836 fixed-iterate bounds.

For 0≤n<10000, the finite probe finds 9,998 starts satisfying W_0, 9,398
satisfying W_20, 767 satisfying W_100, and none satisfying W_200. All positive
starts in this finite probe reach 1 by time 165. These sample counts do not
establish the density limits; they illustrate why increasing the window at a
fixed counting cutoff is a different operation from fixing the window and
letting the cutoff tend to infinity.

```sh
lake build Collatz.Strategy.StoppingQuantifierBoundary
lake env lean scripts/audit_step_density_transport.lean
python3 scripts/probe_step_density_transport.py
bash scripts/check_integrity.sh
```

[Transport proofs](../Collatz/Structure/StepDensityTransport.lean),
[stopping-window proofs](../Collatz/Strategy/StoppingQuantifierBoundary.lean),
[axiom audit](StepDensityTransportAxioms.txt), [probe](StepDensityTransportProbe.json).
