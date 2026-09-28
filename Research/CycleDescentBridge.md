# Cycle descent and the bridge to Collatz

For the standard Collatz map C, suppose C^L(m)=m with L>0.
If x=C^i(m)>m and 0≤i≤L, then

    C^(L−i)(x) = C^L(m) = m < x.

Moreover L−i>0, since i=L would give x=m. This proves the proposed
cycle-descent statement, even without assuming m is the minimum.

If m is the minimum of one full period, every later iterate is at least m:
subtracting full periods reduces any time index to that first period.
Therefore a hypothetical cycle with minimum m>1 is not excluded by descent
from its larger members. Applying the argument to m would require another,
strictly smaller member, which contradicts its being the minimum.

Universal descent would be sufficient. Suppose every n>1 eventually reaches
a smaller positive integer. Strong induction on n proves convergence to 1:
the base n=1 is immediate; for n>1 follow the orbit to a smaller value r,
then use the induction hypothesis at r. Conversely, if every positive n
reaches 1, every n>1 reaches a smaller value. Thus universal descent is
exactly equivalent to Collatz, rather than an established consequence of
the cycle argument. Nonperiodic trajectories also lie outside the cycle
argument's hypothesis.

## Formal verification

`Collatz/Strategy/CycleDescentBridge.lean` proves six results:

- returns_to_base
- higher_cycle_member_descends
- cycle_minimum_never_descends
- collatz_of_universal_descent
- universal_descent_iff_collatz
- cycle_minimum_eq_one_of_descent (explicitly conditional)

The targeted build passed (3 jobs). The six-endpoint axiom audit and the
concrete 1 -> 4 -> 2 -> 1 example passed. Dependencies use only propext and
Quot.sound; no added axioms or proof placeholders. Audit output is in
`Research/CycleDescentBridgeAxioms.txt`. The full repository build was not run.

These are elementary cycle and induction facts. No novelty claim is made,
and the universal descent hypothesis has not been proved.
