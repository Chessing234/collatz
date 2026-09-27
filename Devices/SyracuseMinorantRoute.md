# One-sided comparison route: completed

2026-09-08. The route previously recorded here is now formalized through
its literal universal endpoint. See [the theorem and full proof explanation](SyracuseUniformFloor.md).

For the actual Syracuse PMF, Lean verifies an absolute c>0 such that
μₙ(r)≥c/3ⁿ for every n≥1 and every unit r modulo 3ⁿ. The complete package
check passed for 38 endpoints, with only propext, Classical.choice and
Quot.sound in the transitive axiom footprints. Historical priority is
not established. Collatz itself remains unproved.

The completed chain is:

1. A selected prefix-free subdensity with full reference tails lies below
   the actual law. One-sided truncation error does not pay rejected mass.
2. The literal filtered kernels contract positive-part Haar error.
3. Iteration gives an error at most N C_A/k^A at every generation.
4. Root-uniform summed variation freezes one positive cylinder for all
   sufficiently large generations and every physical representative.
5. The floor bound k_N≥N/2 makes the error at most 4C₂/N.
6. Fixing a test cylinder before increasing N transfers its lower bound
   to the actual Syracuse law by exact projectivity.
7. A bounded inverse valuation reaches that cylinder from every unit.
   The exact PMF recursion propagates a uniform positive floor to all
   units, and projection handles the smaller conductors.

The proof uses Tao's mixing and exact Syracuse distribution machinery and
Mazur's imported core and variation estimates. These remain attributed
and unmodified. The separate `MixingFloorCountermodel.lean` still records
why projectivity and even exponential mixing alone would be insufficient.
