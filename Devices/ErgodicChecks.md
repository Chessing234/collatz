# Counting measure and a conditional recurrence argument

**Status: checked in Lean. Collatz remains unproved.**

Two new modules check an attempted ergodic link in the lemma chain. The
counting-measure claim fails on known convergent orbits. A separate argument
using finite positive weights is valid, but requires assumptions that have
not been established for Collatz.

## A counterexample to the printed counting-measure claims

[Assani's arXiv v3](https://arxiv.org/html/2208.11675v3), Definition 2.7 and
Theorem 3.2, require a constant M independent of both finite sets A and Y
for the averaged counting integral, and the proof concludes M=1. Theorem
3.3 also asserts that every integrable function has an integrable pointwise
time-average limit. We check these printed statements directly; this is
not a claim that the paper's separate finite-measure criterion is false.

Use the paper's shortcut map S(n)=n/2 for even n and (3n+1)/2 for odd n.
Set A={1,2} and Y={1,2,4}. Every positive iterate of each point of Y is in A.
Consequently, for every N>=1,

    (1/N) sum_{j=1}^N sum_{x in Y} 1_A(S^j(x)) = 3,

whereas the counting measure of A is 2. More generally, for
Y_r={2^k : 0<=k<=r}, the same average tends to r+1. Thus no finite constant
M works uniformly over Y, even with this one fixed A.

The function f=1_A is integrable for counting measure. Its time averages
tend to 1 at every power of two, because S^k(2^k)=1. Any pointwise limit
therefore takes the value 1 on infinitely many distinct positive integers
and cannot be integrable for counting measure. This refutes the claimed
integrability of the limit, not pointwise convergence itself.

[CountingMeasureCheck.lean](../ProofAtlasAttack/CollatzTargetDensity/CountingMeasureCheck.lean)
uses the imported `Erdos1135.Terras.accelerated` map and proves both the
finite three-point identity and the unbounded family of limiting averages.
The endpoint `no_integrable_visitMean_limit` uses literal
`MeasureTheory.Integrable` with `Measure.count`. Statements about limits
are required only at positive integers, so adjoining zero in Lean's natural
number type does not affect the counterexample.

## What finite weights would actually give

For the ordinary Collatz map T, assign a real weight w(n)>0 to each positive
integer and require that the weights have finite sum. Suppose one constant
C>0 satisfies

    sum_{x in F} w(x) <= C w(y)

for every iterate k, target y, and finite set F of positive integers with
T^k(x)=y for all x in F. This is `AtomicPowerBound T w C`.

Taking F={x} shows w(T^k(x))>=w(x)/C for every k. Summability implies
w(y)->0 as y->infinity, so the orbit of x stays bounded. A bounded orbit
in the natural numbers repeats a value and eventually enters a cycle.
If every positive periodic point reaches 1, then every positive integer
reaches 1.

[AtomicRecurrence.lean](../ProofAtlasAttack/CollatzTargetDensity/AtomicRecurrence.lean)
checks this chain through the canonical `collatzProp` endpoint. **Neither
the required weights and uniform bound nor the exclusion of nontrivial
cycles is constructed.** A one-step bound with constant C>1 does not give
the stated hypothesis: iterating that bound permits the constant C^k.

There is also a checked restriction on a possible construction. The known
edges 2->1, 4->2, and {1,8}->4 imply

    w(2)<=Cw(1),  w(4)<=Cw(2),  w(1)+w(8)<=Cw(4).

Strict positivity forces C>1. This excludes C<=1 only; it does not exclude
the finite-weight approach with a larger uniform constant. The argument
does not use the counting-measure theorem discussed above.

## Verification

From `ProofAtlasAttack`, run:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

This stage's complete package audit passed with 161 named endpoints, including ten
from the counting-measure check and five from the atomic recurrence module.
All 44 extension source hashes matched that stage's successful report; all 1,485
pinned upstream source hashes remained unchanged. The current report also
includes the [fixed-cost generator connection](FixedCostGenerators.md).
The axiom footprints use
only `propext`, `Classical.choice`, and `Quot.sound`. No unfinished proof,
added axiom, or native-evaluation escape is used.

- [Literal signatures and axiom checks](../ProofAtlasAttack/Verification/ErgodicChecks.lean)
- [Audit output](../ProofAtlasAttack/Verification/ergodic-checks-axioms.log)
- [Full verification report](../ProofAtlasAttack/Verification/local-report.json)

These checks identify a failed input and verify a conditional replacement.
They do not supply the missing convergence argument.
