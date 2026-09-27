# Testing two possible links in the Collatz proof chain

**Status: these are checked constraints on the proposed argument. They do
not establish the missing upper tail or prove Collatz.** The map throughout
is the actual ordinary Collatz map, not a modified example.

Let B be the positive integers that never reach 1, and let

    D = {n in B : T(n) < n},
    A_h = {n > 0 : every iterate of n is at least h}.

## Descent cannot be substituted for convergence

If n belongs to B, then 2n also belongs to B, because T(2n)=n. But 2n drops
strictly at its first step. Doubling therefore gives an injection from
counterexamples below X/2 into D below X:

    count B below floor(X/2) <= count D below X.

The existing predecessor theorem says that, if B is nonempty, there are
c>0 and X0 such that count B below X >= cX for all X>=X0. The injection
then gives

    count D below X >= (c/4)X

for all X>=max(2X0,4). Thus a counterexample would force a positive lower
natural density of counterexamples which nevertheless have stopping time
one. This is a conditional statement; it does not assert that B is nonempty.

The pointwise shortcut can be diagnosed exactly. Lean proves

    (every positive n with T(n)<n reaches 1) <-> Collatz.

For the forward implication, apply the premise to 2n and then use its
first step to n. The converse follows immediately from convergence for all
positive n. The left side is therefore an unproved statement of the full
problem, not a known consequence of a stopping-time estimate.

Terras and Everett's almost-everywhere descent theorem concerns the minimum
being below the starting value. Tao's introduction explicitly distinguishes
this from convergence and explains why averaged descent statements cannot
simply be iterated through exceptional sets. See
[Tao, Section 1.1](https://arxiv.org/html/1909.03562v7#S1.SS1).
The new local lemmas use the proved predecessor estimate to make the
distinction quantitative under the hypothesis of a counterexample.

## Adjusting a fixed threshold does not close the gap

Suppose m is the least counterexample. For every 1<h<=m, Lean proves

    A_h = B.

One inclusion follows because an orbit reaching 1 cannot stay above h>1.
For the other, every iterate of a counterexample is still a counterexample,
so minimality of m puts every such iterate at or above m>=h. Thus all
thresholds in this range give exactly the same exceptional set, rather
than progressively smaller sets that could be eliminated by iteration.

For h>m, the predecessor-set inclusion in the existing energy argument no
longer holds literally: m reaches 3m+1, but m itself lies below h at time
zero. This only proves failure of inclusion. It does **not** prove a positive
density loss, and it does not exclude a future argument which controls the
lost subset quantitatively. Such control is not supplied here.

## Formal files

- [DescentVsConvergence.lean](../ProofAtlasAttack/CollatzTargetDensity/DescentVsConvergence.lean)
- [Verification source](../ProofAtlasAttack/Verification/DescentVsConvergence.lean)
- [Original chain and remaining tail inequality](CollatzProofChain.md)

No novelty claim is made for the doubling or minimality arguments.
Their purpose here is to prevent two invalid substitutions in the attempted
connection between density theorems and pointwise convergence.

That stage's full package check passed on 2026-09-08 with 115 audited endpoints,
including all nine in this file. Only `propext`, `Classical.choice`, and
`Quot.sound` occur in their transitive axiom footprints. All 1,485 upstream
source hashes remained unchanged, and all 39 extension hashes were checked
at that stage. The [report](../ProofAtlasAttack/verification/local-report.json)
now records the latest complete package check, including subsequent modules.
The [audit output](../ProofAtlasAttack/verification/descent-vs-convergence-axioms.log)
prints the conditional density statement and the exact equivalence.
