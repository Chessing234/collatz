# Repeated first descent: fixed rounds versus the orbit minimum

The totalized first-descent map D sends n to its first actual orbit value
below n, when one exists, and leaves n unchanged otherwise. Write D^k(n)
for k applications of this map. A round can contain many accelerated steps.

The new Lean development proves two statements with different quantifiers:

- For every fixed K, the set of starts admitting K consecutive strict
  first descents has natural density one.
- For every individual n, the chain reaches a fixed point within n rounds.
  In particular, D^n(n) never descends further.

Both statements concern the actual accelerated Collatz map. They coexist
because the density limit keeps K fixed, whereas the second statement uses
an input-dependent number of rounds. No exceptional start has been removed
by taking more fixed rounds.

## Transport through each fixed round

The earlier first-descent result proves that D preserves density-one
properties under preimage. Its proof uses a tight distribution of first
stopping times, rather than a uniform stopping horizon. Iterating this
transport proves density preservation for D^k with each fixed k.

Apply that result to finite stopping time, which has density one by the
formalized Terras argument, and take a finite intersection over k < K.
This gives `density_one_dropsThrough`: almost every start supports all K
requested descents consecutively. The proof does not supply one exceptional
set outside which every number of descents succeeds.

In fact, `fixed_rounds_vs_diagonal` packages a direct obstruction to such
an inference: finite stopping holds at D^k(n) on a density-one set for
each fixed k, but fails at D^n(n) for every n.

## The endpoint is the minimum of the original orbit

Strict descent cannot continue indefinitely in the natural numbers.
`stabilizes` proves this directly by strong induction and bounds the number
of rounds by the input. Every round remains on the accelerated orbit.

There is also a prefix issue: an attained never-dropper need not generally
be the minimum of all earlier orbit values. First descent resolves this.
Before its endpoint, every omitted orbit value is at least the preceding
starting value. Thus any lower bound valid after a first descent is valid
before it as well. Pulling this fact back through the rounds proves

    orbitMinimum(n) = D^n(n),
    ∃ t, T^t(n) = orbitMinimum(n),
    ∀ t, orbitMinimum(n) ≤ T^t(n).

The minimum operation is idempotent. For n > 0, Lean proves the equivalence

    orbitMinimum(n) = 1  ↔  ∃ t, T^t(n) = 1.

Consequently the endpoint's existence is not a convergence proof. Proving
that all positive endpoints equal 1 is exactly the remaining problem.
This is an elementary structural formalization, not a claim of historical
novelty or a new solution to Collatz.

The definitions use the classical first-descent time, with a default on
non-descending starts. They are noncomputable. The n-round bound does not
bound the number of accelerated steps needed to discover the endpoint,
and does not provide an algorithm for deciding that a start never descends.

## Size bounds and finite tests

Each first descent ends at or above half its starting value. Induction gives
n ≤ 2^k D^k(n), independently of the accelerated time spent in those rounds.

The independent Python probe follows each start from 1 through 10,000 to 1,
with an explicit finite cap that would report an unresolved input. It extracts
record minima, independently reconstructs each first-descent segment, checks
that omitted prefixes stay above the segment start, and checks the half-size
and cumulative size bounds. It verifies 161,802 segments. The largest observed
round count is 23 (one attaining start is 9,591); the largest accelerated time
is 165 (one attaining start is 6,171).

There are 6,623 tested starts with at least 16 descents and none with at least
32. This does not contradict density one for each fixed number of descents:
the theorem is asymptotic. The probe evaluates finite Python trajectories,
not the noncomputable Lean definition, and makes no universal claim.

## Verification

The dedicated audit includes all 21 theorem endpoints. Only `propext`,
`Classical.choice`, and `Quot.sound` occur as dependencies. The module is
included in the main library and its principal endpoints in the integrity
check.

```sh
lake build Collatz.Strategy.DescentRounds
lake env lean scripts/audit_descent_rounds.lean
python3 scripts/probe_descent_rounds.py
bash scripts/check_integrity.sh
```

[Lean development](../Collatz/Strategy/DescentRounds.lean),
[axiom audit](DescentRoundsAxioms.txt),
[finite probe](DescentRoundsProbe.json).

The [minimum-transport obstruction](MinimumTransportBarrier.md) proves that
the stabilized endpoint does not preserve density one, although every fixed
round does. Its range is exactly the density-zero set of non-descending
starts, and terminal hitting times cannot have density-tight tails.
