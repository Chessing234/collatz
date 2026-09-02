import Collatz.Core.Reach

/-!
# The escape schema is circular

A recurring proposal runs as follows.

> Suppose `n` never reaches `1`.  Iterate the Collatz procedure on `n`.
> Eventually one arrives at a number that *does* reach `1`; hence `n` reaches
> `1` after all, and no counterexample exists.

The middle step is not merely unproved.  It is **refutable from its own
hypothesis**, and this file proves that.

The mechanism is the one-step pullback `reachesOne_of_step`: reaching `1` is
inherited *backwards* along the map, so failing to reach `1` is inherited
*forwards*.  The set of counterexamples is therefore closed under `step`
(`neverReachesOne_step`) and under every iterate (`neverReachesOne_orbit`).
Assuming a counterexample `n` thus places the entire forward orbit of `n` inside
the counterexample set, and `no_escape` records the conclusion: **no point of
that orbit reaches `1`**.  There is nothing to arrive at.

The final result names the price exactly.  `EscapeSchema` is the middle step
written as a proposition, and `escapeSchema_iff_conjecture` proves it *logically
equivalent* to `CollatzConjecture` itself.  So the schema is not a route to the
conjecture; it is the conjecture, restated with a vacuous hypothesis in front.
Any argument of this shape has to discharge the whole problem at the step where
it claims to be making progress.

No Mathlib, no `sorry`.
-/

namespace Collatz
namespace EscapeSchema

open Reach

/-! ## The counterexample predicate -/

/-- `NeverReachesOne n` is the assumption the schema opens with: the orbit of
`n` never meets `1`. -/
def NeverReachesOne (n : Nat) : Prop := ¬ ReachesOne n

/-! ## Forward closure

The pullback lemma `reachesOne_of_step` says convergence travels backwards along
a step.  Contraposing it sends *non*-convergence forwards. -/

/-- **One-step forward closure.**  A counterexample steps to a counterexample. -/
theorem neverReachesOne_step {n : Nat} (h : NeverReachesOne n) :
    NeverReachesOne (step n) :=
  fun hs => h (reachesOne_of_step hs)

/-- **Forward closure along the whole orbit.**  Every iterate of a
counterexample is again a counterexample.  Proved by induction on `k`, which is
exactly the induction the schema needs to fail. -/
theorem neverReachesOne_orbit {n : Nat} (h : NeverReachesOne n) :
    ∀ k : Nat, NeverReachesOne (orbit k n) := by
  intro k
  induction k generalizing n with
  | zero => exact h
  | succ k ih =>
    rw [orbit_succ_steps]
    exact ih (neverReachesOne_step h)

/-- The same statement for an arbitrary reachable point, not just an iterate. -/
theorem neverReachesOne_of_reaches {n m : Nat} (h : NeverReachesOne n)
    (hr : Reaches n m) : NeverReachesOne m :=
  fun hm => h (reachesOne_of_reaches hr hm)

/-- **The escape is impossible.**  Under the schema's own hypothesis, no point
reachable from `n` reaches `1`.  This is the refutation of the middle step: the
number the argument hopes to "eventually arrive at" provably does not exist. -/
theorem no_escape {n : Nat} (h : NeverReachesOne n) (k : Nat) :
    ¬ ReachesOne (orbit k n) :=
  neverReachesOne_orbit h k

/-- Stated as the schema states it: assuming a counterexample, the existential
the argument wants to produce is false. -/
theorem not_exists_escape {n : Nat} (h : NeverReachesOne n) :
    ¬ ∃ k : Nat, ReachesOne (orbit k n) := by
  intro hk
  obtain ⟨k, hk⟩ := hk
  exact no_escape h k hk

/-- Conversely, and this is the only content the schema ever had: if some
iterate reaches `1`, then so does `n`.  Sound, but it presupposes what is to be
proved. -/
theorem reachesOne_of_orbit_escape {n : Nat} (h : ∃ k : Nat, ReachesOne (orbit k n)) :
    ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  exact (reachesOne_iff_orbit k n).mpr hk

/-! ## The schema costs the whole conjecture -/

/-- The middle step of the schema, written as a proposition.  The positivity
hypothesis is needed: `0` is a fixed point with `¬ ReachesOne 0`, so without it
the statement is outright false rather than merely circular. -/
def EscapeSchema : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n → ∃ k : Nat, ReachesOne (orbit k n)

/-- **The schema is the conjecture.**  Proving the middle step is neither more
nor less than proving Collatz.

Forwards: the schema hands us an escape point, `no_escape` says the hypothesis
that produced it forbids it, so the hypothesis fails and `n` reaches `1`.
Backwards: with the conjecture in hand the schema's hypothesis is never
satisfied, so the implication holds vacuously. -/
theorem escapeSchema_iff_conjecture : EscapeSchema ↔ CollatzConjecture := by
  constructor
  · intro hs n hn
    exact Classical.byContradiction fun hne =>
      not_exists_escape hne (hs n hn hne)
  · intro hc n hn hne
    exact absurd (hc n hn) hne

/-- The same point without classical logic: the schema refutes every
counterexample, but a refutation is all it delivers — the positive statement
still has to come from somewhere. -/
theorem escapeSchema_not_not {n : Nat} (hs : EscapeSchema) (hn : 0 < n) :
    ¬ ¬ ReachesOne n :=
  fun hne => not_exists_escape hne (hs n hn hne)

/-- And so the hypothesis of the schema is the hypothesis of the conjecture:
a counterexample to Collatz is a number whose *entire* forward orbit consists of
counterexamples. -/
theorem counterexample_orbit_all_counterexamples {n : Nat}
    (h : ¬ ∃ k : Nat, orbit k n = 1) :
    ∀ k : Nat, ¬ ∃ j : Nat, orbit j (orbit k n) = 1 := by
  have hn' : NeverReachesOne n := h
  intro k
  exact neverReachesOne_orbit hn' k

/-! ## Axiom audit

`no_escape` — the refutation of the middle step — is fully constructive.
Only the classical direction of `escapeSchema_iff_conjecture` (turning
`¬ ¬ ReachesOne n` into `ReachesOne n`) draws on `Classical.choice`; the
constructive half is `escapeSchema_not_not`. -/
#print axioms no_escape
#print axioms escapeSchema_iff_conjecture

end EscapeSchema
end Collatz
