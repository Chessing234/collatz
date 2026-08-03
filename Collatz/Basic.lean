/-!
Core statements for the Collatz project.

This file is deliberately small.
Unproved goals are represented as propositions, not fake theorems.
-/

namespace Collatz

/-- Positive natural states are represented by natural numbers in this seed model. -/
abbrev State := Nat

/-- The Collatz step map on natural numbers.
It sends `0` to `0` so the total function stays simple.
The conjecture below quantifies only over positive inputs. -/
def step (n : State) : State :=
  if n = 0 then 0
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

/-- Repeated application of the Collatz step map. -/
def orbit : Nat → State → State
  | 0, n => n
  | k + 1, n => orbit k (step n)

/-- The standard Collatz conjecture shell. -/
def CollatzConjecture : Prop :=
  ∀ n : State, n > 0 → ∃ k : Nat, orbit k n = 1

/-- A lemma statement waiting for a source and proof. -/
structure LemmaDraft where
  name : String
  source : String
  statement : String
  status : String
  deriving Repr, Inhabited

end Collatz
