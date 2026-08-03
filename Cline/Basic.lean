/-!
Core statements for the Cline project.

This file is deliberately small.
Unproved goals are represented as propositions, not fake theorems.
-/

namespace Cline

/-- A placeholder domain for future precise formulations of the Cline system. -/
abbrev State := Nat

/-- A placeholder step map.
Replace this when the accepted formal statement is fixed. -/
def step (n : State) : State := n

/-- Repeated application of the step map. -/
def orbit : Nat → State → State
  | 0, n => n
  | k + 1, n => orbit k (step n)

/-- The current top-level conjecture shell.
This is a statement to refine, not a theorem to claim. -/
def ClineConjecture : Prop :=
  ∀ n : State, ∃ k : Nat, orbit k n = 1

/-- A lemma statement waiting for a source and proof. -/
structure LemmaDraft where
  name : String
  source : String
  statement : String
  status : String
  deriving Repr, Inhabited

end Cline
