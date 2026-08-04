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

/-- The totalized step map fixes `0`. -/
@[simp] theorem step_zero : step 0 = 0 := by
  simp [step]

/-- The first odd positive state maps to `4`. -/
@[simp] theorem step_one : step 1 = 4 := by
  simp [step]

/-- The state `2` maps to `1`. -/
@[simp] theorem step_two : step 2 = 1 := by
  simp [step]

/-- The state `4` maps to `2`. -/
@[simp] theorem step_four : step 4 = 2 := by
  simp [step]

/-- Zero iterations leave a state unchanged. -/
@[simp] theorem orbit_zero_steps (n : State) : orbit 0 n = n := by
  rfl

/-- One more iteration applies `step` before the remaining iterations. -/
@[simp] theorem orbit_succ_steps (k : Nat) (n : State) :
    orbit (k + 1) n = orbit k (step n) := by
  rfl

/-- The input `1` reaches `1`. -/
theorem one_reaches_one : ∃ k : Nat, orbit k 1 = 1 := by
  exact ⟨0, rfl⟩

/-- The input `2` reaches `1`. -/
theorem two_reaches_one : ∃ k : Nat, orbit k 2 = 1 := by
  exact ⟨1, by simp⟩

/-- The input `4` reaches `1`. -/
theorem four_reaches_one : ∃ k : Nat, orbit k 4 = 1 := by
  exact ⟨2, by simp⟩

/-- A lemma statement waiting for a source and proof. -/
structure LemmaDraft where
  name : String
  source : String
  statement : String
  status : String
  deriving Repr, Inhabited

end Collatz
