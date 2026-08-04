import Collatz.Basic

/-!
Lean notes for Jeffrey C. Lagarias,
"The 3x+1 problem: An annotated bibliography (1963--1999) (sorted by author)",
arXiv:math/0309224 [math.NT].

The arXiv abstract describes the accelerated map
`T(n) = (3n+1)/2` for odd `n` and `T(n) = n/2` for even `n`,
and states the 3x+1 conjecture for positive integers.  The conjecture is
recorded below as a proposition, not as a theorem.

Metadata checked from <https://arxiv.org/abs/math/0309224>:
arXiv:math/0309224 [math.NT], with subjects Number Theory (math.NT)
and Dynamical Systems (math.DS).
-/

namespace Collatz.Papers.Lagarias2003Bibliography

/-- Exact source tracked by this file. -/
def citation : String :=
  "Jeffrey C. Lagarias, The 3x+1 problem: An annotated bibliography (1963--1999) (sorted by author), arXiv:math/0309224 [math.NT]."

/-- The accelerated 3x+1 map described in the arXiv abstract. -/
def acceleratedStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Iteration of the accelerated map. -/
def acceleratedOrbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => acceleratedOrbit k (acceleratedStep n)

/-- The 3x+1 conjecture statement as described in the arXiv abstract. -/
def threeXPlusOneConjecture : Prop :=
  ∀ n : Nat, n > 1 → ∃ k : Nat, acceleratedOrbit k n = 1

/-- Zero iterations leave an accelerated state unchanged. -/
@[simp] theorem acceleratedOrbit_zero_steps (n : Nat) : acceleratedOrbit 0 n = n := by
  rfl

/-- One more accelerated iteration applies `acceleratedStep` first. -/
@[simp] theorem acceleratedOrbit_succ_steps (k n : Nat) :
    acceleratedOrbit (k + 1) n = acceleratedOrbit k (acceleratedStep n) := by
  rfl

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_zero : acceleratedStep 0 = 0 := by
  simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_one : acceleratedStep 1 = 2 := by
  simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_two : acceleratedStep 2 = 1 := by
  simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_three : acceleratedStep 3 = 5 := by
  simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_four : acceleratedStep 4 = 2 := by
  simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_five : acceleratedStep 5 = 8 := by
  simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_eight : acceleratedStep 8 = 4 := by
  simp [acceleratedStep]

/-- The input `1` reaches `1` under the accelerated map. -/
theorem accelerated_one_reaches_one : ∃ k : Nat, acceleratedOrbit k 1 = 1 := by
  exact ⟨2, by simp [acceleratedOrbit]⟩

/-- The input `2` reaches `1` under the accelerated map. -/
theorem accelerated_two_reaches_one : ∃ k : Nat, acceleratedOrbit k 2 = 1 := by
  exact ⟨1, by simp [acceleratedOrbit]⟩

/-- The input `3` reaches `1` under the accelerated map. -/
theorem accelerated_three_reaches_one : ∃ k : Nat, acceleratedOrbit k 3 = 1 := by
  exact ⟨5, by simp [acceleratedOrbit]⟩

/-- The input `4` reaches `1` under the accelerated map. -/
theorem accelerated_four_reaches_one : ∃ k : Nat, acceleratedOrbit k 4 = 1 := by
  exact ⟨2, by simp [acceleratedOrbit]⟩

end Collatz.Papers.Lagarias2003Bibliography