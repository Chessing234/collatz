import Collatz.Basic
import Collatz.Accelerated

/-! Lean notes for Jeffrey C. Lagarias,
"The 3x+1 problem: An annotated bibliography (1963--1999) (sorted by author)",
arXiv:math/0309224 [math.NT].

The arXiv abstract describes the accelerated map
`T(n) = (3n+1)/2` for odd `n` and `T(n) = n/2` for even `n`,
and states the 3x+1 conjecture for positive integers.  The conjecture is
recorded below as a proposition, not as a theorem.

This file now re-uses the shared accelerated-orbit definitions from
`Collatz.Accelerated` and records the bibliographic statement of the
accelerated 3x+1 conjecture.

Metadata checked from <https://arxiv.org/abs/math/0309224>:
arXiv:math/0309224 [math.NT], with subjects Number Theory (math.NT)
and Dynamical Systems (math.DS).
-/

namespace Collatz.Papers.Lagarias2003Bibliography

/-- Exact source tracked by this file. -/
def citation : String :=
  "Jeffrey C. Lagarias, The 3x+1 problem: An annotated bibliography (1963--1999) (sorted by author), arXiv:math/0309224 [math.NT]."

/-- Re-export the citation-friendly name for the accelerated step. -/
abbrev acceleratedStep : Nat → Nat := Collatz.acceleratedStep

/-- Re-export the citation-friendly name for the accelerated orbit. -/
abbrev acceleratedOrbit : Nat → Nat → Nat := Collatz.acceleratedOrbit

/-- The 3x+1 conjecture statement as described in the arXiv abstract. -/
def threeXPlusOneConjecture : Prop :=
  ∀ n : Nat, n > 1 → ∃ k : Nat, acceleratedOrbit k n = 1

/-- The input `1` reaches `1` under the accelerated map. -/
theorem accelerated_one_reaches_one : ∃ k : Nat, acceleratedOrbit k 1 = 1 :=
  Collatz.one_reaches_one_accelerated

/-- The input `2` reaches `1` under the accelerated map. -/
theorem accelerated_two_reaches_one : ∃ k : Nat, acceleratedOrbit k 2 = 1 :=
  Collatz.two_reaches_one_accelerated

/-- The input `3` reaches `1` under the accelerated map. -/
theorem accelerated_three_reaches_one : ∃ k : Nat, acceleratedOrbit k 3 = 1 :=
  Collatz.three_reaches_one_accelerated

/-- The input `4` reaches `1` under the accelerated map. -/
theorem accelerated_four_reaches_one : ∃ k : Nat, acceleratedOrbit k 4 = 1 :=
  Collatz.four_reaches_one_accelerated

end Collatz.Papers.Lagarias2003Bibliography
