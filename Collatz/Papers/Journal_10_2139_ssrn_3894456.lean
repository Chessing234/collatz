import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sheliazhenko, Yurii, "Autonomous Version of Collatz Conjecture: Freedom of Choice Makes Unsolved Problem Solvable", 2021.

Title: Autonomous Version of Collatz Conjecture: Freedom of Choice Makes Unsolved Problem Solvable

Abstract (from harvested metadata, truncated):
In original Collatz conjecture, you have no choice, for any given natural number, other than to move from 2x to x or, if x is an odd number, from x to 3x + 1. It is an unsolved problem whether you must eventually reach 1, repeating the move. But I proved autonomous version of the conjecture: if you can choose to move from any x ∈ N to 2x or 3x + 1 or vice versa, you always have a way to reach 1. The counterintuitive example of making certain outcomes of formal rules with uncertain outcomes via introducing freedom of choice shows heuristic and educational value of the multidisciplinary approach, linking mathematics, philosophy, and legal theory.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.3894456
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_3894456

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sheliazhenko, Yurii, \"Autonomous Version of Collatz Conjecture: Freedom of Choice Makes Unsolved Problem Solvable\", Academia Letters, DOI:10.2139/ssrn.3894456 [2021]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_2139_ssrn_3894456
