import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kórus, P., "Functions for the $3n+1$-problem", 2025.

Title: Functions for the $3n+1$-problem

Abstract (from harvested metadata, truncated):
What functions can represent the $3n+1$-problem? A number of such functions have been given during the past years. In this paper, a specific one is considered which has $1, 2, 3, \ldots$ as critical points and $1.5, 2.5, 3.5, \ldots$ as fixed points on the interval $[1,\infty)$. Another function is presented with critical points $1, 2, 3, \ldots ,$ and fixed point $0.5391\!\ldots $ on the real line.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.15421/242527
-/

namespace Collatz.Papers.Journal_10_15421_242527

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kórus, P., \"Functions for the $3n+1$-problem\", Researches in Mathematics, DOI:10.15421/242527 [2025]."

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

end Collatz.Papers.Journal_10_15421_242527
