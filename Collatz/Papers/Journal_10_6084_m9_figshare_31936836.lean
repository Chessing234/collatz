import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Richard Hudson, "Collatz Conjecture is true", 2026.

Title: Collatz Conjecture is true

Abstract (from harvested metadata, truncated):
Originated by Lothar Collatz in 1937 [1], the conjecture states: given the recursive function, y=3x+1 if x is odd, or y=x/2 if x is even, for any positive integer x, y will equal 1 after a finite number of steps. This analysis examines the details of the Collatz functions and their interactions.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.31936836
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_31936836

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Richard Hudson, \"Collatz Conjecture is true\", Figshare, DOI:10.6084/m9.figshare.31936836 [2026]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_31936836
