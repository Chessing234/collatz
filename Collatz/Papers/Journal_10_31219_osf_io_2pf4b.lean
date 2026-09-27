import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Leszek Mazurek, "Collatz Conjecture - The Proof", 2023.

Title: Collatz Conjecture - The Proof

Abstract (from harvested metadata, truncated):
In this paper, we prove the Collatz conjecture. We show that if a given number can be represented in a form of a certain specific equation then Collatz conjecture is true for that particular number. Next we propose a procedure that for a given number produces this specific equation and we prove that for every initial positive integer, such equation can be found.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/2pf4b
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_2pf4b

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Leszek Mazurek, \"Collatz Conjecture - The Proof\", DOI:10.31219/osf.io/2pf4b [2023]."

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

end Collatz.Papers.Journal_10_31219_osf_io_2pf4b
