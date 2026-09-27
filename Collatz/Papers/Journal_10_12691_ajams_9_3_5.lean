import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wilber Valgusbitkevyt, "Solution to Collatz Conjecture", 2012.

Title: Solution to Collatz Conjecture

Abstract (from harvested metadata, truncated):
There is a pattern for the arbitary sequence which can be divided into four groups to be formalized as a recursive formula which shows the conjecture is true.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.12691/ajams-9-3-5
-/

namespace Collatz.Papers.Journal_10_12691_ajams_9_3_5

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wilber Valgusbitkevyt, \"Solution to Collatz Conjecture\", viXra, DOI:10.12691/ajams-9-3-5 [2012]."

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

end Collatz.Papers.Journal_10_12691_ajams_9_3_5
