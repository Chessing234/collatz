import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Clifford A Pickover, "Hailstone Numbers", 2001.

Title: Hailstone Numbers

Abstract (from harvested metadata, truncated):
Abstract On a recent trip to the Himalayas, Dr. Googol found himself walking in a blinding hailstorm! The hailstones drifted up and down in the wisps and eddies of wind. Sometimes the stones shot up for as far as his eye could see and then came plummeting back to Earth, smashing into the ground like little meteorites. Dr. Googol smiled because he realized hailstones provide a wonderful metaphor for one of the most famous and unusual problems in number theory. He whipped out a piece of paper from his pocket and began scribbling a strange sequence of numbers: 7, 22,11, 34,17.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1093/oso/9780195133424.003.0049
-/

namespace Collatz.Papers.Journal_10_1093_oso_9780195133424_003_0049

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Clifford A Pickover, \"Hailstone Numbers\", Wonders of Numbers, DOI:10.1093/oso/9780195133424.003.0049 [2001]."

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

end Collatz.Papers.Journal_10_1093_oso_9780195133424_003_0049
