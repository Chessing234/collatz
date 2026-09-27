import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for M. E. Lines, "Rising and Falling with the Hailstone Numbers", 2021.

Title: Rising and Falling with the Hailstone Numbers

Abstract (from harvested metadata, truncated):
If anything at all is certain about the ‘hailstone number’ problem it is that its origin is shrouded in mystery. It certainly did not begin with an historic publication or even with any recorded exchange of letters between mathematicians insofar as I am aware. It does not appear to be of very great age, but seems to have Fumed up in a rather haphazard fashion at centres of learning all over the world during the last fifty years or so. Whether passed on by word of mouth or ‘rediscovered’ independently over and over again is not clear. In truth, the problem does not even have a name that is universally accepted. Some refer to it as the 3 N- 1-1 problem, others as the Collatz problem (after a certain Lothar Collatz who, as a student in the 1930s, is credited by some as a possible...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1201/9781003072362-3
-/

namespace Collatz.Papers.Journal_10_1201_9781003072362_3

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "M. E. Lines, \"Rising and Falling with the Hailstone Numbers\", Think of a Number, DOI:10.1201/9781003072362-3 [2021]."

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

end Collatz.Papers.Journal_10_1201_9781003072362_3
