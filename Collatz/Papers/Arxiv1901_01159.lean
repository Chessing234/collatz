import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for John G. Koelzer and D. J. Welling, "An Investigation of the Collatz Conjecture", arXiv:1901.01159 [2019].

Title: An Investigation of the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
This paper explores special conditions on the starting value of a Collatz sequence which imply that the Collatz conjecture is true. This is the result of the collaboration of a retired mathematics professor (Koelzer) and a retired physics professor (Welling).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1901.01159
-/

namespace Collatz.Papers.Arxiv1901_01159

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "John G. Koelzer and D. J. Welling, \"An Investigation of the Collatz Conjecture\", arXiv:1901.01159 [2019]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1901_01159
