import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bülent Sukuşu, "Proof of the Collatz Conjecture", arXiv:2210.00432 [2023].

Title: Proof of the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture (or 3n+1 problem) has been explored for about 86 years. In this article, we prove the Collatz conjecture. We will show that this conjecture holds for all positive integers by applying the Collatz inverse operation to the numbers that satisfy the rules of the Collatz conjecture. Finally, we will prove that there are no positive integers that do not satisfy this conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2210.00432
-/

namespace Collatz.Papers.Arxiv2210_00432

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "B\u00fclent Suku\u015fu, \"Proof of the Collatz Conjecture\", arXiv:2210.00432 [2023]."

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

end Collatz.Papers.Arxiv2210_00432
