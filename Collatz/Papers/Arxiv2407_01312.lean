import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ahmet F. Gocgen, Emin M. Buyukyayla, "Calculation of the Number of Transactions for Collatz Conjecture", arXiv:2407.01312 [2024].

Title: Calculation of the Number of Transactions for Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
In this article we have constructed a basic methodology from which important perspectives for both the Collatz conjecture and Beal's conjecture can be derived. We falsified the conjecture we previously developed on Beal's conjecture and made the falsified conjecture usable for Collatz conjecture. In this regard, we have clearly expressed the numbers that can reach 1 in the Collatz conjecture. Then, using this, we created a limit for the numbers that should be considered for the Collatz conjecture. Thanks to the analysis of this limit, we have clearly expressed the recursive Collatz function in an equation. Using this structure, we wrote a function that indicates how many times the Collatz function repeats certain numbers to reach 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2407.01312
-/

namespace Collatz.Papers.Arxiv2407_01312

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ahmet F. Gocgen and Emin M. Buyukyayla, \"Calculation of the Number of Transactions for Collatz Conjecture\", arXiv:2407.01312 [2024]."

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

end Collatz.Papers.Arxiv2407_01312
