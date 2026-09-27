import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Eduardo M. K. Souza, "Infinity increasing steps on the Collatz sequences", arXiv:2305.16161 [2023].

Title: Infinity increasing steps on the Collatz sequences

Abstract (truncated):
We intend to contribute to the Collatz dynamics problem by seeking to analyze the Collatz conjecture from the tree of numbers sequences. First, we show numerically that the distribution of odd numbers has an initial transient, and proceeds to a power law growth to its maximum. Second, using the formulation that uses only odd numbers, we present analytically a set of odd number sequences that is always increasing and can have an infinite number of terms.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2305.16161
-/

namespace MathlibAttack.Papers.Arxiv2305_16161

open MathlibAttack.Papers

def citation : String := "Eduardo M. K. Souza, \"Infinity increasing steps on the Collatz sequences\", arXiv:2305.16161 [2023]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2305_16161
