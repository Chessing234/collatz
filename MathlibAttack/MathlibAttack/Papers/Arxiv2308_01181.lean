import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Luis H. Gallardo and Olivier Rahavandrainy, "On Collatz Conjecture for binary polynomials", arXiv:2308.01181 [2023].

Title: On Collatz Conjecture for binary polynomials

Abstract (truncated):
We build a variant of Collatz Conjecture for polynomials over $\mathbb{F}_2$ and we prove that it is solved. By the way, we give several examples.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2308.01181
-/

namespace MathlibAttack.Papers.Arxiv2308_01181

open MathlibAttack.Papers

def citation : String := "Luis H. Gallardo and Olivier Rahavandrainy, \"On Collatz Conjecture for binary polynomials\", arXiv:2308.01181 [2023]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2308_01181
