import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Paul M. Weichsel, "Some Collatz quadratic prime sequences", arXiv:2203.03037 [2022].

Title: Some Collatz quadratic prime sequences

Abstract (truncated):
We consider some quadratic variations of the recursive sequence introduced by Lothar Collatz in 1937.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2203.03037
-/

namespace MathlibAttack.Papers.Arxiv2203_03037

open MathlibAttack.Papers

def citation : String := "Paul M. Weichsel, \"Some Collatz quadratic prime sequences\", arXiv:2203.03037 [2022]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2203_03037
