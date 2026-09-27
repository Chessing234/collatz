import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Shalom Eliahou and Jean-Louis Verger-Gaugry, "The number system in rational base $3/2$ and the $3x+1$ problem", arXiv:2504.13716 [2025].

Title: The number system in rational base $3/2$ and the $3x+1$ problem

Abstract (truncated):
The representation of numbers in rational base $p/q$ was introduced in 2008 by Akiyama, Frougny & Sakarovitch, with a special focus on the case $p/q=3/2$. Unnoticed since then, natural questions related to representations in that specific base turn out to intimately involve the Collatz $3x+1$ function. Our purpose in this note is to expose these links and motivate further research into them.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2504.13716
-/

namespace MathlibAttack.Papers.Arxiv2504_13716

open MathlibAttack.Papers

def citation : String := "Shalom Eliahou and Jean-Louis Verger-Gaugry, \"The number system in rational base $3/2$ and the $3x+1$ problem\", arXiv:2504.13716 [2025]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2504_13716
