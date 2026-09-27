import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Vincent Béhani, "Linear dynamics of an operator associated to the Collatz map", arXiv:2303.03203 [2023].

Title: Linear dynamics of an operator associated to the Collatz map

Abstract (truncated):
In this paper, we study the dynamics of an operator $\mathcal T$ naturally associated to the so-called Collatz map, which maps an integer $n \geq 0$ to $n / 2$ if $n$ is even and $3n + 1$ if $n$ is odd. This operator $\mathcal T$ is defined on certain weighted Bergman spaces $\mathcal B ^ 2 _ ω$ of analytic functions on the unit disk. Building on previous work of Neklyudov, we show that $\mathcal T$ is hypercyclic on $\mathcal B ^ 2 _ ω$, independently of whether the Collatz Conjecture holds true or not. Under some assumptions on the weight $ω$, we show that $\mathcal T$ is actually ergodic with respect to a Gaussian measure with full support, and thus frequently hypercyclic and chaotic.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2303.03203
-/

namespace MathlibAttack.Papers.Arxiv2303_03203

open MathlibAttack.Papers

def citation : String := "Vincent B\u00e9hani, \"Linear dynamics of an operator associated to the Collatz map\", arXiv:2303.03203 [2023]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2303_03203
