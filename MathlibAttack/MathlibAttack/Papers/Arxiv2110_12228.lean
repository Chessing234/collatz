import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for J. Llibre and Clàudìa Valls, "A note on the $3x+1$ conjecture", arXiv:2110.12228 [2021].

Title: A note on the $3x+1$ conjecture

Abstract (truncated):
Let $g$ be a map from the set of positive integers into itself defined as follows: Let $x$ be a positive integer. If $x$ is odd, then $g(x)=3x+1$, and if $x$ is even, then $g(x)=x/2$. The $3x+1$ conjecture, also called the Collatz conjecture, states: For any positive integer $x$ there exists another positive integer $m$ such that the $m$-iterate of $x$ under the map $g$ is equal to $1$, i.e. $g^m(x)=1$. We provide some information related with this conjecture.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2110.12228
-/

namespace MathlibAttack.Papers.Arxiv2110_12228

open MathlibAttack.Papers

def citation : String := "J. Llibre and Cl\u00e0ud\u00eca Valls, \"A note on the $3x+1$ conjecture\", arXiv:2110.12228 [2021]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2110_12228
