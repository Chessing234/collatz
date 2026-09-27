import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Emre Yolcu et al., "An Automated Approach to the Collatz Conjecture", arXiv:2105.14697 [2021].

Title: An Automated Approach to the Collatz Conjecture

Abstract (truncated):
We explore the Collatz conjecture and its variants through the lens of termination of string rewriting. We construct a rewriting system that simulates the iterated application of the Collatz function on strings corresponding to mixed binary-ternary representations of positive integers. We prove that the termination of this rewriting system is equivalent to the Collatz conjecture. We also prove that a previously studied rewriting system that simulates the Collatz function using unary representations does not admit termination proofs via natural matrix interpretations, even when used in conjunction with dependency pairs. To show the feasibility of our approach in proving mathematically interesting statements, we implement a minimal termination prover that uses natural/arctic matrix interpretations and we find automated proofs of nontrivial weakenings of the Collatz conjecture. Although we 

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2105.14697
-/

namespace MathlibAttack.Papers.Arxiv2105_14697

open MathlibAttack.Papers

def citation : String := "Emre Yolcu et al., \"An Automated Approach to the Collatz Conjecture\", arXiv:2105.14697 [2021]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2105_14697
