import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Raouf Rajab, "Classification of Collatz infinite sequences", arXiv:2106.01324 [2021].

Title: Classification of Collatz infinite sequences

Abstract (truncated):
In the present paper, we are interested in classifying of Collatz sequences on based to the different behavior of these sequences when their lengths tend to infinity. A Collatz infinite sequence can be defined as an infinite ordered set of positive integers such that the term of rank n is results of applying Collatz map n times to the first term. Such term can be expressed on the form Tn(P)=A(P,n)P+B(P,n). When n tends to infinity, each function among the two partial coefficients denoted by A(P,n) and B(P,n) behaves in different ways. This allows us to determine all categories of Collatz infinite sequences. First, we carry out a classification of Collatz infinite sequences on based of the different possible limits of the two coefficients. In second time, we determine the different proportions of every class of the infinite sequences. Note that results obtained do not represent a proof of

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2106.01324
-/

namespace MathlibAttack.Papers.Arxiv2106_01324

open MathlibAttack.Papers

def citation : String := "Raouf Rajab, \"Classification of Collatz infinite sequences\", arXiv:2106.01324 [2021]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2106_01324
