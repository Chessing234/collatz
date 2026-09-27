import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Raouf Rajab, "Classification of Collatz infinite sequences", arXiv:2106.01324 [2021].

Title: Classification of Collatz infinite sequences

Abstract (from OpenAlex metadata, truncated):
In the present paper, we are interested in classifying of Collatz sequences on based to the different behavior of these sequences when their lengths tend to infinity. A Collatz infinite sequence can be defined as an infinite ordered set of positive integers such that the term of rank n is results of applying Collatz map n times to the first term. Such term can be expressed on the form Tn(P)=A(P,n)P+B(P,n). When n tends to infinity, each function among the two partial coefficients denoted by A(P,n) and B(P,n) behaves in different ways. This allows us to determine all categories of Collatz infinite sequences. First, we carry out a classification of Collatz infinite sequences on based of the different possible limits of the two coefficients. In second time, we determine the different proportions of every class of the infinite sequences. Note that results obtained do not represent a proof of a Collatz conjecture but they have a strong relationship with this conjecture and it allows us to b

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2106.01324
-/

namespace Collatz.Papers.Arxiv2106_01324

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Raouf Rajab, \"Classification of Collatz infinite sequences\", arXiv:2106.01324 [2021]."

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

end Collatz.Papers.Arxiv2106_01324
