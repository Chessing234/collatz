import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Benyamin Khanzadeh Holasou, "Proof of Collatz Theorem", arXiv:2102.02650 [2021].

Title: Proof of Collatz Theorem

Abstract (from OpenAlex metadata, truncated):
In this article, we will show that Collatz is theorem and we proof it by method that we made in section 2 and 3. In section 1, first we introduction Collatz problem and idea of mathematician about this problem then we change the function of this problem and we make a new definition of Collatz set and generalize Collatz problem in the set theory. In section 2 we decrease all of natural numbers to $\mathbb{Z}_{10}$ and make a model with lemma that we said. Then in section 3 we say 3 properties of numbers that are in our models and then we make a new definition of coloring of graph to complete our model and make a new model to explain Collatz system with 3 numbers. Finally in section 4 we begin proof some part of first model and we use properties that we proved in section 3, to proof our model completely.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2102.02650
-/

namespace Collatz.Papers.Arxiv2102_02650

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Benyamin Khanzadeh Holasou, \"Proof of Collatz Theorem\", arXiv:2102.02650 [2021]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2102_02650
