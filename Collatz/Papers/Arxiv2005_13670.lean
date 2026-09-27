import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kauffman, Louis, Lopes, Pedro, "On the orbits associated with the Collatz conjecture", arXiv:2005.13670 [2020].

Title: On the orbits associated with the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
This article is based upon previous work by Sousa Ramos and his collaborators. They first prove that the existence of only one orbit associated with the Collatz conjecture is equivalent to the determinant of each matrix of a certain sequence of matrices to have the same value. These matrices are called Collatz matrices. The second step in their work would be to calculate this determinant for each of the Collatz matrices. Having calculated this determinant for the first few terms of the sequence of matrices, their plan was to prove the determinant of the current term equals the determinant of the previous one. Unfortunately, they could not prove it for the cases where the dimensions of the matrices are 26+54l or 44+54l, where l is a positive integer. In the current article we improve on these results.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2005.13670
-/

namespace Collatz.Papers.Arxiv2005_13670

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kauffman, Louis and Lopes, Pedro, \"On the orbits associated with the Collatz conjecture\", arXiv:2005.13670 [2020]."

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

end Collatz.Papers.Arxiv2005_13670
