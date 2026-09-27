import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Emre Yolcu et al., "An Automated Approach to the Collatz Conjecture", arXiv:2105.14697 [2021].

Title: An Automated Approach to the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
We explore the Collatz conjecture and its variants through the lens of termination of string rewriting. We construct a rewriting system that simulates the iterated application of the Collatz function on strings corresponding to mixed binary-ternary representations of positive integers. We prove that the termination of this rewriting system is equivalent to the Collatz conjecture. We also prove that a previously studied rewriting system that simulates the Collatz function using unary representations does not admit termination proofs via natural matrix interpretations, even when used in conjunction with dependency pairs. To show the feasibility of our approach in proving mathematically interesting statements, we implement a minimal termination prover that uses natural/arctic matrix interpretations and we find automated proofs of nontrivial weakenings of the Collatz conjecture. Although we do not succeed in proving the Collatz conjecture, we believe that the ideas here represent an intere

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2105.14697
-/

namespace Collatz.Papers.Arxiv2105_14697

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Emre Yolcu et al., \"An Automated Approach to the Collatz Conjecture\", arXiv:2105.14697 [2021]."

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

end Collatz.Papers.Arxiv2105_14697
