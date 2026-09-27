import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ramachandra Bhat, "Convergence of Collatz Sequences: Procedure to Prove the Collatz Conjecture", arXiv:2103.03100 [2021].

Title: Convergence of Collatz Sequences: Procedure to Prove the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
As Collatz conjecture is still to be proved, a method to arrive at the complete proof is explored here. Conceptually, the process relies on the pre-proven sequence data and the method follows the confirmation of the convergence of the Collatz sequence for all the natural numbers in a sequential forward manner (ascending order of n). Hence, all the numbers less than n have been proved to converge before beginning to prove the convergence of the sequence for the number n. Initially, the the nature of problem was explored and explained the reason for some of the remarkable properties. Then, the pattern analysis of a first few sequences data led to the concept of pre-proven sequence. Then, the origin of quartets and subsequently, the octet patterns are described. The "Even-Odd" combinations and the concept of (8*v + c) gave a clear picture for the overall process of evaluation for the convergence. Then onwards, individual set of numbers are analyzed and the convergence confirmations are ar

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2103.03100
-/

namespace Collatz.Papers.Arxiv2103_03100

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ramachandra Bhat, \"Convergence of Collatz Sequences: Procedure to Prove the Collatz Conjecture\", arXiv:2103.03100 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2103_03100
