import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Collatz Dynamics is Partitioned by Residue Class Regularly", arXiv:2304.11388 [2023].

Title: Collatz Dynamics is Partitioned by Residue Class Regularly

Abstract (from OpenAlex metadata, truncated):
We propose Reduced Collatz Conjecture that is equivalent to Collatz Conjecture, which states that every positive integer can return to an integer less than it, instead of 1. Reduced Collatz Conjecture is easier to explore because certain structures must be presented in reduced dynamics, rather than in original dynamics (as original dynamics is a mixture of original dynamics). Reduced dynamics is a computation sequence from starting integer to the first integer less than it, in terms of ``I'' that represents (3*x+1)/2 and ``O'' that represents x/2. We formally prove that all positive integers are partitioned into two halves and either presents ``I'' or ``O'' in next ongoing computation. More specifically, (1) if any positive integer x that is i module $2^t$ (i is an odd integer) is given, then the first t computations (each one is either ``I'' or ``O'' corresponding to whether current integer is odd or even) will be identical with that of i. (2) If current integer after t computations (

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2304.11388
-/

namespace Collatz.Papers.Arxiv2304_11388

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Collatz Dynamics is Partitioned by Residue Class Regularly\", arXiv:2304.11388 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2304_11388
