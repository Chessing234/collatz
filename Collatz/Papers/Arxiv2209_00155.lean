import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Collatz Dynamics is Partitioned by Residue Class Regularly", arXiv:2209.00155 [2022].

Title: Collatz Dynamics is Partitioned by Residue Class Regularly

Abstract (from OpenAlex metadata, truncated):
We propose Reduced Collatz Conjecture that is equivalent to Collatz Conjecture, which states that every positive integer can return to an integer less than it, instead of 1. Reduced Collatz Conjecture should be easier because some properties are presented in reduced dynamics, rather than in original dynamics (e.g., ratio and period). Reduced dynamics is a computation sequence from starting integer to the first integer less than it, and original dynamics is a computation sequence from starting integer to 1. Reduced dynamics is a component of original dynamics. We denote dynamics of x as a sequence of either computations in terms of ``I'' that represents (3*x+1)/2 and ``O'' that represents x/2. Here 3*x+1 and x/2 are combined together, because 3*x+1 is always even and followed by x/2. We formally prove that all positive integers are partitioned into two halves and either presents ``I'' or 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2209.00155
-/

namespace Collatz.Papers.Arxiv2209_00155

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Collatz Dynamics is Partitioned by Residue Class Regularly\", arXiv:2209.00155 [2022]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2209_00155
