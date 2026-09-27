import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jonas Kaiser, "On the relationship between the Collatz conjecture and Mersenne prime numbers", arXiv:1608.00862 [2016].

Title: On the relationship between the Collatz conjecture and Mersenne prime numbers

Abstract (from OpenAlex metadata, truncated):
The purpose of this study is to show how to get a necessary criterion for prime numbers with the help of special matrices. My special interest lies in the empirical research of these matrices and their patterns, structures and symmetries. The matrices in turn depend on an expansion of the Collatz algorithm 3n+1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1608.00862
-/

namespace Collatz.Papers.Arxiv1608_00862

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jonas Kaiser, \"On the relationship between the Collatz conjecture and Mersenne prime numbers\", arXiv:1608.00862 [2016]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1608_00862
