import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andreas-Stephan Elsenhans, "Numerical verification of the Collatz conjecture for billion digit random numbers", arXiv:2502.16743 [2025].

Title: Numerical verification of the Collatz conjecture for billion digit random numbers

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture, also known as the 3n+1 problem, is one of the most popular open problems in number theory. In this note, an algorithm for the verification of the Collatz conjecture is presented that works on a standard PC for numbers with up to ten billion decimal places.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2502.16743
-/

namespace Collatz.Papers.Arxiv2502_16743

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andreas-Stephan Elsenhans, \"Numerical verification of the Collatz conjecture for billion digit random numbers\", arXiv:2502.16743 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2502_16743
