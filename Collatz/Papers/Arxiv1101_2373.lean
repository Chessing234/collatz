import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kevin P. Thompson, "An Alternative Computational Approach to the Collatz Conjecture", arXiv:1101.2373 [2011].

Title: An Alternative Computational Approach to the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
An alternative computational approach to the Collatz (3n+1) conjecture is presented that may be theoretically capable of confirming the conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1101.2373
-/

namespace Collatz.Papers.Arxiv1101_2373

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kevin P. Thompson, \"An Alternative Computational Approach to the Collatz Conjecture\", arXiv:1101.2373 [2011]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1101_2373
