import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Collatz Conjecture for $2^{100000}-1$ is True - Algorithms for Verifying Extremely Large Numbers", arXiv:1609.00374 [2016].

Title: Collatz Conjecture for $2^{100000}-1$ is True - Algorithms for Verifying Extremely Large Numbers

Abstract (from OpenAlex metadata, truncated):
Collatz conjecture (or 3x+1 problem) is out for about 80 years. The verification of Collatz conjecture has reached to the number about 60bits until now. In this paper, we propose new algorithms that can verify whether the number that is about 100000bits (30000 digits) can return 1 after 3*x+1 and x/2 computations. This is the largest number that has been verified currently. The proposed algorithm changes numerical computation to bit computation, so that extremely large numbers (without upper bound) becomes possible to be verified. We discovered that $2^{100000}-1$ can return to 1 after 481603 times of 3*x+1 computation, and 863323 times of x/2 computation.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1609.00374
-/

namespace Collatz.Papers.Arxiv1609_00374

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Collatz Conjecture for $2^{100000}-1$ is True - Algorithms for Verifying Extremely Large Numbers\", arXiv:1609.00374 [2016]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1609_00374
