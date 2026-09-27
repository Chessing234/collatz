import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vigleik Angeltveit, "An improved algorithm for checking the Collatz conjecture for all n < 2^N", arXiv:2602.10466 [2026].

Title: An improved algorithm for checking the Collatz conjecture for all n < 2^N

Abstract (from OpenAlex metadata, truncated):
We describe a new algorithm for verifying the Collatz conjecture for all n < 2^N for some fixed N. The algorithm takes less than twice as long to verify convergence for all n < 2^{N+1} as it does to verify convergence for all n < 2^N. We also discuss verification of the analogue of the Collatz conjecture for negative numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2602.10466
-/

namespace Collatz.Papers.Arxiv2602_10466

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vigleik Angeltveit, \"An improved algorithm for checking the Collatz conjecture for all n < 2^N\", arXiv:2602.10466 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2602_10466
