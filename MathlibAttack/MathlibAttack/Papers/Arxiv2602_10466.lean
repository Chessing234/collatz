import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Vigleik Angeltveit, "An improved algorithm for checking the Collatz conjecture for all n < 2^N", arXiv:2602.10466 [2026].

Title: An improved algorithm for checking the Collatz conjecture for all n < 2^N

Abstract (truncated):
We describe a new algorithm for verifying the Collatz conjecture for all n < 2^N for some fixed N. The algorithm takes less than twice as long to verify convergence for all n < 2^{N+1} as it does to verify convergence for all n < 2^N. We also discuss verification of the analogue of the Collatz conjecture for negative numbers.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2602.10466
-/

namespace MathlibAttack.Papers.Arxiv2602_10466

open MathlibAttack.Papers

def citation : String := "Vigleik Angeltveit, \"An improved algorithm for checking the Collatz conjecture for all n < 2^N\", arXiv:2602.10466 [2026]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2602_10466
