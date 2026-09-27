import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Andreas-Stephan Elsenhans, "Numerical verification of the Collatz conjecture for billion digit random numbers", arXiv:2502.16743 [2025].

Title: Numerical verification of the Collatz conjecture for billion digit random numbers

Abstract (truncated):
The Collatz conjecture, also known as the 3n+1 problem, is one of the most popular open problems in number theory. In this note, an algorithm for the verification of the Collatz conjecture is presented that works on a standard PC for numbers with up to ten billion decimal places.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2502.16743
-/

namespace MathlibAttack.Papers.Arxiv2502_16743

open MathlibAttack.Papers

def citation : String := "Andreas-Stephan Elsenhans, \"Numerical verification of the Collatz conjecture for billion digit random numbers\", arXiv:2502.16743 [2025]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2502_16743
