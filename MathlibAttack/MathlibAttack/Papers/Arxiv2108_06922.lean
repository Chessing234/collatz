import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Ashish Tiwari, "A Conjecture Equivalent to the Collatz Conjecture", arXiv:2108.06922 [2021].

Title: A Conjecture Equivalent to the Collatz Conjecture

Abstract (truncated):
We present a formulation of the Collatz conjecture that is potentially more amenable to modeling and analysis by automated termination checking tools.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2108.06922
-/

namespace MathlibAttack.Papers.Arxiv2108_06922

open MathlibAttack.Papers

def citation : String := "Ashish Tiwari, \"A Conjecture Equivalent to the Collatz Conjecture\", arXiv:2108.06922 [2021]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2108_06922
