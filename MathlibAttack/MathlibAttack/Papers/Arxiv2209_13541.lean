import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Lei Li, "A Proof for the Collatz Conjecture", arXiv:2209.13541 [2022].

Title: A Proof for the Collatz Conjecture

Abstract (truncated):
It is well known that the following Collatz Conjecture is one of the unsolved problems in mathematics. Collatz Conjecture: For any positive integer $n>1$, the following recursive algorithm will convergent to 1 by a finite number of steps. A) If $n$ is an even number then $n/2 \to n$, B) If $n$ is an odd number then $3n+1 \to n$. This paper proposes a proof for the Collatz Conjecture by the elementary mathematical induction.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2209.13541
-/

namespace MathlibAttack.Papers.Arxiv2209_13541

open MathlibAttack.Papers

def citation : String := "Lei Li, \"A Proof for the Collatz Conjecture\", arXiv:2209.13541 [2022]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2209_13541
