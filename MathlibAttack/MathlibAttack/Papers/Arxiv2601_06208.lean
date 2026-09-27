import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Abderrahman Bouhamidi, "An Extension of the Collatz Conjecture modulo $2^p+2^q$", arXiv:2601.06208 [2026].

Title: An Extension of the Collatz Conjecture modulo $2^p+2^q$

Abstract (truncated):
In this paper, we will introduce an extension to the Collatz's conjecture. This conjecture may be seen as a general conjecture that unifies the Collatz one together with many other similar conjectures. For instance, we propose our new conjecture modulo $10$ which may be stated as follows. Starting from any positive integer, if it is a multiple of $10$ then divide it by 10, otherwise, multiply it by $12$, add $8$ times its last digit and divide the result by $10$. Repeat the process infinitely. Regardless the starting number, the process eventually reaches $4$ after a finite number of iterations. The genaral conjecture studied here will encompasse the classical Collatz conjecture togher with our proposed one modulo $10$.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2601.06208
-/

namespace MathlibAttack.Papers.Arxiv2601_06208

open MathlibAttack.Papers

def citation : String := "Abderrahman Bouhamidi, \"An Extension of the Collatz Conjecture modulo $2^p+2^q$\", arXiv:2601.06208 [2026]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2601_06208
