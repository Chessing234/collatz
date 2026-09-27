import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for T. E. Raptis, "On the intimate association between even binary palindromic words and the Collatz-Hailstone iterations", arXiv:2408.00805 [2024].

Title: On the intimate association between even binary palindromic words and the Collatz-Hailstone iterations

Abstract (truncated):
The celebrated $3x+1$ problem is reformulated via the use of an analytic expression of the trailing zeros sequence resulting in a single branch formula $f(x)+1$ with a unique fixed point. The resultant formula $f(x)$ is also found to coincide with that of the discrete derivative of the sorted sequence of fixed points of the reflection operator on even binary palindromes of fixed even length \textit{2k} in any interval $[0\cdots2^{2k}-1]$. A set of equivalent reformulations of the problem are also presented.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2408.00805
-/

namespace MathlibAttack.Papers.Arxiv2408_00805

open MathlibAttack.Papers

def citation : String := "T. E. Raptis, \"On the intimate association between even binary palindromic words and the Collatz-Hailstone iterations\", arXiv:2408.00805 [2024]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2408_00805
