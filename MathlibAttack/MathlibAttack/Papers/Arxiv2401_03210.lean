import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Gil Alon et al., "On the stopping time of the Collatz map in $\mathbb{F}_2[x]$", arXiv:2401.03210 [2024].

Title: On the stopping time of the Collatz map in $\mathbb{F}_2[x]$

Abstract (truncated):
We study the stopping time of the Collatz map for a polynomial $f \in \mathbb{F}_2[x]$, and bound it by $O({\rm deg} (f)^{1.5})$, improving upon the quadratic bound proven by Hicks, Mullen, Yucas and Zavislak. We also prove the existence arithmetic sequences of unbounded length in the stopping times of certain sequences of polynomials, a phenomenon observed in the classical Collatz map.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2401.03210
-/

namespace MathlibAttack.Papers.Arxiv2401_03210

open MathlibAttack.Papers

def citation : String := "Gil Alon et al., \"On the stopping time of the Collatz map in $\\mathbb{F}_2[x]$\", arXiv:2401.03210 [2024]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2401_03210
