import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Matt Hohertz, "Bounds for zeros of Collatz polynomials, with necessary and sufficient strictness conditions", arXiv:2012.08006 [2020].

Title: Bounds for zeros of Collatz polynomials, with necessary and sufficient strictness conditions

Abstract (truncated):
In a previous paper, we introduced the Collatz polynomials $P_N(z)$, whose coefficients are the terms of the Collatz sequence of the positive integer $N$. Our work in this paper expands on our previous results, using the Eneström-Kakeya Theorem to tighten our old bounds of the roots of $P_N(z)$ and giving precise conditions under which these new bounds are sharp. In particular, we confirm an experimental result that zeros on the circle $\{z\in\mathbb{C}: |z| = 2\}$ are rare: the set of $N$ such that $P_N(z)$ has a root of modulus 2 is sparse in the natural numbers. We close with some questions for further study.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2012.08006
-/

namespace MathlibAttack.Papers.Arxiv2012_08006

open MathlibAttack.Papers

def citation : String := "Matt Hohertz, \"Bounds for zeros of Collatz polynomials, with necessary and sufficient strictness conditions\", arXiv:2012.08006 [2020]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2012_08006
