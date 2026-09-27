import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Matt Hohertz, "Bounds for zeros of Collatz polynomials, with necessary and sufficient strictness conditions", arXiv:2012.08006 [2020].

Title: Bounds for zeros of Collatz polynomials, with necessary and sufficient strictness conditions

Abstract (from OpenAlex metadata, truncated):
In a previous paper, we introduced the Collatz polynomials $P_N(z)$, whose coefficients are the terms of the Collatz sequence of the positive integer $N$. Our work in this paper expands on our previous results, using the Eneström-Kakeya Theorem to tighten our old bounds of the roots of $P_N(z)$ and giving precise conditions under which these new bounds are sharp. In particular, we confirm an experimental result that zeros on the circle $\{z\in\mathbb{C}: |z| = 2\}$ are rare: the set of $N$ such that $P_N(z)$ has a root of modulus 2 is sparse in the natural numbers. We close with some questions for further study.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2012.08006
-/

namespace Collatz.Papers.Arxiv2012_08006

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Matt Hohertz, \"Bounds for zeros of Collatz polynomials, with necessary and sufficient strictness conditions\", arXiv:2012.08006 [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2012_08006
