import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mike Winkler, "New results on the stopping time behaviour of the Collatz 3x + 1 function", arXiv:1504.00212 [2015].

Title: New results on the stopping time behaviour of the Collatz 3x + 1 function

Abstract (from OpenAlex metadata, truncated):
Let $σ_n=\lfloor1+n\cdot\log_23\rfloor$. For the Collatz 3x + 1 function exists for each $n\in\mathbb{N}$ a set of different residue classes $(\text{mod}\ 2^{σ_n})$ of starting numbers $s$ with finite stopping time $σ(s)=σ_n$. Let $z_n$ be the number of these residue classes for each $n\geq0$ as listed in the OEIS as A100982. It is conjectured that for each $n\geq4$ the value of $z_n$ is given by the formula \begin{align*} z_n=\frac{(m+n-2)!}{m!\cdot(n-2)!}-\sum_{i=2}^{n-1}\binom{\big\lfloor\frac{3(n-i)+δ}{2}\big\rfloor}{n-i}\cdot z_i, \end{align*} where $m=\big\lfloor(n-1)\cdot\log_23\big\rfloor-(n-1)$ and $δ\in\mathbb{Z}$ assumes different values within the sum at intervals of 5 or 6 terms. This allows us to create an iterative algorithm which generates $z_n$ for each $n>6$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1504.00212
-/

namespace Collatz.Papers.Arxiv1504_00212

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mike Winkler, \"New results on the stopping time behaviour of the Collatz 3x + 1 function\", arXiv:1504.00212 [2015]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1504_00212
