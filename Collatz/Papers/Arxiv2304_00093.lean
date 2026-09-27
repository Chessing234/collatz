import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gaurav Goyal, "Resolution of the 3n+1 Problem Using Inequality Relation Between Indices of 2 and 3", arXiv:2304.00093 [2023].

Title: Resolution of the 3n+1 Problem Using Inequality Relation Between Indices of 2 and 3

Abstract (from OpenAlex metadata, truncated):
Collatz conjecture states that an integer $n$ reduces to $1$ when certain simple operations are applied to it. Mathematically, the Collatz function is written as $f^k(n) = \frac{3^kn + C}{2^{z}}$, where $z, k, C \geq 1$. Suppose the integer $n$ violates Collatz conjecture by reappearing as $2^in$, where $i \geq 1$, then the equation modifies to $n \left(1 - \frac{3^k}{2^{z}2^i}\right) = \frac{C}{2^{z}2^i}$. The article takes an elementary approach to this problem by calculating the bounds on the values of $\frac{C}{2^{z}2^i}$ and $1 - \frac{3^k}{2^{z}2^i}$. Correspondingly, an upper limit on the integer $n$ is placed that can re-appear in the sequence. The integer $n$ lies in the $(-\infty, 5)$ range, and the limit on the number of odd steps is $k < 3$. Finally, it is shown that no integer chain exists that does not lead to 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2304.00093
-/

namespace Collatz.Papers.Arxiv2304_00093

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gaurav Goyal, \"Resolution of the 3n+1 Problem Using Inequality Relation Between Indices of 2 and 3\", arXiv:2304.00093 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2304_00093
