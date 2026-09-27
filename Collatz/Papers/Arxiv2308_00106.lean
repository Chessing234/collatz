import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gaurav Goyal, "Is It Worth Testing Large Numbers for Collatz Conjecture?", arXiv:2308.00106 [2023].

Title: Is It Worth Testing Large Numbers for Collatz Conjecture?

Abstract (from OpenAlex metadata, truncated):
Starting with a positive odd integer $n$, apply a function $f(n)$ repetitively such that $f(n) = 3n + 1$ if $n \not\equiv 0 (\text{mod}\:2)$ or $f(n) = n/2$ if $n \equiv 0 (\text{mod}\:2)$. Let the sequence of all the odd integers obtained form an orbit $n, f^1(n) , f^2(n), \ldots, f^k(n), f^{k + 1}(n)$. The $k^{th}$ odd integer is written as $f^k(n) = (3^k + \mathbf{B(k)})/2^{\mathbf{z(k)}}$ where $\mathbf{B(k)}$ is the collection of terms without the coefficient $n$. We show that when $1 - \mathbf{B(k)}/(2^{\mathbf{z(k)}} n) \approx 1$, the condition for unbounded orbit is given by OEIS A022921. Further, if there exists at least one orbit for which $f^{k + 1}(n) = n$ when $(k + 1) < 3$, we show that there exists no orbit with $k + 1 > 3$ for which $f^{k + 1}(n) = n$. The final result is that the odd integers that can violate the Collatz conjecture are smaller than 5.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2308.00106
-/

namespace Collatz.Papers.Arxiv2308_00106

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gaurav Goyal, \"Is It Worth Testing Large Numbers for Collatz Conjecture?\", arXiv:2308.00106 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2308_00106
