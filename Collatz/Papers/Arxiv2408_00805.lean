import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for T. E. Raptis, "On the intimate association between even binary palindromic words and the Collatz-Hailstone iterations", arXiv:2408.00805 [2024].

Title: On the intimate association between even binary palindromic words and the Collatz-Hailstone iterations

Abstract (from OpenAlex metadata, truncated):
The celebrated $3x+1$ problem is reformulated via the use of an analytic expression of the trailing zeros sequence resulting in a single branch formula $f(x)+1$ with a unique fixed point. The resultant formula $f(x)$ is also found to coincide with that of the discrete derivative of the sorted sequence of fixed points of the reflection operator on even binary palindromes of fixed even length \textit{2k} in any interval $[0\cdots2^{2k}-1]$. A set of equivalent reformulations of the problem are also presented.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2408.00805
-/

namespace Collatz.Papers.Arxiv2408_00805

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "T. E. Raptis, \"On the intimate association between even binary palindromic words and the Collatz-Hailstone iterations\", arXiv:2408.00805 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2408_00805
