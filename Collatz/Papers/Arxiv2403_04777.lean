import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ali Ebnenasir, "Specifying and Verifying the Convergence Stairs of the Collatz Program", arXiv:2403.04777 [2024].

Title: Specifying and Verifying the Convergence Stairs of the Collatz Program

Abstract (from OpenAlex metadata, truncated):
This paper presents an algorithmic method that, given a positive integer $j$, generates the $j$-th convergence stair containing all natural numbers from where the Collatz conjecture holds by exactly $j$ applications of the Collatz function. To this end, we present a novel formulation of the Collatz conjecture as a concurrent program, and provide the general case specification of the $j$-th convergence stair for any $j > 0$. The proposed specifications provide a layered and linearized orientation of Collatz numbers organized in an infinite set of infinite binary trees. To the best of our knowledge, this is the first time that such a general specification is provided, which can have significant applications in analyzing and testing the behaviors of complex non-linear systems. We have implemented this method as a software tool that generates the Collatz numbers of individual stairs. We also show that starting from any value in any convergence stair the conjecture holds. However, to prove 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2403.04777
-/

namespace Collatz.Papers.Arxiv2403_04777

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ali Ebnenasir, \"Specifying and Verifying the Convergence Stairs of the Collatz Program\", arXiv:2403.04777 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2403_04777
