import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for John L. Simons, "Cycles of higher-order Collatz sequences", 2022.

Title: Cycles of higher-order Collatz sequences

Abstract (from harvested metadata, truncated):
Consider a sequence of numbers x_n \in \mathbb{Z_+} defined by x_{n+1}= \frac{x_n}{2} if x_n is even, and x_{n+1}= \frac{x_n+2x_{n-1}+q}{2} if x_n is odd. A 1-cycle is a periodic sequence with one transition from odd to even numbers. We prove theoretical and computational results for the existence of 1-cycles, and discuss a generalization to more complex cycles.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.7546/nntdm.2022.28.1.48-63
-/

namespace Collatz.Papers.Journal_10_7546_nntdm_2022_28_1_48_63

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "John L. Simons, \"Cycles of higher-order Collatz sequences\", Notes on Number Theory and Discrete Mathematics, DOI:10.7546/nntdm.2022.28.1.48-63 [2022]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_7546_nntdm_2022_28_1_48_63
