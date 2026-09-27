import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Richard Kaufman, "A Reduced Forward Collatz Algorithm: How Binary Strings Change Their Length Under 3x+1", arXiv:2301.07466 [2023].

Title: A Reduced Forward Collatz Algorithm: How Binary Strings Change Their Length Under 3x+1

Abstract (from OpenAlex metadata, truncated):
We developed an algorithm that easily goes from one odd number to the next odd number in binary representation for the reduced forward Collatz map (Syracuse function). The algorithm indicates when an odd number can grow or shrink to the next odd number based on the pattern of binary digits. The algorithm is also used to provide a simpler method for determining the change in binary string length for the reduced map than one found in the literature. Accordingly, an inspection of the binary digits for an odd number can determine the number of binary digits of the subsequent odd number. We also show some simple results for what the smallest number could be for a counterexample to the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2301.07466
-/

namespace Collatz.Papers.Arxiv2301_07466

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Richard Kaufman, \"A Reduced Forward Collatz Algorithm: How Binary Strings Change Their Length Under 3x+1\", arXiv:2301.07466 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2301_07466
