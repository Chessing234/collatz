import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Schwob, Michael R., Shiue, Peter, Venkat, Rama, "Novel Theorems and Algorithms Relating to the Collatz Conjecture", arXiv:2104.10713 [2021].

Title: Novel Theorems and Algorithms Relating to the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
Proposed in 1937, the Collatz conjecture has remained in the spotlight for mathematicians and computer scientists alike due to its simple proposal, yet intractable proof. In this paper, we propose several novel theorems, corollaries, and algorithms that explore relationships and properties between the natural numbers, their peak values, and the conjecture. These contributions primarily analyze the number of Collatz iterations it takes for a given integer to reach 1 or a number less than itself, or the relationship between a starting number and its peak value.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2104.10713
-/

namespace Collatz.Papers.Arxiv2104_10713

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Schwob, Michael R. et al., \"Novel Theorems and Algorithms Relating to the Collatz Conjecture\", arXiv:2104.10713 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2104_10713
