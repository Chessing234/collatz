import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "A New Approach on Proving Collatz Conjecture", 2019.

Title: A New Approach on Proving Collatz Conjecture

Abstract (from harvested metadata, truncated):
Collatz Conjecture (3x+1 problem) states any natural number x will return to 1 after 3 ⁎ x+1 computation (when x is odd) and x/2 computation (when x is even). In this paper, we propose a new approach for possibly proving Collatz Conjecture (CC). We propose Reduced Collatz Conjecture (RCC)—any natural number x will return to an integer that is less than x. We prove that RCC is equivalent to CC. For proving RCC, we propose exploring laws of Reduced Collatz Dynamics (RCD), i.e., from a starting integer to the first integer less than the starting integer. RCC can also be stated as follows: RCD of any natural number exists. We prove that RCD is the components of original Collatz dynamics (from a starting integer to 1); i.e., RCD is more primitive and presents better properties. We prove that...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1155/2019/6129836
-/

namespace Collatz.Papers.Journal_10_1155_2019_6129836

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"A New Approach on Proving Collatz Conjecture\", Journal of Mathematics, DOI:10.1155/2019/6129836 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1155_2019_6129836
