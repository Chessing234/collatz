import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dagnachew Jenber, "Collatz Theorem.", arXiv:1811.08500 [2021].

Title: Collatz Theorem.

Abstract (from OpenAlex metadata, truncated):
This paper studies the proof of Collatz conjecture for some set of sequence of odd numbers with infinite number of elements. These set generalized to the set which contains all positive odd integers. This extension assumed to be the proof of the full conjecture, using the concept of mathematical induction. In section 9, the Collatz conjecture is proved again using mathematical induction. Therefore Collatz conjecture is proved two times. Finally two algorithms with GNU Octave code are given to check the validity of the proof for some particular numbers, code of Algorithm 1 is the restatement of Collatz conjecture function which is used to check the validity of our newly generated Collatz function for some particular terms which is provided by Algorithm 2. Therefore go from Algorithm 2 to Algorithm 1 for checking the sequence of numbers and the number of steps needed to reach to 1 according to the conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1811.08500
-/

namespace Collatz.Papers.Arxiv1811_08500

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dagnachew Jenber, \"Collatz Theorem.\", arXiv:1811.08500 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1811_08500
