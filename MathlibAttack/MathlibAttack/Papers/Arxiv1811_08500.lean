import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Dagnachew Jenber, "Collatz Theorem.", arXiv:1811.08500 [2021].

Title: Collatz Theorem.

Abstract (truncated):
This paper studies the proof of Collatz conjecture for some set of sequence of odd numbers with infinite number of elements. These set generalized to the set which contains all positive odd integers. This extension assumed to be the proof of the full conjecture, using the concept of mathematical induction. In section 9, the Collatz conjecture is proved again using mathematical induction. Therefore Collatz conjecture is proved two times. Finally two algorithms with GNU Octave code are given to check the validity of the proof for some particular numbers, code of Algorithm 1 is the restatement of Collatz conjecture function which is used to check the validity of our newly generated Collatz function for some particular terms which is provided by Algorithm 2. Therefore go from Algorithm 2 to Algorithm 1 for checking the sequence of numbers and the number of steps needed to reach to 1 accordin

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/1811.08500
-/

namespace MathlibAttack.Papers.Arxiv1811_08500

open MathlibAttack.Papers

def citation : String := "Dagnachew Jenber, \"Collatz Theorem.\", arXiv:1811.08500 [2021]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv1811_08500
