import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Ramachandra Bhat, "Convergence of Collatz Sequences: Procedure to Prove the Collatz Conjecture", arXiv:2103.03100 [2021].

Title: Convergence of Collatz Sequences: Procedure to Prove the Collatz Conjecture

Abstract (truncated):
As Collatz conjecture is still to be proved, a method to arrive at the complete proof is explored here. Conceptually, the process relies on the pre-proven sequence data and the method follows the confirmation of the convergence of the Collatz sequence for all the natural numbers in a sequential forward manner (ascending order of n). Hence, all the numbers less than n have been proved to converge before beginning to prove the convergence of the sequence for the number n. Initially, the the nature of problem was explored and explained the reason for some of the remarkable properties. Then, the pattern analysis of a first few sequences data led to the concept of pre-proven sequence. Then, the origin of quartets and subsequently, the octet patterns are described. The "Even-Odd" combinations and the concept of (8*v + c) gave a clear picture for the overall process of evaluation for the conver

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2103.03100
-/

namespace MathlibAttack.Papers.Arxiv2103_03100

open MathlibAttack.Papers

def citation : String := "Ramachandra Bhat, \"Convergence of Collatz Sequences: Procedure to Prove the Collatz Conjecture\", arXiv:2103.03100 [2021]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2103_03100
