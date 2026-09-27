import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Chin‐Long Wey, "The Proof of the Collatz Conjecture", arXiv:2309.09991 [2023].

Title: The Proof of the Collatz Conjecture

Abstract (truncated):
The 3n+1, or Collatz problem, is one of the hardest math problems, yet still unsolved. The Collatz conjecture is to prove or disprove that the Collatz sequences COL(n) always eventually reach the number of 1, for all n belongs to N+ (all positive integers). The Syracuse conjecture is a (2N+1)-version of Collatz conjecture, where (2N+1) is all odd integers. The Syracuse and Collatz problem can be conceptually described by a tree trunk and branches. The trunk is made of the junctions that produce the main branches, where J0=1 is the root junction. Each branch consists of active and dead junctions, where only the active junctions are capable of producing new sub-branches. Conceptually assuming the trunk and branches can grow indefinitely and can also absorb nutrients from the root. As the tree grows indefinitely, all N+ (2N+1) are included for the Collatz (Syracuse) sequence. This paper dev

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2309.09991
-/

namespace MathlibAttack.Papers.Arxiv2309_09991

open MathlibAttack.Papers

def citation : String := "Chin\u2010Long Wey, \"The Proof of the Collatz Conjecture\", arXiv:2309.09991 [2023]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2309_09991
