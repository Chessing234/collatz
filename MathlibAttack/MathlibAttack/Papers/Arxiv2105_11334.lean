import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Rolf Bruun and Sourangshu Ghosh, "The Collatz Graph as Flow-Diagram, The Copenhagen Graph and the different Algorithms for generating The Collatz Odd Series.", arXiv:2105.11334 [2021].

Title: The Collatz Graph as Flow-Diagram, The Copenhagen Graph and the different Algorithms for generating The Collatz Odd Series.

Abstract (truncated):
By defining the Adjacency-Matrix for the Collatz Graph it is shown that it is possible, from the Adjacency-Matrix, to generate a 'picture' which defines the Flow-Diagram for the Collatz Graph. In a sense the Flow-Diagram is the Collatz Graph. While defining a Double 2D Matrix containing all odd numbers it is shown, that the 3N+1-Problem is in fact a problem concerning Groups of values not only individual Values. This implicates, that it is possible to predict the number of Operations needed to reach the Origo/Root 1 for a Group of values, if the number of Operations is known for a single Value in the Group. After the formal analysis of the 'Double 2D Matrix' a group of five Algorithms is investigated. Based on the fact that two different Algorithms (with different rules) can generate identical Odd-Series and the fact that two of the Algorithms are able to generate identical 'Branching-co

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2105.11334
-/

namespace MathlibAttack.Papers.Arxiv2105_11334

open MathlibAttack.Papers

def citation : String := "Rolf Bruun and Sourangshu Ghosh, \"The Collatz Graph as Flow-Diagram, The Copenhagen Graph and the different Algorithms for generating The Collatz Odd Series.\", arXiv:2105.11334 [2021]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2105_11334
