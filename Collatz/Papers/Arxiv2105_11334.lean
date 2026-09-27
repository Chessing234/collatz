import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rolf Bruun and Sourangshu Ghosh, "The Collatz Graph as Flow-Diagram, The Copenhagen Graph and the different Algorithms for generating The Collatz Odd Series.", arXiv:2105.11334 [2021].

Title: The Collatz Graph as Flow-Diagram, The Copenhagen Graph and the different Algorithms for generating The Collatz Odd Series.

Abstract (from OpenAlex metadata, truncated):
By defining the Adjacency-Matrix for the Collatz Graph it is shown that it is possible, from the Adjacency-Matrix, to generate a 'picture' which defines the Flow-Diagram for the Collatz Graph. In a sense the Flow-Diagram is the Collatz Graph. While defining a Double 2D Matrix containing all odd numbers it is shown, that the 3N+1-Problem is in fact a problem concerning Groups of values not only individual Values. This implicates, that it is possible to predict the number of Operations needed to reach the Origo/Root 1 for a Group of values, if the number of Operations is known for a single Value in the Group. After the formal analysis of the 'Double 2D Matrix' a group of five Algorithms is investigated. Based on the fact that two different Algorithms (with different rules) can generate identical Odd-Series and the fact that two of the Algorithms are able to generate identical 'Branching-codes' in both directions UP and DOWN in a (binary) Tree, it is concluded that Collatz Conjecture is T

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2105.11334
-/

namespace Collatz.Papers.Arxiv2105_11334

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rolf Bruun and Sourangshu Ghosh, \"The Collatz Graph as Flow-Diagram, The Copenhagen Graph and the different Algorithms for generating The Collatz Odd Series.\", arXiv:2105.11334 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2105_11334
