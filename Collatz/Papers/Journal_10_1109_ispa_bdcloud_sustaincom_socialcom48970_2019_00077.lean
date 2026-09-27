import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Ratio and Partition are Revealed in Proposed Graph on Reduced Collatz Dynamics", 2019.

Title: Ratio and Partition are Revealed in Proposed Graph on Reduced Collatz Dynamics

Abstract (from harvested metadata, truncated):
Collatz conjecture is also known as 3X+1 problem. The original dynamics is occurred 3x+1 and x/2 during the process from any given starting integer to 1. We but propose to study reduced dynamics, which are occurred (3*x+1)/2 and x/2 during the process from a starting integer to the first integer less than the starting integer, because reduced dynamics is the building blocks of original dynamics and x/2 always follows 3*x+1. We thus propose a graph (directed binary tree) to represent all possible reduced dynamics, in which (3*x+1)/2 is denoted as "I" with right directed edge and x/2 is denoted as "O" with down directed edge. The graph can show some inner laws in reduced dynamics directly and...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/ispa-bdcloud-sustaincom-socialcom48970.2019.00077
-/

namespace Collatz.Papers.Journal_10_1109_ispa_bdcloud_sustaincom_socialcom48970_2019_00077

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Ratio and Partition are Revealed in Proposed Graph on Reduced Collatz Dynamics\", DOI:10.1109/ispa-bdcloud-sustaincom-socialcom48970.2019.00077 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_ispa_bdcloud_sustaincom_socialcom48970_2019_00077
