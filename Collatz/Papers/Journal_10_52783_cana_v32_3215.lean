import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for H R Vidyashree, "Visualizing and Proving the Collatz Conjecture: Ananta-Graph Approach", 2025.

Title: Visualizing and Proving the Collatz Conjecture: Ananta-Graph Approach

Abstract (from harvested metadata, truncated):
The Collatz Conjecture, proposed by Lothar Collatz in 1937, is an unsolved mathematical problem often called the “3x+1 problem” or the “Hailstone sequence”. It suggests that starting with any positive integer and applying a specific process: dividing an even number by 2 or multiplying an odd number by 3 and adding 1 will eventually result in the sequence reaching the cycle 4, 2, 1 regardless of the starting value. Despite its simplicity, no one has been able to prove or disprove this conjecture for all positive numbers. The behaviour of the Collatz Conjecture can also be illustrated through a graphical representation, showing how the sequence for different starting numbers evolves before reaching the repeating cycle of 4, 2, 1. In this paper, we highlight the various graphical...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.52783/cana.v32.3215
-/

namespace Collatz.Papers.Journal_10_52783_cana_v32_3215

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "H R Vidyashree, \"Visualizing and Proving the Collatz Conjecture: Ananta-Graph Approach\", Communications on Applied Nonlinear Analysis, DOI:10.52783/cana.v32.3215 [2025]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_52783_cana_v32_3215
