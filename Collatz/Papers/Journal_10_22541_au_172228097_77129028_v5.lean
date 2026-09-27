import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Guillermo Wells Abascal, "Monotonicity and Convergence in the Collatz Conjecture: the Tendency of Integers to Reach 1", 2025.

Title: Monotonicity and Convergence in the Collatz Conjecture: the Tendency of Integers to Reach 1

Abstract (from harvested metadata, truncated):
The Collatz conjecture declares that every positive integer will eventually reach 1 when subjected to a simple iterative process: if the number is even, it is divided by 2, and if it is odd, it is multiplied by 3 and then increased by 1. Despite the straightforward nature of these rules, a general proof of the conjecture remains elusive. For the above, this study introduces an alternative interpretation of the conjecture. This approach involves multiplying an odd integer N 1 by 3 and subsequently adding the largest power-of-2 factor within N 1 . Repeated iterations of this alternative process show that any initial odd integer N 1 will eventually convert into a power of 2, leading the sequence towards convergence. The behavior of the sequence was studied by representing integers as a power...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.22541/au.172228097.77129028/v5
-/

namespace Collatz.Papers.Journal_10_22541_au_172228097_77129028_v5

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Guillermo Wells Abascal, \"Monotonicity and Convergence in the Collatz Conjecture: the Tendency of Integers to Reach 1\", DOI:10.22541/au.172228097.77129028/v5 [2025]."

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

end Collatz.Papers.Journal_10_22541_au_172228097_77129028_v5
