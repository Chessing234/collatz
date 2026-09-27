import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kirk O. Hahn, "Analysis of Collatz Conjecture Rules", 2024.

Title: Analysis of Collatz Conjecture Rules

Abstract (from harvested metadata, truncated):
Abstract A proof of the Collatz Conjecture is presented. Changing the perspective of the problem from looking at the pattern of the positive integers to looking at the conjecture rules made the proof possible. The conjecture rule for even numbers organizes all positive integers into unique sets and the rule for odd numbers interconnects the unique sets into dendritic pathways to “1.” Infinite loops, other than the minor 4-2-1 loop after reaching “1,” and values continually increasing to infinity are shown to be mathematically impossible. The proof predicted a general equation that shows all positive integers reach a final value of “1," and calculates the values and locations of the odd positive integers during the iterations for each tested positive integer. JEL classification numbers:...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.47260/tma/1411
-/

namespace Collatz.Papers.Journal_10_47260_tma_1411

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kirk O. Hahn, \"Analysis of Collatz Conjecture Rules\", Theoretical Mathematics & Applications, DOI:10.47260/tma/1411 [2024]."

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

end Collatz.Papers.Journal_10_47260_tma_1411
