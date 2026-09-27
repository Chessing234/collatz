import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Moftah, Khaled, "Block Format Solves the Collatz Conjecture", 2024.

Title: Block Format Solves the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Blocks are unit convergence between two consecutive odd numbers formed according to the three x plus one conjecture rules. The left odd number is the left hook, L, and the right odd number is the right hook, R. They include even numbers between their boundaries. They are divided into families (F1 = 5, 11, 17, … &amp; F2 = 1, 7, 11, … &amp; F3 = 3, 9, 15, …) and groups based on their group length (The number of the middle-even numbers between the two hooks). Blocks are taken individually and placed beside each other, similar to the domino tiles play, which, by their formulation, satisfies the conjecture rules. Formed chains reach number one in the convergence mode or continue generating odd positive numbers infinitely according to the generation mode. The final convergence to number one is...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.9734/jamcs/2024/v39i41880
-/

namespace Collatz.Papers.Journal_10_9734_jamcs_2024_v39i41880

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Moftah, Khaled, \"Block Format Solves the Collatz Conjecture\", Journal of Advances in Mathematics and Computer Science, DOI:10.9734/jamcs/2024/v39i41880 [2024]."

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

end Collatz.Papers.Journal_10_9734_jamcs_2024_v39i41880
