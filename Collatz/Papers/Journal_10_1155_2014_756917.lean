import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Manfred Trümper, "The Collatz Problem in the Light of an Infinite Free Semigroup", 2014.

Title: The Collatz Problem in the Light of an Infinite Free Semigroup

Abstract (from harvested metadata, truncated):
The Collatz (or 3m+1 ) problem is examined in terms of a free semigroup on which suitable diophantine and rational functions are defined. The elements of the semigroup, called T-words, comprise the information about the Collatz operations which relate an odd start number to an odd end number, the group operation being the concatenation of T-words. This view puts the concept of encoding vectors, first introduced in 1976 by Terras, in the proper mathematical context. A method is described which allows to determine a one-parameter family of start numbers compatible with any given T-word. The result brings to light an intimate relationship between the Collatz 3m+1 problem and the 3m-1 problem. Also, criteria for the rise or fall of a Collatz sequence are derived and the important notion of...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1155/2014/756917
-/

namespace Collatz.Papers.Journal_10_1155_2014_756917

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Manfred Trümper, \"The Collatz Problem in the Light of an Infinite Free Semigroup\", Chinese Journal of Mathematics, DOI:10.1155/2014/756917 [2014]."

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

end Collatz.Papers.Journal_10_1155_2014_756917
