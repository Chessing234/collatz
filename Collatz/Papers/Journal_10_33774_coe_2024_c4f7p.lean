import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Taha Muhammad, "Collatz Sequence", 2024.

Title: Collatz Sequence

Abstract (from harvested metadata, truncated):
Abstract of Solving Collatz Sequence I started from a loop containing all positive numbers and performed Collatz law on each number x in the loop, obtained algebraic equations, and defined the values of x, which not belong to the set of natural numbers except 1. Then I applied Collatz laws and obtained the elements of the loop, which are {4, 2, 1}. S (n)= {n/2 or 3n+1, ..., 4,2,1} for all N+. Thus LS (n) = {4,2,1} for all N+. I added extra work to support my proof: 1- Graph 2- Sketch 3- Chart 4- Table 5- Pattern 5- [If LS (n)= {4,2,1} for r = 3k] True Then I proved that [LS (n) = {4, 2, 1} for r+3= 3(k+1)] True 6- [If LS (n) has no loop if for r = 3k+h, h&lt;3, h is a natural number] True Th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2024-c4f7p
-/

namespace Collatz.Papers.Journal_10_33774_coe_2024_c4f7p

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Taha Muhammad, \"Collatz Sequence\", DOI:10.33774/coe-2024-c4f7p [2024]."

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

end Collatz.Papers.Journal_10_33774_coe_2024_c4f7p
