import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Christian Koch et al., "Divisions by Two in Collatz Sequences: A Data Science Approach", 2020.

Title: Divisions by Two in Collatz Sequences: A Data Science Approach

Abstract (from harvested metadata, truncated):
The Collatz conjecture is an unsolved number theory problem. We approach the question by examining the divisions by two that are performed within Collatz sequences. Aside from classical mathematical methods, we use techniques of data science. Based on the analysis of 10,000 sequences we show that the number of divisions by two lies within clear boundaries. Building on the results, we develop and prove an equation to calculate the maximum possible number of divisions by two for any given a Collatz sequence. Whenever this maximum is reached, a sequence leads to the result one, as conjectured by Lothar Collatz. Furthermore, we show how many divisions by two are required for a cycle of a specific length. The findings are valuable for further investigations and could form the basis for a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.18052/www.scipress.com/ijpms.21.1
-/

namespace Collatz.Papers.Journal_10_18052_www_scipress_com_ijpms_21_1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Christian Koch et al., \"Divisions by Two in Collatz Sequences: A Data Science Approach\", International Journal of Pure Mathematical Sciences, DOI:10.18052/www.scipress.com/ijpms.21.1 [2020]."

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

end Collatz.Papers.Journal_10_18052_www_scipress_com_ijpms_21_1
