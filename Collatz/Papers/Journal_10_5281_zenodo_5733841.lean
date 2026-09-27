import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jai Sharma et al., "Looping and Divergence in the Collatz Conjecture", 2021.

Title: Looping and Divergence in the Collatz Conjecture

Abstract (from harvested metadata, truncated):
In this paper, we investigate the possible scenarios in which a number does not satisfy the Collatz Conjecture. Specifically, we examine numbers which may have a looping Collatz reduction sequence as well as numbers which may lead to a diverging Collatz reduction sequence. In order to investigate these, we look at the parity of the numbers in a general Collatz reduction sequence. Further, we examine cases in which these parity cycles repeat themselves infinitely in the reduction sequence. Through the research conducted in the paper, we formulate a necessary condition for looping in the Collatz Conjecture. We also prove that if a number has a diverging reduction sequence, then it must generate an infinite non-repeating parity cycle.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.5733841
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_5733841

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jai Sharma et al., \"Looping and Divergence in the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.5733841 [2021]."

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

end Collatz.Papers.Journal_10_5281_zenodo_5733841
