import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "The Cylinder Horizon of the Accelerated 3x + 1 Map A Number-Theoretic Case Study in Descriptive Boundaries and Projectability Limits", 2026.

Title: The Cylinder Horizon of the Accelerated 3x + 1 Map A Number-Theoretic Case Study in Descriptive Boundaries and Projectability Limits

Abstract (from harvested metadata, truncated):
We record an elementary, self-contained observation about the accelerated Collatz mapT (m) = (3m + 1)/2ν2(3m+1) on odd integers. Let Dk = ν2(3mk + 1) be the discharge (valuation)sequence of an orbit. We show that a positive integer can reproduce a fixed eventually-periodiclow-discharge valuation word—one whose mean discharge satisfies ¯d < log2 3—for at most¯d−1 log2 m0 + O(1) steps.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20500707
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20500707

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"The Cylinder Horizon of the Accelerated 3x + 1 Map A Number-Theoretic Case Study in Descriptive Boundaries and Projectability Limits\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20500707 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20500707
