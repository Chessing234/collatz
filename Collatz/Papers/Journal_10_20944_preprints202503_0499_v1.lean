import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vicente PR., "Collatz Conjecture, Cycles, the 4n – 2 Series, and Positions Within the Series", 2025.

Title: Collatz Conjecture, Cycles, the 4n – 2 Series, and Positions Within the Series

Abstract (from harvested metadata, truncated):
We demonstrate that the Collatz conjecture generates cycles that consistently converge to the series defined by (4n - 2), ultimately terminating at the number 2. We propose an innovative algorithm that predicts the positions within this series during each cycle. Through a rigorously defined metric, we establish that these positions invariably converge to position 1, corresponding to the number 2 in the Collatz sequence (2 to 1 to 4 to 2). This approach not only confirms the validity of the conjecture for all positive integers but also provides a novel framework for understanding its cyclic behavior.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202503.0499.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202503_0499_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vicente PR., \"Collatz Conjecture, Cycles, the 4n – 2 Series, and Positions Within the Series\", DOI:10.20944/preprints202503.0499.v1 [2025]."

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

end Collatz.Papers.Journal_10_20944_preprints202503_0499_v1
