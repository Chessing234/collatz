import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Messerman, Hayden R. et al., "Generalized Collatz Functions: Cycle Lengths and Statistics", 2012.

Title: Generalized Collatz Functions: Cycle Lengths and Statistics

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.7710/2168-0620.1002
-/

namespace Collatz.Papers.Journal_10_7710_2168_0620_1002

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Messerman, Hayden R. et al., \"Generalized Collatz Functions: Cycle Lengths and Statistics\", International Journal of Undergraduate Research and Creative Activities, DOI:10.7710/2168-0620.1002 [2012]."

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

end Collatz.Papers.Journal_10_7710_2168_0620_1002
