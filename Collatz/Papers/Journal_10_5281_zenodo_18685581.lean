import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerdá Bennassar, "2-adic Structure of Tails and Survival Sets in the Collatz Dynamics", 2026.

Title: 2-adic Structure of Tails and Survival Sets in the Collatz Dynamics

Abstract (from harvested metadata, truncated):
This paper studies the 2-adic structure of the compressed Collatz dynamics from a purely arithmetic perspective. We prove that each tail level corresponds to a unique modular class and that the dynamics acts affinely within each of them. From this classification, the existence of non-trivial cycles in the classes with valuation at least two is ruled out, and restricted survival sets are introduced, which parametrize exactly the initial conditions compatible with avoiding descent for an arbitrary number of steps. The necessity of the defining restriction is established, and a deterministic upper bound for the measure of these sets is proved without additional hypotheses. The equivalence between the emptiness of the infinite survival set and the Collatz conjecture on the corresponding class...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18685581
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18685581

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerdá Bennassar, \"2-adic Structure of Tails and Survival Sets in the Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18685581 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18685581
