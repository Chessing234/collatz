import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "Conditional Obstructions and Launch Renormalization in Accelerated Collatz Dynamics", 2026.

Title: Conditional Obstructions and Launch Renormalization in Accelerated Collatz Dynamics

Abstract (from harvested metadata, truncated):
This technical note studies the least-realizer problem for finite valuation words of the accelerated Collatz map and its connection to the single-window residue-axis formulation of the Effective Occupation Conjecture (EOC). The central result is an exact launch-state collapse: once the coarse 2-adic residue of a valuation word has stabilized to its least positive realizer r(D), the remaining transport state is determined by an actual accelerated Collatz iterate m_j^\ast. Consequently, an anomalously small realizer forces a long suffix of the valuation word to be the genuine orbit segment of a smaller integer. This produces a structural decomposition into bounded-period periodic behavior, cyc...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21935927
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21935927

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"Conditional Obstructions and Launch Renormalization in Accelerated Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21935927 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21935927
