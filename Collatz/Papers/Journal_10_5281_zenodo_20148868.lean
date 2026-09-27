import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nobuki Fujimoto et al., "Sigma-Cascade Observation of Collatz Orbit Confluence: Empirical Peak-Merge Enumeration and the n=96k Hypothesis — Rei-AIOS Paper 152 v0.1 DRAFT", 2026.

Title: Sigma-Cascade Observation of Collatz Orbit Confluence: Empirical Peak-Merge Enumeration and the n=96k Hypothesis — Rei-AIOS Paper 152 v0.1 DRAFT

Abstract (from harvested metadata, truncated):
We apply the σ-cascade methodology of Paper 151 Theorem 14 to forward Collatz (3x+1) orbits and report empirical observations on orbit confluence — the phenomenon that many distinct starting points reach exactly the same maximum ("peak") value. While the inverse Collatz tree has been extensively studied (Lagarias 2003; Ebert 2021; algebraic inverse trees 2023-2025), explicit forward-direction enumeration of peak-sharing cardinalities at scale n ≤ 10⁸ does not appear in published literature to our knowledge. (1) DIRECT ENUMERATION at n ≤ 10⁸: 11.5M unique Collatz peak values; among these, 219 are 'tier-3 super-hubs' (shared by > 1,414 starting points), with the largest peak 121,012,864 = 2⁷ ×...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20148868
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20148868

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nobuki Fujimoto et al., \"Sigma-Cascade Observation of Collatz Orbit Confluence: Empirical Peak-Merge Enumeration and the n=96k Hypothesis — Rei-AIOS Paper 152 v0.1 DRAFT\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20148868 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20148868
