import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nobuki Fujimoto et al., "Sigma-Cascade Observation of Collatz Orbit Confluence: 10^9 Scan + G_3 Subgraph Framework + Erratum E3 + Lemma 5d.1 Lean 4 Mechanized — Rei-AIOS Paper 152 v0.3 DRAFT", 2026.

Title: Sigma-Cascade Observation of Collatz Orbit Confluence: 10^9 Scan + G_3 Subgraph Framework + Erratum E3 + Lemma 5d.1 Lean 4 Mechanized — Rei-AIOS Paper 152 v0.3 DRAFT

Abstract (from harvested metadata, truncated):
Paper 152 v0.3 update. Parent v0.2 DOI 10.5281/zenodo.20149662; concept root v0.1 DOI 10.5281/zenodo.20148868. We apply Paper 151 Theorem 14 (sigma-cascade) to forward Collatz (3x+1) orbits at scale n 10^8" was correct. (D) DISSOCIATION at 10^9: n=96k strengthened + class 21 weakened = independent claims

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20148867
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20148867

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nobuki Fujimoto et al., \"Sigma-Cascade Observation of Collatz Orbit Confluence: 10^9 Scan + G_3 Subgraph Framework + Erratum E3 + Lemma 5d.1 Lean 4 Mechanized — Rei-AIOS Paper 152 v0.3 DRAFT\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20148867 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20148867
