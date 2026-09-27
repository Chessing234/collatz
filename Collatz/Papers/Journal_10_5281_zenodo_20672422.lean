import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, "Valuations 2-adiques et mesure de Haar nulle des orbites divergentes de Collatz", 2026.

Title: Valuations 2-adiques et mesure de Haar nulle des orbites divergentes de Collatz

Abstract (from harvested metadata, truncated):
Français : Ce dépôt contient la version 4 du préprint consacré à la conjecture de Collatz (problème 3x+1). Les versions antérieures (v1-v3) ont établi un spectromètre de divergence C1-C10, soumis à une falsification critique révélant un mur ergodique, puis resserré le cadre par un dénombrement combinatoire des séquences de valuations. La présente version introduit un théorème conditionnel de mesure de Haar nulle pour les orbites divergentes, structuré en sept piliers : uniformité 2-adique exacte (Lemme G.1), marginales géométriques exactes, dénombrement exact des séquences suspectes, argument Borel-Cantelli sur Z2, lemme ultramétrique, forçage par blocs de valuations unitaires, et éliminatio...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20672422
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20672422

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, \"Valuations 2-adiques et mesure de Haar nulle des orbites divergentes de Collatz\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20672422 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20672422
