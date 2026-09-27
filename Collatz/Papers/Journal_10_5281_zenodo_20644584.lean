import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, "La Conjecture de Collatz : Lemmes exacts, obstruction LTE et test de tameness sous décorrélation asymptotique", 2026.

Title: La Conjecture de Collatz : Lemmes exacts, obstruction LTE et test de tameness sous décorrélation asymptotique

Abstract (from harvested metadata, truncated):
Description française : Ce dépôt contient la version 3 du préprint consacré à la conjecture de Collatz (problème 3x+1). Cette version intègre six corrections formelles issues d'une évaluation critique par un autre modèle de langage sur la v2, et synthétise cinq découvertes conditionnelles : (1) lemme exact sur la croissance sous-linéaire des phases pauvres, (2) falsification de la compensation locale par blocs, (3) conjecture de décorrelation asymptotique des valuations 2-adiques validée empiriquement, (4) test de tameness au sens de Foss-Tweedie par sous-échantillonnage adaptatif, et (5) fréquence positive des phases riches. Chaque découverte est soumise à une dialectique Thèse / Antithèse...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20644584
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20644584

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, \"La Conjecture de Collatz : Lemmes exacts, obstruction LTE et test de tameness sous décorrélation asymptotique\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20644584 [2026]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_20644584
