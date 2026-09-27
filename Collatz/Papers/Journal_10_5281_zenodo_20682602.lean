import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, "Arithmetic Lemmas on the Modular Structure of the 3n+1 Map", 2026.

Title: Arithmetic Lemmas on the Modular Structure of the 3n+1 Map

Abstract (from harvested metadata, truncated):
Français : Ce dépôt contient la version 6 du préprint consacré à la conjecture de Syracuse (problème 3n+1). Les versions antérieures (v1-v5) ont exploré des voies modulaires, ergodiques et arithmétiques, dont certaines se sont révélées incompletes sous falsification interne. La présente version ne retient que huit lemmes arithmétiques rigoureusement prouvés sur la structure modulaire 2-adique de l'application accélérée, ainsi qu'une réduction conditionnelle de la conjecture à une question diophantienne finie et explicite. Elle ne prétend pas démontrer la conjecture de Syracuse. Les données empiriques (200 000+ trajectoires) constituent un support expérimental, non une preuve. Le document est...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20682602
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20682602

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Antoine Couet and Moonshot AI / Kimi K 2.6 Thinking, \"Arithmetic Lemmas on the Modular Structure of the 3n+1 Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20682602 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20682602
