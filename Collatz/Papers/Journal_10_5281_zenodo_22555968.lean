import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sousa Pereira Mario and Mazzoni Enzo, "La conjecture de Syracuse enfin démontrée ? : Étude mathématique détaillée concernant la conjecture de Syracuse via une approche inédite et novatrice — le cadre MSP²", 2026.

Title: La conjecture de Syracuse enfin démontrée ? : Étude mathématique détaillée concernant la conjecture de Syracuse via une approche inédite et novatrice — le cadre MSP²

Abstract (from harvested metadata, truncated):
Cet article introduit MSP² (écriture regroupée des étapes de Syracuse), une reformulation de la conjecture de Syracuse (Collatz) qui regroupe chaque étape impaire suivie de sa division par 2 inévitable en une seule opération. Cette écriture fait apparaître deux familles d’arbres inverses (racines 6q+1 et 6q−1), dont on établit l’exhaustivité vis-à-vis des vols impairs, ainsi qu’un Tableau Générateur (TG) qui organise systématiquement les changements de variable et les tests de parité associés à ces arbres. On y démontre plusieurs lois de périodicité (verticale, suivant l’axe Z, d’entrée et de sortie), une réduction de l’étude globale à des représentants canoniques, la construction récursive...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22555968
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22555968

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sousa Pereira Mario and Mazzoni Enzo, \"La conjecture de Syracuse enfin démontrée ? : Étude mathématique détaillée concernant la conjecture de Syracuse via une approche inédite et novatrice — le cadre MSP²\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22555968 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22555968
