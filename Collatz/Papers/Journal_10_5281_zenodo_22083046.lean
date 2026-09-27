import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fouad Bensmail, "Théorie congruentielle des nombres : primalité, factorisation, dynamique de Collatz et applications", 2026.

Title: Théorie congruentielle des nombres : primalité, factorisation, dynamique de Collatz et applications

Abstract (from harvested metadata, truncated):
Œuvre unifiée développant le crible congruentiel et ses applications : comptage exact des paires de premiers (jumeaux et généralisation), limites de la factorisation RSA, dynamique de Collatz (familles à forme close, grammaire 2-adique, domination des zéros, bornes de cycles), miroir additif de Goldbach, nombres de Carmichael, détection de clés faibles, et programme long terme (jalons M1–M4). Contributions originales : forme close universelle pour les familles convergentes de Collatz, opérateur d'effacement de bloc E, dualité 2↔3, monovariant de contraction sur le monde de 3, réduction de la conjecture à l'absence d'orbites pauvres en zéros, critère général de Carmichael à m formes, détecteu...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22083046
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22083046

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fouad Bensmail, \"Théorie congruentielle des nombres : primalité, factorisation, dynamique de Collatz et applications\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22083046 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22083046
