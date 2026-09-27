import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Silvano Salvador, "La Congettura di Collatz e l'Analisi Ergodica dei Sistemi Dinamici Discreti", 2026.

Title: La Congettura di Collatz e l'Analisi Ergodica dei Sistemi Dinamici Discreti

Abstract (from harvested metadata, truncated):
La congettura di Collatz, conosciuta anche come problema 3n+1, congettura di Ulam, problema di Kakutani o problema di Hasse, rappresenta uno dei problemi irrisolti più semplici da enunciare e più difficili da dimostrare dell'intera matematica contemporanea...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17613/49k86-1q464
-/

namespace Collatz.Papers.Journal_10_17613_49k86_1q464

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Silvano Salvador, \"La Congettura di Collatz e l'Analisi Ergodica dei Sistemi Dinamici Discreti\", DOI:10.17613/49k86-1q464 [2026]."

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

end Collatz.Papers.Journal_10_17613_49k86_1q464
