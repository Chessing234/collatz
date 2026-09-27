import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerda Bennassar, "MI DEMOSTRACION DE LA CONJETURA DE COLLATZ", 2023.

Title: MI DEMOSTRACION DE LA CONJETURA DE COLLATZ

Abstract (from harvested metadata, truncated):
En este escrito, se analizan las propiedades de la raíz digital de los números y se busca una posible conexión con las secuencias de la Conjetura de Collatz.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/udqw7
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_udqw7

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerda Bennassar, \"MI DEMOSTRACION DE LA CONJETURA DE COLLATZ\", DOI:10.31219/osf.io/udqw7 [2023]."

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

end Collatz.Papers.Journal_10_31219_osf_io_udqw7
