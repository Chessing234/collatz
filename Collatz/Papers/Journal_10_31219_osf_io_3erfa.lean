import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerda Bennassar, "LA CONJETURA DE COLLATZ. Orden y armonía en los números de las secuencias.", 2019.

Title: LA CONJETURA DE COLLATZ. Orden y armonía en los números de las secuencias.

Abstract (from harvested metadata, truncated):
Propongo una tabla numérica en la que se demuestra visualmente que las secuencias formadas con el algoritmo de Collatz acaban siempre en el número 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/3erfa
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_3erfa

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerda Bennassar, \"LA CONJETURA DE COLLATZ. Orden y armonía en los números de las secuencias.\", DOI:10.31219/osf.io/3erfa [2019]."

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

end Collatz.Papers.Journal_10_31219_osf_io_3erfa
