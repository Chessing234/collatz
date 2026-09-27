import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Audemir Loris, "Considerações sabre  a Conjectura de Collatz", 2024.

Title: Considerações sabre  a Conjectura de Collatz

Abstract (from harvested metadata, truncated):
Parte da comunidade cientifica tem dispendido considerável tempo e recursos para de alguma forma validar a conjectura de Collatz, inúmeros esforços tem logrado considerável avanço nesta direção, porém tal conjectura carecia de uma confirmação definitiva de que escolhido um número impar qualquer xi ∈ N∗, obteremos x(i+1) = 3xi + 1, sendo este um número x(i+1) par, divide-se o mesmo pelo número dois (sucessivamente) até obter-se outro número impar ∈ N∗ , repete-se o processo xn = 3x(n−1) + 1 e divisões por dois até que resulte finalmente um número igual 1.Neste trabalho apresentam-se deduções, algoritmos e equações que corroboram com tal proposição, embasam tal percepção e conclusão de que a c...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1590/scielopreprints.7664
-/

namespace Collatz.Papers.Journal_10_1590_scielopreprints_7664

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Audemir Loris, \"Considerações sabre  a Conjectura de Collatz\", DOI:10.1590/scielopreprints.7664 [2024]."

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

end Collatz.Papers.Journal_10_1590_scielopreprints_7664
