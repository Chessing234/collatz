import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Silvio L. Cordeiro, "Syracuse, Ancient City", 2011.

Title: Syracuse, Ancient City

Abstract (from harvested metadata, truncated):
Uma das maiores cidades gregas na Antiguidade, Siracusa situa-se na maior ilha do Mar Mediterrâneo - a Sicília - no cruzamento de vias marítimas milenares, freqüentada por povos diversos na história. A partir de um relato de viagem da equipe do Laboratório de Estudos sobre a Cidade Antiga (LABECA MAE USP) à Sicília, em 2007, o documentário dirigido por Silvio Luiz Cordeiro mostra as impressões de seis siracusanos sobre a sua cidade: entre os tempos de um mesmo lugar, do passado remoto à vivência do presente, a memória de uma cidade viva.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.11606/issn.2594-5939.revmaesupl.2011.113570
-/

namespace Collatz.Papers.Journal_10_11606_issn_2594_5939_revmaesupl_2011_113570

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Silvio L. Cordeiro, \"Syracuse, Ancient City\", Revista do Museu de Arqueologia e Etnologia. Suplemento, DOI:10.11606/issn.2594-5939.revmaesupl.2011.113570 [2011]."

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

end Collatz.Papers.Journal_10_11606_issn_2594_5939_revmaesupl_2011_113570
