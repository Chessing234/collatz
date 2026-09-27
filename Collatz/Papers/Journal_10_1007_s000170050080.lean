import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for G�nther J. Wirsching, "�ber das 3 n + 1 Problem", 2000.

Title: �ber das 3 n + 1 Problem

Abstract (from harvested metadata, truncated):
Gu ¨nther Wirsching wurde 1960 in Wu ¨rzburg geboren.Er studierte 1979 bis 1985 in Mu ¨nchen und Bonn Mathematik, Physik und Philosophie.Seine Forschungen in der Mathematik begann er mit einer Diplomarbeit zur homologischen Algebra und Kategorientheorie.Im Fru ¨hjahr 1990 wurde er in Eichsta ¨tt mit einer Dissertation zur Differentialgeometrie promoviert.Danach wandte er sich versta ¨rkt der diskreten Mathematik und insbesondere den diskreten dynamischen Systemen zu.Seit 1996 arbeitet er an der Universita ¨t Eichsta ¨tt als Dozent fu ¨r Mathematik.In seiner Freizeit spielt er oft klassische Musik auf seiner Gitarre.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1007/s000170050080
-/

namespace Collatz.Papers.Journal_10_1007_s000170050080

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "G�nther J. Wirsching, \"�ber das 3 n + 1 Problem\", Elemente der Mathematik, DOI:10.1007/s000170050080 [2000]."

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

end Collatz.Papers.Journal_10_1007_s000170050080
