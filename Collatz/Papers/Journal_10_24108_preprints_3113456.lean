import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Владимир Трушников, "ГИПОТЕЗА КОЛЛАТЦА-часть1.  Доказательство отсутствия в алгоритме «3X+1»  закольцованных фрагментов.", 2025.

Title: ГИПОТЕЗА КОЛЛАТЦА-часть1.  Доказательство отсутствия в алгоритме «3X+1»  закольцованных фрагментов.

Abstract (from harvested metadata, truncated):
Статья посвящена анализу условий существования закольцованных фрагментов в алгоритмах, которые их содержат. Применение индуктивно-дедуктивного метода к алгоритмам вида «3X+d» (аналогичным алгоритму Коллатца) показало, что формирование таких фрагментов определяется отношением Xₙ/d. От того, является ли это отношение дробью или положительным целым числом, зависит, завершится ли последовательность кольцом, состоящим из нескольких «нечетных» чисел, или циклом типа «d⇒d».

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.24108/preprints-3113456
-/

namespace Collatz.Papers.Journal_10_24108_preprints_3113456

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Владимир Трушников, \"ГИПОТЕЗА КОЛЛАТЦА-часть1.  Доказательство отсутствия в алгоритме «3X+1»  закольцованных фрагментов.\", DOI:10.24108/preprints-3113456 [2025]."

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

end Collatz.Papers.Journal_10_24108_preprints_3113456
