import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Unknown, "On the feasibility of any finite evolution pattern in the Collatz problem", 2022.

Title: On the feasibility of any finite evolution pattern in the Collatz problem

Abstract (from harvested metadata, truncated):
Îïðåäåëåíî ïîíÿòèå ýâîëþöèîííîé ñõåìû â çàäà÷å Êîëëàòöà è äîêàçàíî, ÷òî ëþáàÿ ýâîëþöèîííàÿ ñõåìà êîíå÷íîé äëèíû ìîæåò áûòü ðåàëèçîâàíà â êàêîé-òî êîíêðåòíîé ïîñëåäîâàòåëüíîñòè Êîëëàòöà.Êëþ÷åâûå ñëîâà: ýâîëþöèîííàÿ ñõåìà, çàäà÷à Êîëëàòöà

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33184/mnkuomsh2t-2022-09-28.161
-/

namespace Collatz.Papers.Journal_10_33184_mnkuomsh2t_2022_09_28_161

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Unknown, \"On the feasibility of any finite evolution pattern in the Collatz problem\", Уфимская осенняя математическая школа - 2022. 2 часть, DOI:10.33184/mnkuomsh2t-2022-09-28.161 [2022]."

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

end Collatz.Papers.Journal_10_33184_mnkuomsh2t_2022_09_28_161
