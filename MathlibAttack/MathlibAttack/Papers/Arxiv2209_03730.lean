import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Raouf Rajab, "Characteristic numbers and characteristic equations of parity vectors of Collatz sequences", arXiv:2209.03730 [2022].

Title: Characteristic numbers and characteristic equations of parity vectors of Collatz sequences

Abstract (truncated):
The present work deals with the characterization of parity vectors of Collatz sequences (of finite and infinite length). Such a characterization leads to the determination of several numbers (integers or non-integers) that we call the characteristic numbers of a given parity vector. Some characteristic numbers are linked together by equations that can be called characteristic equations of the considered parity vector. If a parity vector v of finite length n contains the first n terms of a parity vector V of infinite length then all the characteristic numbers of v are considered as characteristic numbers of order n of the infinite vector V. The limits of nth order characteristic numbers when n tends to infinity constitute the absolute characteristic numbers of the infinite vector V and they allow determining its behavior and properties. In this paper, we study the properties of parity vec

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2209.03730
-/

namespace MathlibAttack.Papers.Arxiv2209_03730

open MathlibAttack.Papers

def citation : String := "Raouf Rajab, \"Characteristic numbers and characteristic equations of parity vectors of Collatz sequences\", arXiv:2209.03730 [2022]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2209_03730
