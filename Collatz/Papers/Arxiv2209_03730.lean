import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Raouf Rajab, "Characteristic numbers and characteristic equations of parity vectors of Collatz sequences", arXiv:2209.03730 [2022].

Title: Characteristic numbers and characteristic equations of parity vectors of Collatz sequences

Abstract (from OpenAlex metadata, truncated):
The present work deals with the characterization of parity vectors of Collatz sequences (of finite and infinite length). Such a characterization leads to the determination of several numbers (integers or non-integers) that we call the characteristic numbers of a given parity vector. Some characteristic numbers are linked together by equations that can be called characteristic equations of the considered parity vector. If a parity vector v of finite length n contains the first n terms of a parity vector V of infinite length then all the characteristic numbers of v are considered as characteristic numbers of order n of the infinite vector V. The limits of nth order characteristic numbers when n tends to infinity constitute the absolute characteristic numbers of the infinite vector V and they allow determining its behavior and properties. In this paper, we study the properties of parity vectors of infinite length based on their characteristic numbers. Then, we establish the relations betw

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2209.03730
-/

namespace Collatz.Papers.Arxiv2209_03730

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Raouf Rajab, \"Characteristic numbers and characteristic equations of parity vectors of Collatz sequences\", arXiv:2209.03730 [2022]."

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

end Collatz.Papers.Arxiv2209_03730
