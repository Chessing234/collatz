import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Taha Muhammad, "Collatz Sequence Solution (2nd Way)", 2024.

Title: Collatz Sequence Solution (2nd Way)

Abstract (from harvested metadata, truncated):
Abstract of Collatz Sequence Solution (2nd Way) I discovered a fact in Collatz Sequence: S (n) = {a, b, c,…,w} ⇒ LS(n) = LS(a) = LS(b) = LS(c) = …. = LS (w) … (Fact1) n, a, b, c, w, r ∈ N_+, LS(n) = {4,2,1} when n ∈ {1,2,3,4,5, …, r-1} Let LS(r) = {4,2,1} when n ∈ Z = {1,2,3,4,5, …, r-1, r} Part a) If (r+1) ∈ (N_even), and I proved LS(r+1) = {4,2,1} ⇒ LS(n) = {4,2,1} for all even #s Part b) If (r+1) ∈ (N_odd), and I proved LS(r+1) = {4,2,1} by part a. Therefore LS(N) = {4,2,1} for all n ∈N.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2024-f4j0z-v4
-/

namespace Collatz.Papers.Journal_10_33774_coe_2024_f4j0z_v4

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Taha Muhammad, \"Collatz Sequence Solution (2nd Way)\", DOI:10.33774/coe-2024-f4j0z-v4 [2024]."

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

end Collatz.Papers.Journal_10_33774_coe_2024_f4j0z_v4
