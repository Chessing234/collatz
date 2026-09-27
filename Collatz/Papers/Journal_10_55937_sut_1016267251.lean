import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tomoaki Mimuro, "On certain simple cycles of the Collatz conjecture", 2001.

Title: On certain simple cycles of the Collatz conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture is that there exists a positive integer n which satisfies fn(m)=1 for any integer m≥3, where f is the function on the rational number field defined by f(m)=m/2 if the numerator of m is even and f(m)=(3m+1)/2 if the numerator of m is odd. Let m be a rational number such that fn(m)=m>1. Then we show that, if m has some simple sequences, then the total number of positive integer m is finite, by estimating f(m)−m.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.55937/sut/1016267251
-/

namespace Collatz.Papers.Journal_10_55937_sut_1016267251

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tomoaki Mimuro, \"On certain simple cycles of the Collatz conjecture\", SUT Journal of Mathematics, DOI:10.55937/sut/1016267251 [2001]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_55937_sut_1016267251
