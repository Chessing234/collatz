import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ali M., "Proving Collatz Conjecture by finding cycles and diverging seeds", 2022.

Title: Proving Collatz Conjecture by finding cycles and diverging seeds

Abstract (from harvested metadata, truncated):
Abstract The Collatz conjecture can be formulated in this question: Do we guarantee reaching one after applying function f (Hereinafter called Collatz function) multiple times? f(x) = (3x+1, x|2) ∨ (x|2, x ∤ 2) In this paper, we discuss an approach to analyze Collatz conjecture nature for all qx + 1, q ∈ {1,3,5,7,..}. this approach builds a method to know the number of potential cycles for q x + 1, q ∈ {1,3,5,7,..}, x x, Mx ∈ ℂ. Multiple non-trivial cycles (numbers that form a cycle and does not reach one) were previously found where q ∈ {5, 181}. This paper will introduce equations that find non-trivial cycles, and therefore proving or disproving Collatz conjecture for any q.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.21203/rs.3.rs-2288122/v1
-/

namespace Collatz.Papers.Journal_10_21203_rs_3_rs_2288122_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ali M., \"Proving Collatz Conjecture by finding cycles and diverging seeds\", DOI:10.21203/rs.3.rs-2288122/v1 [2022]."

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

end Collatz.Papers.Journal_10_21203_rs_3_rs_2288122_v1
