import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Brent, Barry, "3x+1 dynamics on rationals with fixed denominator", arXiv:math/0204170 [2002].

Title: 3x+1 dynamics on rationals with fixed denominator

Abstract (from arXiv metadata, truncated):
We propose the existence of an infinite class of exact analogues of the 3x+1 conjecture for rational numbers with fixed denominators. For some other denominators, there are several attracting cycles, which exhibit scaling and covariance phenomena. We analyze these phenomena in terms of results of Bohm, Sontacchi and Lagarias.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/math/0204170
-/

namespace Collatz.Papers.ArxivMath_0204170

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Brent, Barry, \"3x+1 dynamics on rationals with fixed denominator\", arXiv:math/0204170 [2002]."

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

end Collatz.Papers.ArxivMath_0204170
