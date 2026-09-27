import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sharma J et al., "Exploring Algebraic Conditions on Counterexamples of the Collatz Conjecture", 2022.

Title: Exploring Algebraic Conditions on Counterexamples of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
In this paper, we investigate the possible scenarios in which a number does not satisfy the Collatz Conjecture, or the 3x+1 conjecture. Specifically, we examine the algebraic behavior of possible counterexamples of the Collatz Conjecture which may lead to a loop other than the trivial loop or unbounded divergence. In order to investigate these, we examine the parity of the numbers in a general Collatz reduction sequence. Further, we examine cases in which these parity cycles are infinitely periodic with finite period. Through the research conducted in the paper, we formulate a necessary algebraic condition for looping in the Collatz Conjecture. We also prove that if a number has a diverging reduction sequence, then it must generate an infinite aperiodic parity cycle.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.21203/rs.3.rs-2133810/v1
-/

namespace Collatz.Papers.Journal_10_21203_rs_3_rs_2133810_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sharma J et al., \"Exploring Algebraic Conditions on Counterexamples of the Collatz Conjecture\", DOI:10.21203/rs.3.rs-2133810/v1 [2022]."

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

end Collatz.Papers.Journal_10_21203_rs_3_rs_2133810_v1
