import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Manfred Truemper, "Handles, Hooks, and Scenarios: A fresh Look at the Collatz Conjecture", 2006.

Title: Handles, Hooks, and Scenarios: A fresh Look at the Collatz Conjecture

Abstract (from harvested metadata, truncated):
An operational approach to the Collatz Conjecture is presented. Scenarios are defined as strings of characters "s" (for "spike") and "d" (for "down") which symbolize the Collatz operations (3m+1)/2 and m/2 in a Collatz Series connecting two odd integers, the startnumber and the endnumber. It is shown that a scenario determines uniquely four integers, called startperiod, startphase, endperiod, and endphase such that startnumber = startperiod x k minus startphase, and endnumber = endperiod x k minus endphase, where k is any natural number. Therefore, any scenario can be realized infinitely many times, with well-defined startnumber and endnumber for each realization. It is shown how the periods and phases for a given scenario are calculated. The results are used to prove that any odd (even)...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.48550/arxiv.math/0612228
-/

namespace Collatz.Papers.ArxivMath_0612228

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Manfred Truemper, \"Handles, Hooks, and Scenarios: A fresh Look at the Collatz Conjecture\", arXiv:math/0612228 [2006]."

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

end Collatz.Papers.ArxivMath_0612228
