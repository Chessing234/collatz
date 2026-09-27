import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kamal Barghout, "On the Probabilistic Proof of the Convergence of the Collatz Conjecture", 2019.

Title: On the Probabilistic Proof of the Convergence of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
A new approach towards probabilistic proof of the convergence of the Collatz conjecture is described via identifying a sequential correlation of even natural numbers by divisions by 2 that follows a recurrent pattern of the form x,1,x,1… , where x represents divisions by 2 more than once. The sequence presents a probability of 50:50 of division by 2 more than once as opposed to division by 2 once over the even natural numbers. The sequence also gives the same 50:50 probability of consecutive Collatz even elements when counted for division by 2 more than once as opposed to division by 2 once and a ratio of 3:1. Considering Collatz function producing random numbers and over sufficient number of iterations, this probability distribution produces numbers in descending order that lead to the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1155/2019/6814378
-/

namespace Collatz.Papers.Journal_10_1155_2019_6814378

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kamal Barghout, \"On the Probabilistic Proof of the Convergence of the Collatz Conjecture\", Journal of Probability and Statistics, DOI:10.1155/2019/6814378 [2019]."

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

end Collatz.Papers.Journal_10_1155_2019_6814378
