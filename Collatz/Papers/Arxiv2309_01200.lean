import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jishe Feng, "Proof the Collatz Conjecture by a new view of natural numbers", arXiv:2309.01200 [2023].

Title: Proof the Collatz Conjecture by a new view of natural numbers

Abstract (from OpenAlex metadata, truncated):
The two main strategies used in this study are the binary representation and the decomposition of a natural number into many compound functions of odd function and even function. The Collatz conjecture regarding odd even numbers in number theory can be examined and discussed using them in this way: The sequence created by the finite iterations of the Collatz function becomes the ultimately periodic sequence if any natural number is the beginning value, proving the conjecture that has been held for 85 years.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2309.01200
-/

namespace Collatz.Papers.Arxiv2309_01200

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jishe Feng, \"Proof the Collatz Conjecture by a new view of natural numbers\", arXiv:2309.01200 [2023]."

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

end Collatz.Papers.Arxiv2309_01200
