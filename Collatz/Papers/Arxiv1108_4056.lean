import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Thomas W. Lynch, "More Jabber about the Collatz Conjecture and a Closed Form for Detecting Cycles on Special Subsequences [Assertion: Collatz cycles]", arXiv:1108.4056 [2011].

Title: More Jabber about the Collatz Conjecture and a Closed Form for Detecting Cycles on Special Subsequences [Assertion: Collatz cycles]

Abstract (from OpenAlex metadata, truncated):
Professor Cadogan at the University of the West Indies identified special starting points that yield long subsequences where the normalization constant, k, is always one. I studied these special sequences and found an implicit mixed integer equation in closed form which if solved would produce seed values in cycling subsequences. Such cycles only occur among extremely large numbers, causing the equation to be difficult to solve numerically.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1108.4056
-/

namespace Collatz.Papers.Arxiv1108_4056

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Thomas W. Lynch, \"More Jabber about the Collatz Conjecture and a Closed Form for Detecting Cycles on Special Subsequences [Assertion: Collatz cycles]\", arXiv:1108.4056 [2011]."

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

end Collatz.Papers.Arxiv1108_4056
