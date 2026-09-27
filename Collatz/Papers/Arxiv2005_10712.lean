import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hassan Sedaghat, "Dual Nature of Orbits of the Divide-or-Choose 2 Rule: A Quadratic Collatz-type Recursion", arXiv:2005.10712 [2020].

Title: Dual Nature of Orbits of the Divide-or-Choose 2 Rule: A Quadratic Collatz-type Recursion

Abstract (from OpenAlex metadata, truncated):
We obtain a complete characterization of all orbits of a quadratic Collatz-type recursion called the divide-or-choose-2 rule. Each orbit either ends in a cycle whose period depends on the initial value or it goes to infinity. We specify which initial values generate periodic orbits, and also show that all other initial values generate orbits that go to infinity.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2005.10712
-/

namespace Collatz.Papers.Arxiv2005_10712

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hassan Sedaghat, \"Dual Nature of Orbits of the Divide-or-Choose 2 Rule: A Quadratic Collatz-type Recursion\", arXiv:2005.10712 [2020]."

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


end Collatz.Papers.Arxiv2005_10712
