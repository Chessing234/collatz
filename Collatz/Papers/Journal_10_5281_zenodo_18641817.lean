import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ziadah, "The Collatz Conjecture as a Quasi-Closed Cycle", 2026.

Title: The Collatz Conjecture as a Quasi-Closed Cycle

Abstract (from harvested metadata, truncated):
This paper derives an algebraic equivalence from the Collatz Conjecture using the transformation: x = (n - 1) / 4 Under this transformation, every positive natural number n can be written as: n = 4x + 1 This representation decomposes the positive integers into four quartic categories according to the fractional part of x: x = k x = k + 1/2 x = k + 1/4 x = k + 3/4 where k is an integer. Thus, the quartic lattice is: Q = { k, k + 1/4, k + 1/2, k + 3/4 | k ∈ Z } Rewriting the Collatz map: If n is even: T(n) = n / 2 If n is odd: T(n) = 3n + 1 In terms of x, the dynamics become two affine transformations: Even branch: x → ((4x + 1) / 8) - 1/4 Odd branch: x → 3x + 1 Therefore, the iteration is gov...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18641817
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18641817

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ziadah, \"The Collatz Conjecture as a Quasi-Closed Cycle\", Zenodo, DOI:10.5281/zenodo.18641817 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18641817
