import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Di Gruso, Massimo, "A Proof of the Collatz Conjecture Through Disjoint Partitions", 2026.

Title: A Proof of the Collatz Conjecture Through Disjoint Partitions

Abstract (from harvested metadata, truncated):
This paper presents a complete proof of the Collatz conjecture through the construction of a partition of positive integers into disjoint sets. Our proof establishes three key results: the completeness of our partition through strict monotonicity of pre-generators, the uniqueness of finite sequences converging to 1, and the identification of 1-4-1 as the only possible cycle. We demonstrate that our formalization is equivalent to the classical Collatz problem, thereby proving that every positive integer eventually reaches 1 under repeated application of the Collatz transformations. Our approach reveals the underlying structural properties that guarantee this convergence.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.14799759
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_14799759

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Di Gruso, Massimo, \"A Proof of the Collatz Conjecture Through Disjoint Partitions\", Zenodo, DOI:10.5281/zenodo.14799759 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_14799759
