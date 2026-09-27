import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "The Collatz Conjecture: A Resolution through Inverse Function Generative Completeness", 2024.

Title: The Collatz Conjecture: A Resolution through Inverse Function Generative Completeness

Abstract (from harvested metadata, truncated):
This article presents a novel resolution of the Collatz Conjecture, centered on the concept of Generative Completeness of the inverse Collatz function. We introduce and rigorously prove that for all N ∈ ℕ+, there exists a minimal generator mN = 1 such that all positive integers up to N can be generated through successive applications of the inverse Collatz function G. This key property, which we term "Generative Completeness", forms the cornerstone of our proof. Building upon this foundation, we establish several crucial results: The boundedness of all Collatz sequences The existence and uniqueness of cycles in Collatz sequences The nature of the unique cycle as {1, 4, 2} We then present three distinct approaches to resolving the Collatz Conjecture, all fundamentally rooted in the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202406.0256.v7
-/

namespace Collatz.Papers.Journal_10_20944_preprints202406_0256_v7

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"The Collatz Conjecture: A Resolution through Inverse Function Generative Completeness\", Preprints.org, DOI:10.20944/preprints202406.0256.v7 [2024]."

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

end Collatz.Papers.Journal_10_20944_preprints202406_0256_v7
