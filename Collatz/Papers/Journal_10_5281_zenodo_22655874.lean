import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Haruto Ariyoshi, "A Proof of the Collatz Conjecture via the Three-Period Cycle Structure and General Integration Formula in the Inverse Graph", 2026.

Title: A Proof of the Collatz Conjecture via the Three-Period Cycle Structure and General Integration Formula in the Inverse Graph

Abstract (from harvested metadata, truncated):
The Collatz conjecture asserts that for any positive integer, the sequence of operations (halving even numbers and tripling and adding one to odd numbers) always converges to 1. In this paper, we analyze the problem from the perspective of the inverse Collatz graph rooted at the main trunk \(2^{n}\). We show that the branching structure of odd numbers generated from this trunk exhibits a deterministic, self-replicating periodicity consisting of exactly three distinct morphological states. By formalizing this rule into a single general integration formula, we demonstrate the bijectivity (surjectivity and injectivity) of the generated index mapping onto the set of all odd integers. Consequentl...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22655874
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22655874

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Haruto Ariyoshi, \"A Proof of the Collatz Conjecture via the Three-Period Cycle Structure and General Integration Formula in the Inverse Graph\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22655874 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22655874
