import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Feng J., "Using Full Binary Directed Tree Proof the Collatz Conjecture", 2024.

Title: Using Full Binary Directed Tree Proof the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We use binary string to represent a natural number and show the composite procedure of odd-number and even-number functions, thus we propose full binary directed tree to represent the set of natural numbers and give another partition the natural number set to three sets: pure odd, pure even and mixed number. For the Collatz conjecture we make use of the parity of a natural number to analyse the sequence of iteration (or composite) of Collatz function and reduced Collatz function analog to the inverse function. We give tabular and binary strings to the algebra expression to state the sequence of Collatz, this is the key topic to proof the conjecture: the discrete powers of 2 can be changed to ultimately continuous powers of 2, finally get to pure even number and to the smallest number 1....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202405.0510.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202405_0510_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Feng J., \"Using Full Binary Directed Tree Proof the Collatz Conjecture\", DOI:10.20944/preprints202405.0510.v1 [2024]."

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

end Collatz.Papers.Journal_10_20944_preprints202405_0510_v1
