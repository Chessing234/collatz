import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Peter David Van De Bogart, "A Framework for the Collatz Conjecture", 2025.

Title: A Framework for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
A Framework for the Collatz conjecture by establishing three results: (1) the 2-adic valuation of 3n+1 for odd n follows a geometric distribution with parameter 1/2, giving E[k] = 2; (2) this implies the expected energy change per odd step is log₂(3) - 2 ≈ -0.415, guaranteeing convergence; (3) non-trivial cycles are impossible because cycle closure requires 3^m = 2^S for positive integers, which contradicts the irrationality of log₂(3). Combined, these results prove every positive integer eventually reaches 1. "Author's note (Dec 2025): This work presents a framework and conjecture, not a complete proof. The core structural insight awaits rigorous formalization."

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18024089
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18024089

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Peter David Van De Bogart, \"A Framework for the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18024089 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18024089
