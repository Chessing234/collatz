import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for (sobeh), mahmoud sabri jaber, "The MSJS Theorem: A Complete Proof of the Collatz Conjecture via Pattern Invariance, Finite-State Reduction, and Loop Contraction", 2026.

Title: The MSJS Theorem: A Complete Proof of the Collatz Conjecture via Pattern Invariance, Finite-State Reduction, and Loop Contraction

Abstract (from harvested metadata, truncated):
This work presents a complete and rigorous proof of the Collatz conjecture, formalized as the MSJS Theorem. The proof is built upon a fundamental observation: the Collatz map is a network of recurring loops governed solely by the units digit. Every odd number has a mandatory entry into a specific even number, while every even number has two possible exits determined by the tens digit — one when X2 is even, and another when X2 is odd (a +5 offset). This simple rule confines all positive integers to a finite network of cycles that inevitably lead to the absorbing cycle 1 -> 4 -> 2 -> 1. The result is proven by exhaustive verification over the finite core (X3, X2, X1) consisting of exactly 1000...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21515413
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21515413

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "(sobeh), mahmoud sabri jaber, \"The MSJS Theorem: A Complete Proof of the Collatz Conjecture via Pattern Invariance, Finite-State Reduction, and Loop Contraction\", Zenodo, DOI:10.5281/zenodo.21515413 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21515413
