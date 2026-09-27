import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for adityabagchi2002-boop, "adityabagchi2002-boop/LEAN-VALIDATED-PROOF-OF-COLLATZ-CONJECTURE: Finite-State Deterministic Validation of Collatz Conjecture (Formally Validated)", 2026.

Title: adityabagchi2002-boop/LEAN-VALIDATED-PROOF-OF-COLLATZ-CONJECTURE: Finite-State Deterministic Validation of Collatz Conjecture (Formally Validated)

Abstract (from harvested metadata, truncated):
This release contains the complete, axiom-free Lean 4 source code validating the results presented in the manuscript "Finite-State Deterministic Validation of the Collatz Conjecture" Verification Status: Engine: Lean 4 (Mathlib) Axiom Check: Passed (Standard Foundations Only; No custom axiom or sorry commands used). CI Status: Passing (Green Badge). Scope of Formalization: This repository formally verifies the two central pillars of the proof: The Perturbation Model (Theorem 1): Validates the structural impossibility of non-trivial integer cycles by proving the mutual exclusivity of the algebraic cycle condition and the 3-adic valuation constraints. The Modular Loop Framework (Theorem 2): Va...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18113610
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18113610

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "adityabagchi2002-boop, \"adityabagchi2002-boop/LEAN-VALIDATED-PROOF-OF-COLLATZ-CONJECTURE: Finite-State Deterministic Validation of Collatz Conjecture (Formally Validated)\", Zenodo, DOI:10.5281/zenodo.18113610 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18113610
