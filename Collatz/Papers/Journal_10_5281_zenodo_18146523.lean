import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bagchi, Aditya, "Formal LEAN Validation of Collatz Conjecture", 2026.

Title: Formal LEAN Validation of Collatz Conjecture

Abstract (from harvested metadata, truncated):
This deposit contains the Lean 4 source code for the formal verification of the non-existence of non-trivial cycles and divergent trajectories in the Collatz system.The codebase implements a Deterministic Framework consisting of 16 interconnected lemmas (1A–2H) leading to the final contradictions in Theorem 1 (Non-Existence of Cycles) and Theorem 2 (Impossibility of Divergence). LEAN Verification Status: The entire formalization adheres to the highest standards of proof integrity: Tool: Lean 4 Theorem Prover / Mathlib. Integrity: The code contains zero unproven assertions (sorry or admit). Guarantee: The synthesis formally validates that the required Exponential Cost of Repair (Corollary 1H-...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18146523
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18146523

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bagchi, Aditya, \"Formal LEAN Validation of Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.18146523 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18146523
