import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yamamoto, Takeo, "Collatz Conjecture: A Formal Axiom System and Executable Framework Based on Structural Properties in Lean 4", 2026.

Title: Collatz Conjecture: A Formal Axiom System and Executable Framework Based on Structural Properties in Lean 4

Abstract (from harvested metadata, truncated):
This repository provides a formal axiom system for the Collatz conjecture, fully implemented and verified in the Lean 4 proof assistant. Rather than pursuing a standard ZFC arithmetic derivation, this work establishes that key structural properties of the Collatz map—such as loop prohibition, a deterministic two-step contraction mechanism, and confluent orbit merging—are provable as sorry-free theorems from standard integer axioms. Utilizing the Curry-Howard isomorphism, global convergence is adopted as an independent axiom justified by extensive empirical evidence and computational validation up to $2^{71}$. The resulting framework passes Lean's strict type-checker (CI-verified Green) and s...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20314162
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20314162

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yamamoto, Takeo, \"Collatz Conjecture: A Formal Axiom System and Executable Framework Based on Structural Properties in Lean 4\", Zenodo, DOI:10.5281/zenodo.20314162 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20314162
