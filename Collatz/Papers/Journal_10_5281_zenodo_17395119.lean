import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rubendall, C. Mike "WildFacts", "Collatz Conjecture Proof via Lattice Embedding and Power-of-Two Lifting", 2026.

Title: Collatz Conjecture Proof via Lattice Embedding and Power-of-Two Lifting

Abstract (from harvested metadata, truncated):
We reformulate the Collatz iteration as a lattice embedding over stopping time and powersof two. This reveals an exact algebraic and topological structure underlying the conjecture. Byproving the lattice is connected and every vertical fiber intersects the 1-orbit, we obtain a directconstructive proof of the Collatz conjecture within ZFC

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17395119
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17395119

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rubendall, C. Mike \"WildFacts\", \"Collatz Conjecture Proof via Lattice Embedding and Power-of-Two Lifting\", Zenodo, DOI:10.5281/zenodo.17395119 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17395119
