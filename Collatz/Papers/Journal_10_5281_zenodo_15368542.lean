import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for yu, gande, "A Concise Version of the Complete Proof of the Collatz Conjecture", 2025.

Title: A Concise Version of the Complete Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Abstract: This paper completely proves the Collatz conjecture that all iterative orbits can converge to 1. This paper first analyzes the common rules of iterative orbits that can converge to 1, and regards orbits with the same rules and trivial periodic orbits as a whole, which will help analyze the boundedness of all iterative orbits, and then analyzes the periodicity of iterative orbits, and finally proves the conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15368542
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15368542

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "yu, gande, \"A Concise Version of the Complete Proof of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.15368542 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_15368542
