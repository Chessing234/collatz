import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wang, Guojiang, "The 4 (mod 6 ) Boundary Theorem: A Two-Phase Deterministic Proof Framework for the Collatz Conjecture", 2026.

Title: The 4 (mod 6 ) Boundary Theorem: A Two-Phase Deterministic Proof Framework for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz Conjecture posits that any positive integer s ∈ N + will invariably converge to the trivial limit cycle ( 4 , 2 , 1 ) under the iteration of the arithmetic operator f ( n ) . Traditionally analyzed as a pseudo-random walk, this paper demonstrates that the trajectory is governed by a rigid, two-phase dynamic boundary system. By mapping the expansion step to simultaneous linear congruences across the prime bases p 1 = 2 and p 2 = 3 , we prove via the Chinese Remainder Theorem (CRT) that every upward trajectory is injected into a unique, invariant boundary checkpoint defined by x ≡ 4 ( mod 6 ) . Once injected, the system exhibits a total phase transition where the Modulo 2 switch as...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20360502
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20360502

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wang, Guojiang, \"The 4 (mod 6 ) Boundary Theorem: A Two-Phase Deterministic Proof Framework for the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.20360502 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20360502
