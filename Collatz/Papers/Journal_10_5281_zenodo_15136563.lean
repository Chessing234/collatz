import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Stalker, Eric, "Stalker's Resolution of the Collatz Conjecture", 2025.

Title: Stalker's Resolution of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper presents a complete proof of the Collatz Conjecture, establishing that all positive integers under the 3n+1 map converge to the cycle {1, 2, 4}. The proof employs a Lyapunov-style energy function with quantified cumulative decay, exclusion of non-trivial cycles via Diophantine approximation and Baker’s theorem, deterministic total stopping time bounds using the Syracuse function, and an ergodic-theoretic framework for long-term behavior. Computational verification up to $2^{20}$ confirms the absence of alternative cycles. This resolves a longstanding open problem in number theory.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15136563
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15136563

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Stalker, Eric, \"Stalker's Resolution of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.15136563 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_15136563
