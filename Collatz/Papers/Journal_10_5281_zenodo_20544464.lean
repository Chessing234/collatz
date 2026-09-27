import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Borgatta, Piero, "Phantom Orbit Shadowing for the Collatz Conjecture: Verified Core, Two Barriers, and a Repositioning", 2026.

Title: Phantom Orbit Shadowing for the Collatz Conjecture: Verified Core, Two Barriers, and a Repositioning

Abstract (from harvested metadata, truncated):
Phantom Orbit Shadowing for the Collatz Conjecture: Verified Core, Two Barriers, and a Repositioning (version 4). This is a consolidation and repositioning version of an ongoing, AI-assisted personal research program on the Collatz conjecture by an independent researcher. It does not report progress toward a proof of the conjecture. Its purpose is to state precisely what is rigorously established, to identify the two distinct barriers the program runs into, to prove why the current approaches stop there, and to record the resulting decision about what to do next. This is not a proof of the Collatz conjecture, and v4 does not claim progress toward one. It is a mechanically verified core plus...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20544464
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20544464

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Borgatta, Piero, \"Phantom Orbit Shadowing for the Collatz Conjecture: Verified Core, Two Barriers, and a Repositioning\", Zenodo, DOI:10.5281/zenodo.20544464 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20544464
