import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Beksultan, Miras, "Collatz conjecture from ease to complexity"", 2026.

Title: Collatz conjecture from ease to complexity"

Abstract (from harvested metadata, truncated):
This paper presents a complete proof of the Collatz conjecture using a non‑standard mathematical framework that unifies number theory, analysis, and geometry through the mechanics of the infinite Rubik's cube. The work is divided into four parts. Part 1 introduces the author's original non‑standard number theory, including the concepts of Original Position (OP), Counter Position (CP), the reverse cycle (C_b), and the variation potential (V(P_P)). Part 2 develops a non‑standard analysis of number trajectories, proving that the set of natural numbers partitions as N = OP ∪ CP, where CP = {2^x : x ∈ N}, and demonstrating that every n ∈ OP possesses a strict descent property. Part 3 constructs a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21167755
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21167755

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Beksultan, Miras, \"Collatz conjecture from ease to complexity\"\", Zenodo, DOI:10.5281/zenodo.21167755 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21167755
