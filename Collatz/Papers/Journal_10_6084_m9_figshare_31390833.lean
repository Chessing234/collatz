import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kalhori, Mohammad Reza, "The Proof of the Collatz Conjecture via Reverse Branching Analysis and Tree Incompatibility v2pdf", 2026.

Title: The Proof of the Collatz Conjecture via Reverse Branching Analysis and Tree Incompatibility v2pdf

Abstract (from harvested metadata, truncated):
This work presents a structural proof of the Collatz Conjecture based on two key ideas: Reverse Branching Analysis and Tree Incompatibility. The method examines the backward expansion of Collatz trajectories and demonstrates that incompatible branching structures prevent the existence of non‑trivial divergent paths. The analysis shows that every positive integer eventually reaches the 1–4–2–1 cycle, resolving the conjecture under the proposed framework.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.31390833
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_31390833

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kalhori, Mohammad Reza, \"The Proof of the Collatz Conjecture via Reverse Branching Analysis and Tree Incompatibility v2pdf\", figshare, DOI:10.6084/m9.figshare.31390833 [2026]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_31390833
