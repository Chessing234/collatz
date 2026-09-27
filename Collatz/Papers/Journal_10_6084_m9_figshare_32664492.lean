import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Umanah, Amaete, "Collatz Engine: A Public Computational System for Sequential Evaluation of the Collatz Map", 2026.

Title: Collatz Engine: A Public Computational System for Sequential Evaluation of the Collatz Map

Abstract (from harvested metadata, truncated):
Collatz Engine is a persistent computational system for sequentially evaluating the Collatz map over positive integers and recording finite computational behavior, including trajectories, stopping times, peak values, and record events.This technical report documents the system architecture, computation method, persistence model, data structure, integrity requirements, and public reporting layer of Collatz Engine. The system is designed as a public computational observatory that preserves state across interruptions and reports finite computational progress through a public dashboard.The report does not present a proof of the Collatz conjecture. It describes a finite computational system and t...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.32664492
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_32664492

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Umanah, Amaete, \"Collatz Engine: A Public Computational System for Sequential Evaluation of the Collatz Map\", figshare, DOI:10.6084/m9.figshare.32664492 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_6084_m9_figshare_32664492
