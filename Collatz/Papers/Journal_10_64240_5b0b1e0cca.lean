import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Barmak Honarvar, "Collatz dynamics as an almost circle rotation with bounded error", 2026.

Title: Collatz dynamics as an almost circle rotation with bounded error

Abstract (from harvested metadata, truncated):
If Collatz iterates are nearly an irrational circle rotation, what does that change about how we should look for a proof?

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.64240/5b0b1e0cca
-/

namespace Collatz.Papers.Journal_10_64240_5b0b1e0cca

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Barmak Honarvar, \"Collatz dynamics as an almost circle rotation with bounded error\", DOI:10.64240/5b0b1e0cca [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_64240_5b0b1e0cca
