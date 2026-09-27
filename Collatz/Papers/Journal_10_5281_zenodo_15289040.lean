import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Winsor, Christian, "A Divisibility-Based Heuristic for the Collatz Conjecture", 2026.

Title: A Divisibility-Based Heuristic for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper revisits an earlier attempt of mine to approach the Collatz Conjecture; the open question of whether repeatedly halving even numbers and tripling-then-adding-one odd numbers always eventually reaches 1 no matter the starting number. The original draft introduced a way to group numbers by a divisibility property and claimed that a specific rule always moves numbers into a "smaller" group, which, combined with computer verification for small numbers, was accidentally presented as a complete logical proof of the conjecture. It was not, and on review the grouping tracks a divisibility property, not the actual size of the number, so showing a number moves to a "smaller" group says noth...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15289040
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15289040

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Winsor, Christian, \"A Divisibility-Based Heuristic for the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.15289040 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_15289040
