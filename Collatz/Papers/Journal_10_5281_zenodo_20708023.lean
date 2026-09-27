import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for mrDarkDuck, "mrDarkDuck/collatz-3d-attractor: How 3D Graphics and Claude Shannon Tamed the Collatz Conjecture: The Story of an Independent Assault", 2026.

Title: mrDarkDuck/collatz-3d-attractor: How 3D Graphics and Claude Shannon Tamed the Collatz Conjecture: The Story of an Independent Assault

Abstract (from harvested metadata, truncated):
How 3D Graphics and Claude Shannon Tamed the Collatz Conjecture: The Story of an Independent Assault Greetings, colleagues and independent thinkers! My name is Kirill. First, an important disclaimer: I have no formal connection to academic institutions or institutional science; I am an independent researcher. However, this exact status allowed me to look at the problem outside the boundaries and constraints of classical textbooks. The Collatz Conjecture (the 3n+1 problem) is the ultimate mathematical monster of the 20th century—a structural puzzle that has defeated some of the greatest minds in history. Paul Erdős once famously remarked that "mathematics is not yet ripe for such problems." T...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20708023
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20708023

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "mrDarkDuck, \"mrDarkDuck/collatz-3d-attractor: How 3D Graphics and Claude Shannon Tamed the Collatz Conjecture: The Story of an Independent Assault\", Zenodo, DOI:10.5281/zenodo.20708023 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20708023
