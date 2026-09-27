import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lange, Mike, "The LNL Project (LSR): A Structural Framework for the Collatz Conjecture", 2026.

Title: The LNL Project (LSR): A Structural Framework for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Abstract This preprint presents the LNL (Lange Number Line) and LSR (Lange Structural Research) framework, a structural research program for investigating the Collatz Conjecture. Instead of studying individual trajectories, this work introduces a structural representation based on the Ironing Board Model, the Lange Pillar Graph (LSG), First Activation, the empirical Lange Constant, and a block-based DNA representation of Collatz trajectories. The manuscript clearly distinguishes between: mathematical definitions, rigorously proven local lemmas, empirical computational observations, and open research hypotheses. The objective of this work is not to claim a completed proof of the Collatz Conje...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21516496
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21516496

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lange, Mike, \"The LNL Project (LSR): A Structural Framework for the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.21516496 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21516496
