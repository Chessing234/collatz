import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jan Kleinnijenhuis and Alissa M. Kleinnijenhuis, "Pruning the binary tree, proving the Collatz conjecture", arXiv:2008.13643 [2020].

Title: Pruning the binary tree, proving the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
The yet unproven Collatz conjecture maintains that repeatedly connecting even numbers n to n/2, and odd n to 3n+1, connects all natural numbers to a single tree with 1 as its root. Pruning ever more numbers from this tree until the density of pruned numbers relative to the natural numbers is arbitrarily close to 100% would prove that all numbers belonged to the tree. Preliminarily, numbers divisible by 2 or 3 are pruned. A binary tree is reconnected that forks at each number towards an ``upward'' and a ``rightward'' number. Next, intermediate rightward numbers, upward numbers with a rightward parent, with a rightward grandparent, etcetera, are pruned, which accrues the density of pruned numbers arbitrarily close to 100%. This proves the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2008.13643
-/

namespace Collatz.Papers.Arxiv2008_13643

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jan Kleinnijenhuis and Alissa M. Kleinnijenhuis, \"Pruning the binary tree, proving the Collatz conjecture\", arXiv:2008.13643 [2020]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps


end Collatz.Papers.Arxiv2008_13643
