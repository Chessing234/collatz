import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "A Bidirectional Approach to the Collatz Conjecture", arXiv:2505.02268 [2025].

Title: A Bidirectional Approach to the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The '''Collatz conjecture''' posits that iterating the function C(n) = n/2 for even ''n'' and C(n) = 3n+1 for odd ''n'' eventually reaches 1 from any positive starting integer. We present a complete resolution through '''dual dynamical analysis'''—a novel framework examining the interplay between forward generation sequences and backward convergence trajectories. The fundamental cycle \{1,4,2\} emerges as both the unique attractor for forward iteration and the minimal universal source for backward generation. This duality creates an inescapable mathematical structure ensuring convergence. Unlike traditional approaches that struggle with the apparent chaos of individual trajectories, our framework reveals how forward complexity masks backward simplicity, transforming an intractable analytical problem into one of structural necessity.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2505.02268
-/

namespace Collatz.Papers.Arxiv2505_02268

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"A Bidirectional Approach to the Collatz Conjecture\", arXiv:2505.02268 [2025]."

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

end Collatz.Papers.Arxiv2505_02268
