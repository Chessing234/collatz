import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for George M. Georgiou, "Encoding and Visualization in the Collatz Conjecture", arXiv:1811.00384 [2018].

Title: Encoding and Visualization in the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture is one of the easiest mathematical problems to state and yet it remains unsolved. For each $n\ge 2$ the Collatz iteration is mapped to a binary sequence and a corresponding unique integer which can recreate the iteration. The binary sequence is used to produce the Collatz curve, a 2-D visualization of the iteration on a grid, which, besides the aesthetics, provides a qualitative way for comparing iterations. Two variants of the curves are explored, the r-curves and on-change-turn-right curves. There is a scarcity of acyclic r-curves and only three r-curves were found having a cycle of minimum length greater than 4.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1811.00384
-/

namespace Collatz.Papers.Arxiv1811_00384

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "George M. Georgiou, \"Encoding and Visualization in the Collatz Conjecture\", arXiv:1811.00384 [2018]."

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


end Collatz.Papers.Arxiv1811_00384
