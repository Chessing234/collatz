import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Abderrahman Bouhamidi, "Weakly and Strongly Admissible Triplets for a Collatz-Type Map", arXiv:2601.17573 [2026].

Title: Weakly and Strongly Admissible Triplets for a Collatz-Type Map

Abstract (from OpenAlex metadata, truncated):
In this paper, we investigate a class of Collatz-like problems associated with weakly and strongly admissible triplets of integers. This framework extends the classical Collatz mapping, providing a systematic method for generating triplets with convergence to cycles, thereby bypassing the difficulties inherent in solving Diophantine equations. We introduce several special families of admissible triplets and establish general structural properties. In addition, we propose conjectures that generalize the classical Collatz conjecture. Bounds on the lengths of potential non-trivial cycles are derived and analyzed, and two algorithms are presented for computing lower bounds on cycle lengths. Finally, experimental tests are given to illustrate our approach.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2601.17573
-/

namespace Collatz.Papers.Arxiv2601_17573

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Abderrahman Bouhamidi, \"Weakly and Strongly Admissible Triplets for a Collatz-Type Map\", arXiv:2601.17573 [2026]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2601_17573
