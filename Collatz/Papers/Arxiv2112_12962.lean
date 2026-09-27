import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Daohang Sha, "Minimum Steps to reach to a Smaller Number in 3n+1/Collatz Process", arXiv:2112.12962 [2021].

Title: Minimum Steps to reach to a Smaller Number in 3n+1/Collatz Process

Abstract (from OpenAlex metadata, truncated):
We analyze the stopping-time and cycle structure of the normalized Collatz iteration. Using a recursive description of admissible binary sequences, we show that every integer $m \equiv 3 \pmod{4}$ arises uniquely and derive new bounds for the associated stopping and cycle numbers. These bounds imply that $F_{q}(m)/m \to 1$ as the sequence length increases, while equality is impossible for any finite sequence. Consequently, no finite nontrivial cycle is compatible with the iteration, and the trivial cycle at $1$ is the only admissible periodic orbit.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2112.12962
-/

namespace Collatz.Papers.Arxiv2112_12962

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Daohang Sha, \"Minimum Steps to reach to a Smaller Number in 3n+1/Collatz Process\", arXiv:2112.12962 [2021]."

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


end Collatz.Papers.Arxiv2112_12962
