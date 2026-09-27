import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Liedtke, Dieter, "With the discovery of their level error by GIT, the Riemann and Collatz conjectures  are confirmed in their own structure", 2025.

Title: With the discovery of their level error by GIT, the Riemann and Collatz conjectures  are confirmed in their own structure

Abstract (from harvested metadata, truncated):
The Collatz conjecture and the Riemann hypothesis are among the best-known unsolved problems in mathematics. They have occupied researchers for decades, tying up immense computing resources and serving as touchstones for the mathematical understanding of finiteness and infinity. This work shows that both problems are based on a common level error: the mixing of the finite processes of space-time with the infinite potential of dimension 0. With the help of Holistic Information Theory (HIT), a clear separation of these levels is made. As a result, the Collatz and Riemann conjectures appear not as unsolvable puzzles, but as manifestations of universal laws of information. In this sense, both conjectures are confirmed by an error in their classical formulation. In addition, it is shown that...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.63368/collatz-riemann-confirmed
-/

namespace Collatz.Papers.Journal_10_63368_collatz_riemann_confirmed

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Liedtke, Dieter, \"With the discovery of their level error by GIT, the Riemann and Collatz conjectures  are confirmed in their own structure\", DOI:10.63368/collatz-riemann-confirmed [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_63368_collatz_riemann_confirmed
