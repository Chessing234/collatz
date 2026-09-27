import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maarten J. Wensink, "Why there are no mappings to infinity under the Collatz map (and similar)", arXiv:1910.03289 [2019].

Title: Why there are no mappings to infinity under the Collatz map (and similar)

Abstract (from OpenAlex metadata, truncated):
Following up on earlier work, I suggest why there are no mappings to infinity under the Collatz conjecture, nor under other mappings of the generalization $3n+p$, where $p$ is odd.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1910.03289
-/

namespace Collatz.Papers.Arxiv1910_03289

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maarten J. Wensink, \"Why there are no mappings to infinity under the Collatz map (and similar)\", arXiv:1910.03289 [2019]."

/-- Recorded claim shell (generalization); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1910_03289
