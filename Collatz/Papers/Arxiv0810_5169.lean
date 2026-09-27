import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for M. Bruschi, "A generalization of the Collatz problem and conjecture", arXiv:0810.5169 [2008].

Title: A generalization of the Collatz problem and conjecture

Abstract (from OpenAlex metadata, truncated):
We introduce an infinite set of integer mappings that generalize the well-known Collatz-Ulam mapping and we conjecture that an infinite subset of these mappings feature the remarkable property of the Collatz conjecture, namely that they converge to unity irrespective of which positive integer is chosen initially.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/0810.5169
-/

namespace Collatz.Papers.Arxiv0810_5169

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "M. Bruschi, \"A generalization of the Collatz problem and conjecture\", arXiv:0810.5169 [2008]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv0810_5169
