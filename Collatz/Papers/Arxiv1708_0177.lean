import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kurmet Sultan, "Proof of the Collatz Conjecture", arXiv:1708.0177 [2026].

Title: Proof of the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
It is shown that the essence of the Collatz function lies in connecting all natural numbers based on positive odd numbers not divisible by 3. A proof of the Collatzconjecture is obtained by proving that the graph of the Collatz function is a tree with root 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1708.0177
-/

namespace Collatz.Papers.Arxiv1708_0177

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kurmet Sultan, \"Proof of the Collatz Conjecture\", arXiv:1708.0177 [2026]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1708_0177
