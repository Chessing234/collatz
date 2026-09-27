import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kawasaki, Toshiharu, "Fixed point theorem in metric spaces and its application to the Collatz conjecture", arXiv:2502.20642 [2025].

Title: Fixed point theorem in metric spaces and its application to the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
In this paper, we show the new fixed point theorem in metric spaces. Furthermore, for this fixed point theorem, we apply to the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2502.20642
-/

namespace Collatz.Papers.Arxiv2502_20642

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kawasaki, Toshiharu, \"Fixed point theorem in metric spaces and its application to the Collatz conjecture\", arXiv:2502.20642 [2025]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2502_20642
