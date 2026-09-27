import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Konstadinidis, Pavlos B., "The Real 3x+1 Problem", arXiv:math/0410481 [2004].

Title: The Real 3x+1 Problem

Abstract (from arXiv metadata, truncated):
In this work, we introduce another extension U of the 3n+1 function to the real line. We propose a conjecture about the U-trajectories that generalizes the famous 3n+1 (or Collatz) conjecture. We then prove our main result about the iterates of U (which is directly related to both of these conjectures). We also introduce the "flipped 3x+1" function \widetilde U and prove an analogous result for its trajectories. In the final section, we pose some interesting questions about the iterates of U (and \widetilde U), prove a couple of simple results about the iterates of U and \widetilde U, introduce other related functions and propose yet more conjectures and questions about their iterates. It's our hope that the results, conjectures and questions presented here will be not only relevant to the 3n+1 conjecture itself, but also of interest in their own right.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/math/0410481
-/

namespace Collatz.Papers.ArxivMath_0410481

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Konstadinidis, Pavlos B., \"The Real 3x+1 Problem\", arXiv:math/0410481 [2004]."

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

end Collatz.Papers.ArxivMath_0410481
