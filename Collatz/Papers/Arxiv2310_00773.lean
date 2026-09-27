import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "Resolving the Collatz Conjecture: A Rigorous Proof through Inverse Discrete Dynamical Systems and Algebraic Inverse Trees", arXiv:2310.00773 [2024].

Title: Resolving the Collatz Conjecture: A Rigorous Proof through Inverse Discrete Dynamical Systems and Algebraic Inverse Trees

Abstract (from OpenAlex metadata, truncated):
This article introduces the Theory of Inverse Discrete Dynamical Systems (TIDDS), a novel methodology for modeling and analyzing discrete dynamical systems via inverse algebraic models. Key concepts such as inverse modeling, structural analysis of inverse algebraic trees, and the establishment of topological equivalences for property transfer between a system and its inverse are elucidated. Central theorems on homeomorphic invariance and topological transport validate the transfer of cardinal attributes between dynamic representations, offering a fresh perspective on complex system analysis. A significant application presented is an alternative proof of the Collatz Conjecture, achieved by constructing an associated inverse model and leveraging analytical property transfers within the inverted tree structure. This work not only demonstrates the theory's capability to address and solve ope

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2310.00773
-/

namespace Collatz.Papers.Arxiv2310_00773

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"Resolving the Collatz Conjecture: A Rigorous Proof through Inverse Discrete Dynamical Systems and Algebraic Inverse Trees\", arXiv:2310.00773 [2024]."

/-- Recorded main claim shell (logic); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2310_00773
