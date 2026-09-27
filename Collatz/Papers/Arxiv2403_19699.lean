import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eric Sakk, "Symbolic Dynamic Formulation for the Collatz Conjecture: I. Local and Quasi-global Behavior", arXiv:2403.19699 [2024].

Title: Symbolic Dynamic Formulation for the Collatz Conjecture: I. Local and Quasi-global Behavior

Abstract (from OpenAlex metadata, truncated):
In this work, a symbolic dynamical formulation based upon discrete iterative mappings derived from the Collatz conjecture is introduced. It is demonstrated that this formulation naturally induces a ternary alphabet useful for characterizing the expansive and dissipative behavior of generated itineraries. Furthermore, local and quasi-global analyses indicate cyclic behaviors that should prove useful for describing global stability properties of itineraries. Additionally, techniques for generating arbitrarily long divergent itineraries are presented. Finally, this symbolic formulation allows itineraries to be grouped into sequence families that retain equivalent dynamical behavior.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2403.19699
-/

namespace Collatz.Papers.Arxiv2403_19699

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eric Sakk, \"Symbolic Dynamic Formulation for the Collatz Conjecture: I. Local and Quasi-global Behavior\", arXiv:2403.19699 [2024]."

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

end Collatz.Papers.Arxiv2403_19699
