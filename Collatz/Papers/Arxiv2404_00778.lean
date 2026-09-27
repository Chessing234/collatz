import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kirk O. Hahn, "Collatz Conjecture Proof and General Equation", arXiv:2404.00778 [2024].

Title: Collatz Conjecture Proof and General Equation

Abstract (from OpenAlex metadata, truncated):
A proof is given showing the Collatz Conjecture is true for all positive integers. The proof was possible once the perspective of the proof was changed from looking at the pattern of the positive integers to looking at the conjecture rules. The conjecture rule for even numbers organizes all positive integers into unique sets and the rule for odd numbers interconnects the unique sets into dendritic pathways to “1.” Infinite loops, other than the minor 4-2-1 loop after reaching “1,” and pathways to infinity are shown to be mathematically impossible. The proof predicted a general equation that shows all positive integers ultimately reach a final value of “1," and calculates the values and locations of the odd positive integers during the iterations for each tested positive integer.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2404.00778
-/

namespace Collatz.Papers.Arxiv2404_00778

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kirk O. Hahn, \"Collatz Conjecture Proof and General Equation\", arXiv:2404.00778 [2024]."

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

end Collatz.Papers.Arxiv2404_00778
