import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Budee U Zaman, "Validating Collatz Conjecture through Binary Representation and Probabilistic Path Analysis", arXiv:2402.00673 [2024].

Title: Validating Collatz Conjecture through Binary Representation and Probabilistic Path Analysis

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture, a longstanding mathematical puzzle, posits that, regardless of the starting integer, iteratively applying a specific formula will eventually lead to the value 1. This paper introduces a novel approach to validate the Collatz conjecture by leveraging the binary representation of generated numbers. Each transition in the sequence is predetermined using the Collatz conjecture formula, yet the path of transitions is revealed to be intricate, involving alternating increases and decreases for each initial value. The study delves into the global flow of the sequence, investigating the behavior of the generated numbers as they progress toward the termination value of 1. The analysis utilizes the concept of probability to shed light on the complex dynamics of the Collatz conjecture. By incorporating probabilistic methods, this research aims to unravel the underlying patter

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2402.00673
-/

namespace Collatz.Papers.Arxiv2402_00673

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Budee U Zaman, \"Validating Collatz Conjecture through Binary Representation and Probabilistic Path Analysis\", arXiv:2402.00673 [2024]."

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

end Collatz.Papers.Arxiv2402_00673
