import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vincent Béhani, "Linear dynamics of an operator associated to the Collatz map", arXiv:2303.03203 [2023].

Title: Linear dynamics of an operator associated to the Collatz map

Abstract (from OpenAlex metadata, truncated):
In this paper, we study the dynamics of an operator $\mathcal T$ naturally associated to the so-called Collatz map, which maps an integer $n \geq 0$ to $n / 2$ if $n$ is even and $3n + 1$ if $n$ is odd. This operator $\mathcal T$ is defined on certain weighted Bergman spaces $\mathcal B ^ 2 _ ω$ of analytic functions on the unit disk. Building on previous work of Neklyudov, we show that $\mathcal T$ is hypercyclic on $\mathcal B ^ 2 _ ω$, independently of whether the Collatz Conjecture holds true or not. Under some assumptions on the weight $ω$, we show that $\mathcal T$ is actually ergodic with respect to a Gaussian measure with full support, and thus frequently hypercyclic and chaotic.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2303.03203
-/

namespace Collatz.Papers.Arxiv2303_03203

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vincent B\u00e9hani, \"Linear dynamics of an operator associated to the Collatz map\", arXiv:2303.03203 [2023]."

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

end Collatz.Papers.Arxiv2303_03203
