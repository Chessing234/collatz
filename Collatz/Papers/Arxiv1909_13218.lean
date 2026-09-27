import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Longjiang Li, "Determining monotonic step-equal sequences of any limited length in the Collatz problem", arXiv:1909.13218 [2019].

Title: Determining monotonic step-equal sequences of any limited length in the Collatz problem

Abstract (from OpenAlex metadata, truncated):
This paper proposes a formula expression for the well-known Collatz conjecture (or 3x+1 problem), which can pinpoint all the growth points in the orbits of the Collatz map for any natural numbers. The Collatz map $Col: \mathcal{N}+1 \rightarrow \mathcal{N}+1$ on the positive integers is defined as $x_{n+1}=Col(x_n)=(3 x_n +1)/2^{m_n}$ where $x_{n+1}$ is always odd and $m_n$ is the step size required to eliminate any possible even values. The Collatz orbit for any positive integer, $x_1$, is expressed by a sequence, $$ and $x_n$ is defined as a growth point if $Col(x_n)>x_n$ holds, and we show that every growth point is in a format of ``$4y+3$'' where $y$ is any natural number. Moreover, we derive that, for any given positive integer $n$, there always exists a natural number, $x_1$, that starts a monotonic increasing or decreasing Collatz sequence of length $n$ with the same step size. Fo

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1909.13218
-/

namespace Collatz.Papers.Arxiv1909_13218

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Longjiang Li, \"Determining monotonic step-equal sequences of any limited length in the Collatz problem\", arXiv:1909.13218 [2019]."

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

end Collatz.Papers.Arxiv1909_13218
