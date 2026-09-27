import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Farzali Izadi, "Complete Proof of the Collatz Conjecture", arXiv:2101.06107 [2021].

Title: Complete Proof of the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The \textit{Collatz's conjecture} is an unsolved problem in mathematics. It is named after Lothar Collatz in 1973. The conjecture also known as Syrucuse conjecture or problem. Take any positive integer $ n $. If $ n $ is even then divide it by $ 2 $, else do "triple plus one" and get $ 3n+1 $. The conjecture is that for all numbers, this process converges to one. In the modular arithmetic notation, define a function $ f $ as follows: \[f(x)= \left\{ \begin{array}{lll} \frac{n}{2} &if & n\equiv 0 \pmod 2\\ 3n+1& if& n\equiv 1 \pmod 2. \end{array}\right. \] In this paper, we present the proof of the Collatz conjecture for many types of sets defined by the remainder theorem of arithmetic. These sets are defined in mods $6, 12, 24, 36, 48, 60, 72, 84, 96, 108$ and we took only odd positive remainders to work with. It is not difficult to prove that the same results are true for any mod $12m, $ for positive integers $m$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2101.06107
-/

namespace Collatz.Papers.Arxiv2101_06107

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Farzali Izadi, \"Complete Proof of the Collatz Conjecture\", arXiv:2101.06107 [2021]."

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

end Collatz.Papers.Arxiv2101_06107
