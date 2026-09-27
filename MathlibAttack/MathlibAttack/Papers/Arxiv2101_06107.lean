import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Farzali Izadi, "Complete Proof of the Collatz Conjecture", arXiv:2101.06107 [2021].

Title: Complete Proof of the Collatz Conjecture

Abstract (truncated):
The \textit{Collatz's conjecture} is an unsolved problem in mathematics. It is named after Lothar Collatz in 1973. The conjecture also known as Syrucuse conjecture or problem. Take any positive integer $ n $. If $ n $ is even then divide it by $ 2 $, else do "triple plus one" and get $ 3n+1 $. The conjecture is that for all numbers, this process converges to one. In the modular arithmetic notation, define a function $ f $ as follows: \[f(x)= \left\{ \begin{array}{lll} \frac{n}{2} &if & n\equiv 0 \pmod 2\\ 3n+1& if& n\equiv 1 \pmod 2. \end{array}\right. \] In this paper, we present the proof of the Collatz conjecture for many types of sets defined by the remainder theorem of arithmetic. These sets are defined in mods $6, 12, 24, 36, 48, 60, 72, 84, 96, 108$ and we took only odd positive remainders to work with. It is not difficult to prove that the same results are true for any mod $12m, 

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2101.06107
-/

namespace MathlibAttack.Papers.Arxiv2101_06107

open MathlibAttack.Papers

def citation : String := "Farzali Izadi, \"Complete Proof of the Collatz Conjecture\", arXiv:2101.06107 [2021]."

/-- Recorded claim shell (logic); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2101_06107
