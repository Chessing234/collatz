import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tápanes, Denis Martínez, Serra, Jose E. Martínez, "Some elements of a possible demonstration of the Collatz conjecture", arXiv:1512.05438 [2015].

Title: Some elements of a possible demonstration of the Collatz conjecture

Abstract (from arXiv metadata, truncated):
In this paper we are shown the following facts: The probability of increased $ A_{k}=P(T^{k} (x_{0})>T^{k-1} (x_{0})) $, and the probability of decrease $B_{k}=P(T^{k} (x_{0})<T^{k-1} (x_{0}))$ in step $ k $ of a Collataz procedure initiated in $ x_ {0} \in \mathbb{N} $ arbitrary, they are equal for all values of $ k $. This influences on the law that generates the numbers of a Collatz sequence so that it is forced to decrease until the unit. Also is shown in the Collatz conjecture is false for every problem $an +b$ such that $a\geq 5\geq b+2$, and your probabilistic caracter can not be ignored if you want to get to the definitive solution, among other interesting arguments.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1512.05438
-/

namespace Collatz.Papers.Arxiv1512_05438

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "T\u00e1panes, Denis Mart\u00ednez and Serra, Jose E. Mart\u00ednez, \"Some elements of a possible demonstration of the Collatz conjecture\", arXiv:1512.05438 [2015]."

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

end Collatz.Papers.Arxiv1512_05438
