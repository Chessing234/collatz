import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for J. Llibre and Clàudìa Valls, "A note on the $3x+1$ conjecture", arXiv:2110.12228 [2021].

Title: A note on the $3x+1$ conjecture

Abstract (from OpenAlex metadata, truncated):
Let $g$ be a map from the set of positive integers into itself defined as follows: Let $x$ be a positive integer. If $x$ is odd, then $g(x)=3x+1$, and if $x$ is even, then $g(x)=x/2$. The $3x+1$ conjecture, also called the Collatz conjecture, states: For any positive integer $x$ there exists another positive integer $m$ such that the $m$-iterate of $x$ under the map $g$ is equal to $1$, i.e. $g^m(x)=1$. We provide some information related with this conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2110.12228
-/

namespace Collatz.Papers.Arxiv2110_12228

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "J. Llibre and Cl\u00e0ud\u00eca Valls, \"A note on the $3x+1$ conjecture\", arXiv:2110.12228 [2021]."

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

end Collatz.Papers.Arxiv2110_12228
