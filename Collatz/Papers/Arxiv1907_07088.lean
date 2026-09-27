import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zenon B. Batang, "Integer patterns in Collatz sequences", arXiv:1907.07088 [2019].

Title: Integer patterns in Collatz sequences

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture asserts that repeatedly iterating $f(x) = (3x + 1)/2^{a(x)}$, where $a(x)$ is the highest exponent for which $2^{a(x)}$ exactly divides $3x+1$, always lead to $1$ for any odd positive integer $x$. Here, we present an arborescence graph constructed from iterations of $g(x) = (2^{e(x)}x - 1)/3$, which is the inverse of $f(x)$ and where $x \not \equiv [0]_3$ and $e(x)$ is any positive integer satisfying $2^{e(x)}x - 1 \equiv [0]_3$, with $[0]_3$ denoting $0\pmod{3}$. The integer patterns inferred from the resulting arborescence provide new insights into proving the validity of the conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1907.07088
-/

namespace Collatz.Papers.Arxiv1907_07088

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Zenon B. Batang, \"Integer patterns in Collatz sequences\", arXiv:1907.07088 [2019]."

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

end Collatz.Papers.Arxiv1907_07088
