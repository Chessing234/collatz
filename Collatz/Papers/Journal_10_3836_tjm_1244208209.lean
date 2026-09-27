import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tomoaki MIMURO, "On Generalized Circuit of the Collatz Conjecture", 2005.

Title: On Generalized Circuit of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture is that there exists a positive integer $n$ which satisfies $f^n(m)=1$ for any integer $m \geq 3$, where $f$ is the function on the rational number field defined by $f(m)=m/2$ if the numerator of $m$ is even and $f(m)=(3m+1)/2$ if the numerator of $m$ is odd. Let $m$ be a rational number such that $f^n(m)=m>1$. Then we show that, if $m$ has some simple sequences, then the total number of positive integer $m$ is finite, by estimating $f(m)-m$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3836/tjm/1244208209
-/

namespace Collatz.Papers.Journal_10_3836_tjm_1244208209

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tomoaki MIMURO, \"On Generalized Circuit of the Collatz Conjecture\", Tokyo Journal of Mathematics, DOI:10.3836/tjm/1244208209 [2005]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_3836_tjm_1244208209
