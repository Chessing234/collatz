import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gogi Pantsulaia, "Under Collatz conjecture the Collatz mapping has no an asymptotic mixing property $\pmod{3}$", arXiv:1502.05602 [2015].

Title: Under Collatz conjecture the Collatz mapping has no an asymptotic mixing property $\pmod{3}$

Abstract (from OpenAlex metadata, truncated):
By using properties of Markov homogeneous chains and Banach measure in $\mathrm{N}$, it is proved that a relative frequency of even numbers in the sequence of $n$-th coordinates of all Collatz sequences is equal to the number $\frac{2}{3}+\frac{(-1)^{n+1}}{3\times 2^{n+1}}.$ It is shown also that an analogous numerical characteristic for numbers of the form $3m+1$ is equal to the number $\frac{3}{5}+ \frac{(-1)^{n+1}}{15 \times 2^{2(n-1)}}. $ By using these formulas it is proved that under Collatz conjecture the Collatz mapping has no an asymptotic mixing property $\pmod{3}$. It is constructed also an example of a real-valued function on the cartesian product $N^2$ of the set of all natural numbers $N$ such that an equality its repeated integrals (with respect to Banach measure in $N$) implies that Collatz conjecture fails. In addition, it is demonstrated that Collatz conjecture fails fo

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1502.05602
-/

namespace Collatz.Papers.Arxiv1502_05602

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gogi Pantsulaia, \"Under Collatz conjecture the Collatz mapping has no an asymptotic mixing property $\\pmod{3}$\", arXiv:1502.05602 [2015]."

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

end Collatz.Papers.Arxiv1502_05602
