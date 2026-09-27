import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ramon Carbó‐Dorca, "Boolean Hypercubes, Mersenne Numbers, and the Collatz Conjecture", 2020.

Title: Boolean Hypercubes, Mersenne Numbers, and the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This study is based on the trivial transcription of the vertices of a Boolean \textit{N}-Dimensional Hypercube $\textbf{H}_{N} $ into a subset $\mathbb{S}_{N}$ of the decimal natural numbers $\mathbb{N}.$ Such straightforward mathematical manipulation permits to achieve a recursive construction of the whole set $\mathbb{N}.$ In this proposed scheme, the Mersenne numbers act as upper bounds of the iterative building of $\mathbb{S}_{N}$. The paper begins with a general description of the Collatz or $\left(3x+1\right)$ algorithm presented in the $\mathbb{S}_{N} \subset \mathbb{N}$ iterative environment. Application of a defined \textit{ad hoc} Collatz operator to the Boolean Hypercube recursive partition of $\mathbb{N}$, permits to find some hints of the behavior of natural numbers under the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33187/jmsm.776898
-/

namespace Collatz.Papers.Journal_10_33187_jmsm_776898

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ramon Carbó‐Dorca, \"Boolean Hypercubes, Mersenne Numbers, and the Collatz Conjecture\", Journal of Mathematical Sciences and Modelling, DOI:10.33187/jmsm.776898 [2020]."

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

end Collatz.Papers.Journal_10_33187_jmsm_776898
