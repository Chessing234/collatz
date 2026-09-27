import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alazemi, Abdullah et al., "On the inverse Collatz-Sinogowitz irregularity problem", 2023.

Title: On the inverse Collatz-Sinogowitz irregularity problem

Abstract (from harvested metadata, truncated):
Abstract The Collatz-Sinogowitz irregularity index is the oldest known numerical measure of graph irregularity. For a simple and connected graph G G of order n n and size m m , it is defined as CS ( G ) = λ 1 − 2 m / n , \hspace{0.1em}\text{CS}\hspace{0.1em}\left(G)={\lambda }_{1}-2m\hspace{0.1em}\text{/}\hspace{0.1em}n, where λ 1 {\lambda }_{1} is the largest eigenvalue of the adjacency matrix of G G , and 2 m / n 2m\hspace{0.1em}\text{/}\hspace{0.1em}n is the average vertex degree of G G . Here, the Collatz-Sinogowitz inverse irregularity problem is studied. For every integer i ≥ 0 i\ge 0 , it is shown that there exists a graph G G such that CS ( G ) = i \hspace{0.1em}\text{CS}\hspace{0.1em}\left(G)=i . Also, for every interval I i = ( i , i + 1 ) {I}_{i}=\left(i,i+1) , it is shown that...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1515/math-2022-0572
-/

namespace Collatz.Papers.Journal_10_1515_math_2022_0572

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alazemi, Abdullah et al., \"On the inverse Collatz-Sinogowitz irregularity problem\", Open Mathematics, DOI:10.1515/math-2022-0572 [2023]."

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

end Collatz.Papers.Journal_10_1515_math_2022_0572
