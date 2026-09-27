import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Edward G. Belaga and Maurice Mignotte, "The Collatz Problem and Its Generalizations: Experimental Data. Table 2. Factorization of Collatz Numbers 2l − 3k", 2007.

Title: The Collatz Problem and Its Generalizations: Experimental Data. Table 2. Factorization of Collatz Numbers 2l − 3k

Abstract (from harvested metadata, truncated):
The purpose of the present paper is to provide the reader with the table of the factorization in primes of all Collatz numbers $2^\ell-3^k>0$,in the interval $1 <\ell<115$. The interest of such experimental data is double. First, Collatz numbers represent a natural and, in a sense, minimal generalization of two classes of integers, Cunningham integers and Schinzel integers, with the experimental factorization of Cunningham integers representing an ongoing, well-known and well-organized project, initiated by John Brillhart, D. H. Lehmer, J. L. Selfridge, Bryant Tuckerman, and Sam S. Wagstaff. Second, Collatz numbers play the crucial role in the Diophantine interpretation of the Collatz problem : one of the most interesting rephrasing of this problem claims that no narrow Collatz number...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.13140/2.1.1141.4088
-/

namespace Collatz.Papers.Journal_10_13140_2_1_1141_4088

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Edward G. Belaga and Maurice Mignotte, \"The Collatz Problem and Its Generalizations: Experimental Data. Table 2. Factorization of Collatz Numbers 2l − 3k\", HAL (Le Centre pour la Communication Scientifique Directe), DOI:10.13140/2.1.1141.4088 [2007]."

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

end Collatz.Papers.Journal_10_13140_2_1_1141_4088
