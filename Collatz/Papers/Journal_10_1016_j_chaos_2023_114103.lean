import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Masrat Rasool and Samir Brahim Belhaouari, "From Collatz Conjecture to chaos and hash function", 2023.

Title: From Collatz Conjecture to chaos and hash function

Abstract (from harvested metadata, truncated):
The non-linear property of Chaos is a promising approach to information security, and many accomplishments have been made by combining Chaos with several sub-security domains, including chaos-based stream ciphers, block ciphers, image encryption, and hash functions. Most Chaos-based hash functions are insecure or inefficient due to their dependence on complex, attacked multi-dimensional maps or uncertain, weak one-dimensional maps like logistic and tent. The Collatz Conjecture is a mystery that has stumped mathematicians for decades and still has not been solved. This paper aims to introduce a novel approach to addressing current security challenges by utilizing our generalized Collatz process to create a chaos-based hash function. By leveraging the unpredictable behaviour of the Collatz...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1016/j.chaos.2023.114103
-/

namespace Collatz.Papers.Journal_10_1016_j_chaos_2023_114103

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Masrat Rasool and Samir Brahim Belhaouari, \"From Collatz Conjecture to chaos and hash function\", Chaos Solitons & Fractals, DOI:10.1016/j.chaos.2023.114103 [2023]."

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

end Collatz.Papers.Journal_10_1016_j_chaos_2023_114103
