import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Emanuel Silva Catarina, "A Local Lyapunov Function for the Collatz Map on n ≡ 6 (mod 8)", 2026.

Title: A Local Lyapunov Function for the Collatz Map on n ≡ 6 (mod 8)

Abstract (from harvested metadata, truncated):
We prove an explicit formula for the number of consecutive odd steps of the Collatz map for integers n ≡ 6 (mod 8). For n = 8m + 6, the number of iterations of T(k) = (3k+1)/2 before reaching an even value is exactly ν₂(m+1), where ν₂ is the 2-adic valuation. This yields a local Lyapunov function Φ(n) = log₂(n) + ν₂(m+1) that strictly decreases under the Collatz iteration on this class. This result arose from a discussion on Math StackExchange (Question 5135076). It is a special case of general coefficient stopping time analysis, but we could not locate this explicit form for 6 (mod 8) in the literature. MSC Class: 11B83 (Special sequences and sets), 37A44 (Ergodic theory of group actions)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19922038
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19922038

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Emanuel Silva Catarina, \"A Local Lyapunov Function for the Collatz Map on n ≡ 6 (mod 8)\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19922038 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19922038
