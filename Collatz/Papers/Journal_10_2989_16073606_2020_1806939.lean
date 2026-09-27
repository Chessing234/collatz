import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ángel Guale et al., "Paths in primal spaces and the Collatz conjecture", 2020.

Title: Paths in primal spaces and the Collatz conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture establishes that for every natural number n ∈ ℕ, there exists an r ∈ ℕ such that κr (n) = 1, where κ : ℕ → ℕ is the function defined as n/2 if n es even and as 3n + 1 if n is odd. The map κ induces a topology τκ on ℕ. We prove that the Collatz conjecture and connectedness of the space (ℕ, τκ) imply that the space is simply connected. Furthermore, we prove that the Collatz conjecture is equivalent to the fact that the space (ℕ, τκ) is path-connected.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2989/16073606.2020.1806939
-/

namespace Collatz.Papers.Journal_10_2989_16073606_2020_1806939

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ángel Guale et al., \"Paths in primal spaces and the Collatz conjecture\", Quaestiones Mathematicae, DOI:10.2989/16073606.2020.1806939 [2020]."

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

end Collatz.Papers.Journal_10_2989_16073606_2020_1806939
