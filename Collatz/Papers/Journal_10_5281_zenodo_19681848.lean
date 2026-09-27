import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Generalization of the Collatz Conjecture via Dynamic Primorial Multipliers and Divisors", 2026.

Title: Generalization of the Collatz Conjecture via Dynamic Primorial Multipliers and Divisors

Abstract (from harvested metadata, truncated):
We propose a generalization of the Collatz conjecture based on the fundamental properties of prime numbers. While the original $3x+1$ problem restrictedly employs the prime $2$ as a divisor and $3$ as a multiplier, this paper introduces a recursive mapping system. We define a map where an integer is divided by the set of the first $n$ primes and multiplied by the $(n+1)$-th prime. We conjecture that for any $n$, the sequence always converges to a trivial cycle containing 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19681848
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19681848

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Generalization of the Collatz Conjecture via Dynamic Primorial Multipliers and Divisors\", DOI:10.5281/zenodo.19681848 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_19681848
