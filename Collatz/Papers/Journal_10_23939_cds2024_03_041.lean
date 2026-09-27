import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lviv Polytechnic National University et al., "LINEAR RANDOM NUMBER GENERATOR WITH COLLATZ  TRANSFORMATION FUNCTION", 2024.

Title: LINEAR RANDOM NUMBER GENERATOR WITH COLLATZ  TRANSFORMATION FUNCTION

Abstract (from harvested metadata, truncated):
For the first time, a statistical model of a pseudo-random number generator (PRNG) with the Collatz transformation function is constructed and investigated in this paper. The PRNG is implemented in the Python statistical programming environment, and the function is obtained using the inverse transformation method. It is established that the probability integral function takes the form of a transcendental polynomial of quadratic nature, within which the range of PRNG values is justified.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.23939/cds2024.03.041
-/

namespace Collatz.Papers.Journal_10_23939_cds2024_03_041

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lviv Polytechnic National University et al., \"LINEAR RANDOM NUMBER GENERATOR WITH COLLATZ  TRANSFORMATION FUNCTION\", Computer Design Systems. Theory and Practice, DOI:10.23939/cds2024.03.041 [2024]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_23939_cds2024_03_041
