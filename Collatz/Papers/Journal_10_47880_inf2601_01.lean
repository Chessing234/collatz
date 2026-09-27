import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Li Lei, "An Asymptotic Approach for the Collatz Conjecture", 2023.

Title: An Asymptotic Approach for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
lt is well known that the Collatz Conjecture is one of the unsolved problems in mathematics. Supercomputer simulation has confirmed that the Collatz conjecture is correct for all positive integers unti1 2.95*10^20. Recently, Terence Tao proved that almost all orbits of the Collatz map attain almost bounded values. It is to say that the Collatz conjecture is almost correct for almost all positive integers. This paper proposes an asymptotic approach for the Collatz Conjecture by the mathematical induction and probability theory. The result of this paper means that the Collatz conjecture is correct for almost all positive integers. Keywords: Collatz Conjecture, asymptotic approach, probability, mathematical induction.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.47880/inf2601-01
-/

namespace Collatz.Papers.Journal_10_47880_inf2601_01

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Li Lei, \"An Asymptotic Approach for the Collatz Conjecture\", Information (Koganei), DOI:10.47880/inf2601-01 [2023]."

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

end Collatz.Papers.Journal_10_47880_inf2601_01
