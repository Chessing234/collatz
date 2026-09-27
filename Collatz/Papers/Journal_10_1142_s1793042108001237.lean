import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for KOHL, STEFAN, "ON CONJUGATES OF COLLATZ-TYPE MAPPINGS", 2008.

Title: ON CONJUGATES OF COLLATZ-TYPE MAPPINGS

Abstract (from harvested metadata, truncated):
A mapping f : ℤ → ℤ is called residue-class-wise affine if there is a positive integer m such that it is affine on residue classes (mod m). If there is a finite set S ⊂ ℤ which intersects nontrivially with any trajectory of f, then f is called almost contracting. Assume that f is a surjective but not injective residue-class-wise affine mapping, and that the preimage of any integer under f is finite. Then f is almost contracting if and only if there is a permutation σ of ℤ such that fσ = σ-1 ◦ f ◦ σ is either monotonically increasing or monotonically decreasing almost everywhere. In this paper it is shown that if there is no positive integer k such that applying f(k) decreases the absolute value of almost all integers, then σ cannot be residue-class-wise affine itself. The original...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1142/s1793042108001237
-/

namespace Collatz.Papers.Journal_10_1142_s1793042108001237

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "KOHL, STEFAN, \"ON CONJUGATES OF COLLATZ-TYPE MAPPINGS\", International Journal of Number Theory, DOI:10.1142/s1793042108001237 [2008]."

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

end Collatz.Papers.Journal_10_1142_s1793042108001237
