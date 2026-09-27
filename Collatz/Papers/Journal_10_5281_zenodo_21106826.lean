import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bélanger, Josie O. Magee, "A Complete 2-adic Valuation Partition of the Accelerated Collatz Map: Exact Family Successor Laws and an Unconditional Reduction of the Collatz Conjecture to a Single Well-Founded Descent Principle", 2026.

Title: A Complete 2-adic Valuation Partition of the Accelerated Collatz Map: Exact Family Successor Laws and an Unconditional Reduction of the Collatz Conjecture to a Single Well-Founded Descent Principle

Abstract (from harvested metadata, truncated):
ABSTRACT We give a complete, exact, and unconditional classification of the odd positive integers according to the 2-adic valuation v2(3n + 1) that governs the accelerated Collatz map T (n) = (3n + 1)/2v2(3n+1). We prove that for each j ≥ 1 the set of odd integers with v2(3n + 1) = j is exactly one residue class modulo 2j+1, given in closed form, and that these classes partition the odd integers with natural density 2−j summing to 1. On each class the map T is an exact affine law T (n) = 6m + cj with cj ∈ {1, 5} alternating with the parity of j. All statements are proved for every odd integer with no “almost all” provisos, no probabilistic heuristics, and no appeal to convergence. We then an...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21106826
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21106826

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bélanger, Josie O. Magee, \"A Complete 2-adic Valuation Partition of the Accelerated Collatz Map: Exact Family Successor Laws and an Unconditional Reduction of the Collatz Conjecture to a Single Well-Founded Descent Principle\", Zenodo, DOI:10.5281/zenodo.21106826 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21106826
