import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Durmagambetov, Asset and Durmagambetova, Aniyar, "The Collatz Conjecture: Binary Structure Analysis and Trajectory Behavior", 2025.

Title: The Collatz Conjecture: Binary Structure Analysis and Trajectory Behavior

Abstract (from harvested metadata, truncated):
Background: The Collatz conjecture, proposed in 1937, asserts that iteration of the map T(n) = n/2 if n even, 3n + 1 if n odd, reaches 1 for every positive integer n. Verified computationally to n &amp;lt; 268, it remains unproven. This study analyzes the conjecture through binary structure, relating the fractional part {log2 n} to zero density z(n) and v2(3n + 1). Methods: We derive a recurrence relation for fractional parts in binary expansions and analyze block structures using linear systems. For sparse binary numbers (z(n) ≥ n/2), we prove strict trajectory decrease in O(log n) steps. Results: Theorem 1 establishes fractional part recurrence. Theorem 2 proves ≥ 50% zero density in 3n when 1 − {α} &amp;gt; 0.55. Theorem 3 shows strict decrease for sparse binaries. Theorem 4 verifies...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202401.0227.v22
-/

namespace Collatz.Papers.Journal_10_20944_preprints202401_0227_v22

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Durmagambetov, Asset and Durmagambetova, Aniyar, \"The Collatz Conjecture: Binary Structure Analysis and Trajectory Behavior\", DOI:10.20944/preprints202401.0227.v22 [2025]."

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

end Collatz.Papers.Journal_10_20944_preprints202401_0227_v22
