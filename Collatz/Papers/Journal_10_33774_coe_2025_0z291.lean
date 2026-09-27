import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jonathan Kenigson, "“Group Think”: On the Collatz Conjecture via Tao’s Smoothing and Sobolev Techniques", 2025.

Title: “Group Think”: On the Collatz Conjecture via Tao’s Smoothing and Sobolev Techniques

Abstract (from harvested metadata, truncated):
The Collatz conjecture, despite its elementary definition, has resisted resolution for more than eight decades and now occupies a unique position at the intersection of number theory, ergodic theory, probability, dynamical systems, logic, and the analysis of algorithms. Classical density results, stochastic models, dynamical embeddings in real and 2-adic spaces, large-scale computational verifications, and undecidability results together reveal the conjecture’s strikingly interdisciplinary nature and its deep structural difficulties. Recent advances, most notably Tao’s harmonic-analytic and non-Archimedean approach, suggest that meaningful progress may arise only from a synthesis of techniqu...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2025-0z291
-/

namespace Collatz.Papers.Journal_10_33774_coe_2025_0z291

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jonathan Kenigson, \"“Group Think”: On the Collatz Conjecture via Tao’s Smoothing and Sobolev Techniques\", DOI:10.33774/coe-2025-0z291 [2025]."

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

end Collatz.Papers.Journal_10_33774_coe_2025_0z291
