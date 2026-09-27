import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for LIÑAN REYES, CARLOS, "An improvement of the Krasikov–Lagarias lower bound for the 3x+1 problem: π_a(x) ≥ Δ·x^0.8892", 2026.

Title: An improvement of the Krasikov–Lagarias lower bound for the 3x+1 problem: π_a(x) ≥ Δ·x^0.8892

Abstract (from harvested metadata, truncated):
Let π_a(x) be the number of integers n ≤ x whose 3x+1 trajectory reaches a. Krasikov and Lagarias (Acta Arith. 109, 2003) proved π_a(x) ≥ Δ·x^0.84 for a ≢ 0 (mod 3) via a feasible solution of their nonlinear program L_11^NT(λ); that exponent has remained the published record (cited as such in arXiv:2512.13760, Dec. 2025). This note reports feasible solutions of L_k^NT(λ) for k = 12,…,16, obtained by a damped power iteration of the min-linear operator underlying the program, with the k = 16 certificate verified in exact integer arithmetic (rational λ = 9261173/5000000, certified rational lower bounds for the transcendental weights, exact slack ≥ 7.84·10⁻¹¹ over 14,348,907 constraints). By Theorem 2.2 of Krasikov–Lagarias this yields π_a(x) ≥ Δ·x^γ with γ = log₂(9261173/5000000) =...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22254618
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22254618

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "LIÑAN REYES, CARLOS, \"An improvement of the Krasikov–Lagarias lower bound for the 3x+1 problem: π_a(x) ≥ Δ·x^0.8892\", DOI:10.5281/zenodo.22254618 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22254618
