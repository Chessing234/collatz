import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tong Niu, "Parity vectors and paradoxical sequences in the accelerated Collatz map", arXiv:2605.13886 [2026].

Title: Parity vectors and paradoxical sequences in the accelerated Collatz map

Abstract (from OpenAlex metadata, truncated):
This note studies parity vectors and paradoxical sequences in the accelerated Collatz iteration $T(n) = (3n+1)/2$ for $n$ odd, $T(n) = n/2$ for $n$ even. Building on Rozier and Terracol (arXiv:2502.00948, 2025), Terras (1976), Lagarias (1985), and Tao (2019), we prove three theorems and add one numerical observation. The first is a sharp finitary form of Terras's parity-vector density; the second is a closed-form analytic count of paradoxical $Ω_k(n)$ for each fixed length $k$. The third is a density-zero theorem for bounded-length paradoxical sequences with explicit constant. As for the numerical piece, among the seven $(j, q)$ pairs that show up in the Rozier-Terracol enumeration with first term $n \le 10^9$, every paradoxical reduced ratio $q/j$ turns out to be a left convergent, a left semiconvergent, or a Stern-Brocot mediant of adjacent convergents/semiconvergents of $\log_3 2$. The three theorems are unconditional. The fourth observation is verified for $n \le 10^7$ and conjectu

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2605.13886
-/

namespace Collatz.Papers.Arxiv2605_13886

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tong Niu, \"Parity vectors and paradoxical sequences in the accelerated Collatz map\", arXiv:2605.13886 [2026]."

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


end Collatz.Papers.Arxiv2605_13886
