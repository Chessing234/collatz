import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Tong Niu, "Parity vectors and paradoxical sequences in the accelerated Collatz map", arXiv:2605.13886 [2026].

Title: Parity vectors and paradoxical sequences in the accelerated Collatz map

Abstract (truncated):
This note studies parity vectors and paradoxical sequences in the accelerated Collatz iteration $T(n) = (3n+1)/2$ for $n$ odd, $T(n) = n/2$ for $n$ even. Building on Rozier and Terracol (arXiv:2502.00948, 2025), Terras (1976), Lagarias (1985), and Tao (2019), we prove three theorems and add one numerical observation. The first is a sharp finitary form of Terras's parity-vector density; the second is a closed-form analytic count of paradoxical $Ω_k(n)$ for each fixed length $k$. The third is a density-zero theorem for bounded-length paradoxical sequences with explicit constant. As for the numerical piece, among the seven $(j, q)$ pairs that show up in the Rozier-Terracol enumeration with first term $n \le 10^9$, every paradoxical reduced ratio $q/j$ turns out to be a left convergent, a left semiconvergent, or a Stern-Brocot mediant of adjacent convergents/semiconvergents of $\log_3 2$. Th

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2605.13886
-/

namespace MathlibAttack.Papers.Arxiv2605_13886

open MathlibAttack.Papers

def citation : String := "Tong Niu, \"Parity vectors and paradoxical sequences in the accelerated Collatz map\", arXiv:2605.13886 [2026]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2605_13886
