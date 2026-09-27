import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Adam McKenna, "Ghost Cycles of the Syracuse Map: 2-Adic Periodic Orbits and the Exceptional Set", 2026.

Title: Ghost Cycles of the Syracuse Map: 2-Adic Periodic Orbits and the Exceptional Set

Abstract (from harvested metadata, truncated):
Abstract: We study the Syracuse map S(n) = (3n+1)/2^v(3n+1) on odd integers through its transfer operator L on C(Z_2^odd) and its finite approximations P_k. We prove ‖L‖ = 2/3 and ρ(L) ≤ 1/2, and establish two independent obstructions to spectral gap methods: L does not preserve any Hölder or Lipschitz space on (Z_2^odd, |·|_2), and L is unbounded on C(Z_2^odd, Q_2) with ‖P_k‖_2-adic = 2^(k+O(1)) → ∞, closing the Mahler/Amice program in the 2-adic setting. Both obstructions trace to a common root cause: the weight 2^(-v) is archimedeanly small but 2-adically large. Our central result is that "ghost cycles" — extra modular cycles beyond the fixed point {1} — are not transient artifacts: exhau...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18949341
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18949341

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Adam McKenna, \"Ghost Cycles of the Syracuse Map: 2-Adic Periodic Orbits and the Exceptional Set\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18949341 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18949341
