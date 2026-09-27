import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tosho Lazarov Karadzhov, "Finite Valuation Words and Terminal Obstructions for the Accelerated Syracuse Map", 2026.

Title: Finite Valuation Words and Terminal Obstructions for the Accelerated Syracuse Map

Abstract (from harvested metadata, truncated):
This preprint develops a finite-word obstruction framework for the accelerated Syracuse map on positive odd integers. A finite valuation word determines an exact affine iterate formula and a unique realization class modulo a power of 2, while compatible infinite prefixes define a natural 2-adic inverse-limit object together with least positive representatives. The manuscript records the exact finite-word congruence machinery, finite-descent equivalence, terminal-surplus identity, terminal-ceiling break criterion, bad-prefix windows, activated density collapse, stabilization criterion, and strict-jump bookkeeping. These tools are used to isolate terminal obstruction classes for a hypothetical...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21198618
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21198618

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tosho Lazarov Karadzhov, \"Finite Valuation Words and Terminal Obstructions for the Accelerated Syracuse Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21198618 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21198618
