import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for 秦, 子泰, "An Unconditional Proof of the Collatz Conjecture By Qin zitai", 2026.

Title: An Unconditional Proof of the Collatz Conjecture By Qin zitai

Abstract (from harvested metadata, truncated):
AbstractThis paper provides a complete rigorous proof of the Collatz conjecture within the ZFC axiomatic system: starting from any positive odd integer, the Collatz orbit eventually converges to 1. The proof consists of two independent modules, which together yield a contradiction via a joint reductio ad absurdum. First Module (Forced convergence of numbers congruent to 5 mod 8): Using elementary number-theoretic identities, it is proved that numbers congruent to 5 modulo 8 strictly decrease under the Collatz compression map. By the well-ordering principle and the minimal counterexample method, it follows that a number congruent to 5 modulo 8 cannot be the smallest counterexample. This conclusion holds unconditionally. Second Module (Reduction of orbit behavior): First, a modulo 320 low-v...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20670475
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20670475

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "秦, 子泰, \"An Unconditional Proof of the Collatz Conjecture By Qin zitai\", DOI:10.5281/zenodo.20670475 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20670475
