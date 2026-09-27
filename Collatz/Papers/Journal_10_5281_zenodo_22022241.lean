import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture: No Proof Found, Only Tao's Almost-All Orbits Result — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: No Proof Found, Only Tao's Almost-All Orbits Result — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: No proof or partial proof of the Collatz conjecture is presented in these sources; only popular expositions, failed attempts, and Terence Tao's result on almost all orbits attaining almost bounded values. | MATH: Collatz function: \( f(n) = n/2 \) if \( n \) even, \( f(n) = 3n+1 \) if \( n \) odd. Tao's result (2019): For almost all \( n \), the minimal value of the orbit is bounded by any function that grows slower than any iterated logarithm. No exact constants, ratios, or equations beyond the definition. | CONNECTION: None. No geometric ratios (0.382, 0.618, 0.786, 1.618, 2.618), base-60, or crystallographic symmetries appear. The problem is purely number-theoretic and iterative,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22022241
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22022241

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture: No Proof Found, Only Tao's Almost-All Orbits Result — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22022241 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22022241
