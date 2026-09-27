import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nobuki Fujimoto, "Beta-Shift Discriminators for the Collatz Conjecture: Real-Valued Formalization in Lean 4 / Mathlib and the Telescoping Identity", 2026.

Title: Beta-Shift Discriminators for the Collatz Conjecture: Real-Valued Formalization in Lean 4 / Mathlib and the Telescoping Identity

Abstract (from harvested metadata, truncated):
Two structural discriminators D1 (mean log-ratio) and D2 (lag-1 autocorrelation) on Syracuse orbits, derived from the beta = 3/2 shift framework. Integer-decidable version: 11 zero-sorry Lean 4 theorems (native_decide, FUNNEL sampled 8 cores vs n=247 bypass). Real-valued version: 9 zero-sorry Mathlib theorems using Real.log on noncomputable definitions. Key telescoping identity: D1(n) < 0 is equivalent to orbit(n) reaches 1 (the Collatz termination claim). Places Rei STEP 787 empirical 5.7 sigma separation inside the standard Collatz equivalence class. Companion to Paper 66 (95 percent closure) and Paper 69 (Schnorr-D-FUMT8).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19593044
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19593044

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nobuki Fujimoto, \"Beta-Shift Discriminators for the Collatz Conjecture: Real-Valued Formalization in Lean 4 / Mathlib and the Telescoping Identity\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19593044 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_19593044
