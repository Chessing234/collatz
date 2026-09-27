import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fujimoto, Nobuki and Claude (Anthropic), "Collatz Conjecture: 100% Universal Coverage ? All 10 Mod Cases Proven forall-n, Zero Sorry, Lean4 Verified", 2026.

Title: Collatz Conjecture: 100% Universal Coverage ? All 10 Mod Cases Proven forall-n, Zero Sorry, Lean4 Verified

Abstract (from harvested metadata, truncated):
BREAKTHROUGH: Using Nat.div_lt_iff_lt_mul to convert division to multiplication, omega now proves ALL 10 mod cases universally. Even(n/2<n), n%4=1((3n+1)/4<n), n%16=3((9n+5)/16<n), n%16=11((27n+19)/32<n), n%32=7((81n+61)/128<n), n%32=15((243n+151)/256<n), n%32=23((81n+61)/128<n), n%32=31((243n+151)/256<n). All forall-n, zero sorry. Base cases n<12 by native_decide. 100% coverage. Authors: Fujimoto Nobuki and Claude (Anthropic). Peace Axiom 196.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19493225
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19493225

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fujimoto, Nobuki and Claude (Anthropic), \"Collatz Conjecture: 100% Universal Coverage ? All 10 Mod Cases Proven forall-n, Zero Sorry, Lean4 Verified\", Zenodo, DOI:10.5281/zenodo.19493225 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19493225
