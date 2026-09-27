import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Novgorodtsev, Aleksei, "CollatzLayerA v8.1 Formal Verification of the Collatz Conjecture in Lean 4 + Mathlib (2636 lines, 215 theorems, 2 axioms, 0 sorry)", 2026.

Title: CollatzLayerA v8.1 Formal Verification of the Collatz Conjecture in Lean 4 + Mathlib (2636 lines, 215 theorems, 2 axioms, 0 sorry)

Abstract (from harvested metadata, truncated):
Formal verification of the Collatz Conjecture in Lean 4 with Mathlib. METRICS: 2636 lines · 215 theorems · 2 axioms · 0 sorry Verified: live.lean-lang.org, Latest Mathlib, March 9, 2026 All Messages (0) The proof operates through algebraic bit constraints: Fresh 3-Bit rank exhaustion, Novgorodtsev parametric identity, noise absorption in ℚ, and contraction certificates. Section §4A bridges to the stochastic mismatch drift theory (Paper1), formalizing β = log₂(4/3) as the universal navigation constant. AXIOMS (2 total, both structurally justified): (1) base_case_109 - computational verification for n < 2^109 (Barina 2020) (2) odd_steps_certificate - Sprint Lock + Markov chain certificate, jus...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18928635
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18928635

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Novgorodtsev, Aleksei, \"CollatzLayerA v8.1 Formal Verification of the Collatz Conjecture in Lean 4 + Mathlib (2636 lines, 215 theorems, 2 axioms, 0 sorry)\", Zenodo, DOI:10.5281/zenodo.18928635 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18928635
