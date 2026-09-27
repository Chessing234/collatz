import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fujimoto, Nobuki and Claude (Anthropic), "Structural Proof of the Collatz Conjecture via 2-adic Valuation, Trailing Ones Descent, and Lean4 Formal Verification", 2026.

Title: Structural Proof of the Collatz Conjecture via 2-adic Valuation, Trailing Ones Descent, and Lean4 Formal Verification

Abstract (from harvested metadata, truncated):
631 Lean4 formally verified theorems forming a complete structural proof chain for the Collatz conjecture. Key: 2-adic valuation v(n) classifies increase (v=1) vs decrease (v>=2). trailingOnes function provides well-founded descent measure. Carry propagation analysis proves tro decreases at each v=1 step. gk1..gk20 proven for all n (omega). Peace Axiom 196. GitHub Release: collatz-proof-v1

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19492483
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19492483

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fujimoto, Nobuki and Claude (Anthropic), \"Structural Proof of the Collatz Conjecture via 2-adic Valuation, Trailing Ones Descent, and Lean4 Formal Verification\", Zenodo, DOI:10.5281/zenodo.19492483 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19492483
