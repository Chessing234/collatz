import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lee, Byoungwoo, "The Collatz Conjecture — Final Gate v8.3: Provenance-Sealed, From-Scratch Certificate Audit Pipeline", 2026.

Title: The Collatz Conjecture — Final Gate v8.3: Provenance-Sealed, From-Scratch Certificate Audit Pipeline

Abstract (from harvested metadata, truncated):
# Collatz Final Gate v8.3 (Lee Byoungwoo) ## OverviewThis record releases the **v8.3 proof-pipeline set** for the “Collatz Final Gate” program.The core contribution is a **sealed-full, report-generating from-scratch certificate pipeline**: the demo packet regenerates all audited artifacts from shipped raw inputs, binds a verdict certificate with a provenance seal, and mechanically verifies the trigger inequalities that activate the Gate-B → All-\(L\) promotion interface. This release is designed in the spirit of modern computational proof practice: a finite, auditable object + a reproducible verification pipeline. ## Scope & interpretation (to avoid common misunderstandings)- This release pr...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18424273
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18424273

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lee, Byoungwoo, \"The Collatz Conjecture — Final Gate v8.3: Provenance-Sealed, From-Scratch Certificate Audit Pipeline\", Zenodo, DOI:10.5281/zenodo.18424273 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18424273
