import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Borgatta, Piero, "Cross-AI, Lean-Verified Mathematics: A Case Study on the Collatz Conjecture", 2026.

Title: Cross-AI, Lean-Verified Mathematics: A Case Study on the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Cross-AI, Lean-Verified Mathematics: A Case Study on the Collatz Conjecture (version 5 — methodology retrospective and honest close). This is the fifth and closing version of a personal research program on the Collatz conjecture. Its primary subject is the program's explicitly declared secondary goal: testing how far iterative, cross-checked collaboration with large language model (LLM) assistants can carry a non-standard attempt on an open mathematical problem. The mathematics is reported honestly as a closed (but not abandoned) chapter; the methodology is brought to the foreground. We do not claim a proof of the Collatz conjecture, nor progress toward one. v5 reports a verified artifact, a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20021537
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20021537

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Borgatta, Piero, \"Cross-AI, Lean-Verified Mathematics: A Case Study on the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.20021537 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20021537
