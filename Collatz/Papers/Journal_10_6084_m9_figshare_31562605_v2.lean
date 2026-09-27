import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Harris, Juan, "OCM: Fixed-Modulus Block Drift and Finite Bad Sets in the Odd Collatz Map", 2026.

Title: OCM: Fixed-Modulus Block Drift and Finite Bad Sets in the Odd Collatz Map

Abstract (from harvested metadata, truncated):
This research presents a formal structural analysis of the Odd Collatz Map (OCM) using fixed-modulus block drift and 2-adic lifting. The study provides exact modular classifications of "bad sets" (non-contractive residue classes) for block lengths of 2, 3, and 4 steps (modulo 16, 32, and 128). Key Findings: Acyclicity at Modulo 2048: Computational verification proves that the 4-step bad subgraph is a Directed Acyclic Graph (DAG) with a maximum depth of 19 blocks. Structural Obstruction: The work identifies the "Deep State" (1365 mod 2048) and formalizes "Fat Edges" in finite-state automata. 2-Adic Lifting: The results isolate the remaining challenge of the conjecture: controlling compatible...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.31562605.v2
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_31562605_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Harris, Juan, \"OCM: Fixed-Modulus Block Drift and Finite Bad Sets in the Odd Collatz Map\", figshare, DOI:10.6084/m9.figshare.31562605.v2 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_6084_m9_figshare_31562605_v2
