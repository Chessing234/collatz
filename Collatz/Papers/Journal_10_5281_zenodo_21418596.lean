import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Osman Alagöz, "Final-Block Reverse-Residue Audits for the Collatz Problem: Computational Supplement", 2026.

Title: Final-Block Reverse-Residue Audits for the Collatz Problem: Computational Supplement

Abstract (from harvested metadata, truncated):
Computational supplement for the manuscript “A Final-Block Reverse-Residue Reduction and Computational Audits for the Collatz Problem”. The archive contains deterministic Python scripts, frozen JSON and text outputs, SHA-256 hashes, exact reproduction commands, and a standalone consistency verifier. It supports finite audits of first-crossing and reverse-residue obstructions in the accelerated Collatz map, includingthe detailed 27/17 gate, threshold gates with H <= 17, and endpoint-valuation diagnostics through the audited upper rows with H+ <= 58. The archive and companion manuscript explicitly do not claim a proof of the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21418596
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21418596

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Osman Alagöz, \"Final-Block Reverse-Residue Audits for the Collatz Problem: Computational Supplement\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21418596 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21418596
