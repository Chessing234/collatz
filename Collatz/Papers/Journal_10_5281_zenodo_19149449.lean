import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Han-Jun Lim, "Dynamics of the R12 Rendering Algebra: The Collatz Map of the Stage Factors — Lock Classification, the Certified Cycle Floor, the Divergence Cage, and the Exact Colour-Erasure Chain", 2026.

Title: Dynamics of the R12 Rendering Algebra: The Collatz Map of the Stage Factors — Lock Classification, the Certified Cycle Floor, the Divergence Cage, and the Exact Colour-Erasure Chain

Abstract (from harvested metadata, truncated):
Abstract The Collatz map is the free ledger dynamics of the stage-factor decomposition N = T2 wNc = 4·3: each render writes ln Nc of colour and erases a residue-exact geometric number of Landauer bits, mean ledger Tw ln2−ln Nc = ln(T2 w/Nc) = ln(4/3). Thefailuresetoftheconjectureisclassified into strata and each stratum is closed, priced, or caged. Periodic locks: every finite parity word w has the unique 2-adic periodic point ρ(w)/(2|w| − 3j(w)); bias words (j/|w| > log32) are sign-confined to the negative axis, where they are realised by the cycles −1,−5,−17; exact resonances |2h −3k| = 1 reduce to the stage Catalan pairs, forcing the trivial cycle as the unique d =1lock. Cycle floor: any...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19149449
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19149449

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Han-Jun Lim, \"Dynamics of the R12 Rendering Algebra: The Collatz Map of the Stage Factors — Lock Classification, the Certified Cycle Floor, the Divergence Cage, and the Exact Colour-Erasure Chain\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19149449 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19149449
