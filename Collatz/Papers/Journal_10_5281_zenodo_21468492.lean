import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for KyungUP Moon, "The Dual Automaton Structure of Collatz Realizability: From the Δk Automaton to the Integer Realization Automaton", 2026.

Title: The Dual Automaton Structure of Collatz Realizability: From the Δk Automaton to the Integer Realization Automaton

Abstract (from harvested metadata, truncated):
This paper gives an accelerated-valuation formulation of a classical correction/residue correspondence in 3x+1 dynamics, organized as a dictionary between a forward dynamical automaton (the Δk Automaton) and a backward residue construction (the Integer Realization Automaton, IRA). Both automata are shown to share one arithmetic correction quantity Bk, giving a Common Correction Core linking forward orbit correction and backward finite-prefix compatibility residues. The finite-prefix congruence at the heart of this correspondence is the accelerated-coordinate counterpart of the classical parity-vector theorem of Terras (1976), surveyed by Lagarias (1985); the forward/backward reconstruction i...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21468492
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21468492

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "KyungUP Moon, \"The Dual Automaton Structure of Collatz Realizability: From the Δk Automaton to the Integer Realization Automaton\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21468492 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21468492
