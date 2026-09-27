import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Cain, Lukas, "Modular Measure Decay and Renewal-Cycle Contraction for the Collatz Conjecture: A Lean 4 Formalization", 2026.

Title: Modular Measure Decay and Renewal-Cycle Contraction for the Collatz Conjecture: A Lean 4 Formalization

Abstract (from harvested metadata, truncated):
We present a partial machine-checked formalization of the Collatz conjecturein the Lean 4 proof assistant, comprising over twenty-one thousand lines ofproof across fifteen source files. The development introduces a three-layerframework that decomposes the conjecture into modular measure decay, renewal-cyclecontraction, and a bridging argument connecting residue-class analysis toindividual trajectories. At the first layer, we prove that the fraction of"bad" residue classes -- those admitting no finite contraction witness at agiven modular resolution -- decays geometrically to zero as the resolutionincreases. At the second layer, we formalize an explicit renewal-cycle mapthat tracks each odd i...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.31396683
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_31396683

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Cain, Lukas, \"Modular Measure Decay and Renewal-Cycle Contraction for the Collatz Conjecture: A Lean 4 Formalization\", figshare, DOI:10.6084/m9.figshare.31396683 [2026]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_31396683
