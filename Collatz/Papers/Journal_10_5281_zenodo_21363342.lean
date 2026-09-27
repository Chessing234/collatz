import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for (sobeh), mahmoud, "The MSJS System: A Complete Resolution of the Collatz Conjecture via Mandatory Entry and Forced Exit Loops of the Units Digit", 2026.

Title: The MSJS System: A Complete Resolution of the Collatz Conjecture via Mandatory Entry and Forced Exit Loops of the Units Digit

Abstract (from harvested metadata, truncated):
I present a complete resolution of the Collatz conjecture through the MSJS(Modular Special Jump System). The core idea is that the Collatz map is a network of recurring loops (cycles) for the units digit. Every odd number has amandatory entry into a specific even number. Every even number has two possible exits, determined solely by the tens digit (X2): one exit when X2 is even,and another when X2 is odd (a +5 offset). All these loops eventually feed intothe final absorbing cycle 1 → 4 → 2 → 1. This behavior is rigorously provenvia exhaustive verification over the finite core (X3,X2,X1) of 1000 states, and issupported by practical examples (27, 1014, 1034)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21363342
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21363342

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "(sobeh), mahmoud, \"The MSJS System: A Complete Resolution of the Collatz Conjecture via Mandatory Entry and Forced Exit Loops of the Units Digit\", Zenodo, DOI:10.5281/zenodo.21363342 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21363342
