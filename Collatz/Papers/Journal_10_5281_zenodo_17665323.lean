import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "A Structural Resolution to the Halting Problem: Bijective Guarantee of the Collatz Conjecture via Peano-Cantor Integration", 2025.

Title: A Structural Resolution to the Halting Problem: Bijective Guarantee of the Collatz Conjecture via Peano-Cantor Integration

Abstract (from harvested metadata, truncated):
Abstract: This paper identifies the fundamental difficulty of the long-unresolved Collatz Conjecture as stemming from an unconscious self-limitation in conventional mathematics—specifically, a structural ``lack of collaboration'' between the linear definition of natural numbers (Peano Axioms) and non-linear structural analysis (Cantor's Set Theory). We propose that, to solve a non-linear Halting Problem like the Collatz Conjecture, the proof must prioritize the structural fundamental of ``symmetry of the start and stop point ($1$)'' instead of adhering to linear methods. Specifically, we resolve the ``bijective definition deficit'' of the mapping existing between specific sub-patterns (e.g.,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17665323
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17665323

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"A Structural Resolution to the Halting Problem: Bijective Guarantee of the Collatz Conjecture via Peano-Cantor Integration\", Zenodo, DOI:10.5281/zenodo.17665323 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17665323
