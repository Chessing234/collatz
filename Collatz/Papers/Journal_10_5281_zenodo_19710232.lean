import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Resolution of the Collatz Conjecture via the Axiom of Bijective Causality", 2026.

Title: Resolution of the Collatz Conjecture via the Axiom of Bijective Causality

Abstract (from harvested metadata, truncated):
This paper identifies the structural flaws in the traditional definition of natural numbers based on the Peano axioms and provides a complete resolution of the Collatz conjecture by introducing a new dynamic generative definition: the \textbf{Axiom of Bijective Causality}. Traditional mathematical systems based on the Peano postulates extract numerical values statically and remain incomplete, failing to exclude ``non-standard models'' (ghost natural numbers) as demonstrated by the L\"{o}wenheim-Skolem theorem. Within this static framework, the Collatz conjecture inevitably collapses into the ``halting problem,'' restricting research to the accumulation of indirect evidence. In contrast, we t...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19710232
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19710232

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Resolution of the Collatz Conjecture via the Axiom of Bijective Causality\", Zenodo, DOI:10.5281/zenodo.19710232 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19710232
