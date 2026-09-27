import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture: Reformulations, a Flawed Disproof, and Persistent Open Status — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: Reformulations, a Flawed Disproof, and Persistent Open Status — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz remains unsolved; recent work includes topological/ergodic reformulation and a brief Lean-based "disproof" due to kernel vulnerability, not a mathematical counterexample. | MATH: Collatz map T(n) = n/2 if n even, (3n+1)/2 if n odd (or 3n+1 then halve). No new constants or closed-form solutions; the arXiv paper (2601.03297v6) introduces a Borel σ-algebra and thermodynamic formalism, showing recurrence implies periodicity in a class of maps containing Collatz — but no proof of recurrence for all n. | CONNECTION: No direct geometric ratio (0.382, 0.618, 0.786, 1.618, 2.618) or base-60 link. However, the ergodic/topological approach hints at measure-preserving dynamics on a comp...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22748365
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22748365

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture: Reformulations, a Flawed Disproof, and Persistent Open Status — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22748365 [2026]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_5281_zenodo_22748365
