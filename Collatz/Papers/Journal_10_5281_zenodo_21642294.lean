import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for yan huang, "On the Necessity of Higher-Order 2-adic Valuations:\\ A Structural Analysis of Collatz Map Iterations", 2026.

Title: On the Necessity of Higher-Order 2-adic Valuations:\\ A Structural Analysis of Collatz Map Iterations

Abstract (from harvested metadata, truncated):
This manuscript analyzes the variation of 2-adic valuations during Collatz map iterations. The iterative behavior is decomposed through operator separation, and congruence methods are used to prove rigorously that any finite initial odd integer cannot indefinitely sustain iterations with $\nu_2(3x+1)=1$; a 2-adic valuation with $k \ge 2$ must appear within finitely many steps. The generation of even numbers during iteration and the numerical changes under higher valuations are examined. The convergence path following the occurrence of a pure power of two is described. The manuscript distinguishes between rigorous proofs and structural inferences. Based on the established uniqueness of the $\...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21642294
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21642294

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "yan huang, \"On the Necessity of Higher-Order 2-adic Valuations:\\\\ A Structural Analysis of Collatz Map Iterations\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21642294 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21642294
