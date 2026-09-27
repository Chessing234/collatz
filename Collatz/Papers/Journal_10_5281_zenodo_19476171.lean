import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for REDERO, Julien, "A computer-assisted well-founded descent for Collatz components under dyadic leaf certificates", 2026.

Title: A computer-assisted well-founded descent for Collatz components under dyadic leaf certificates

Abstract (from harvested metadata, truncated):
We present a component-wise descent framework for the Collatzproblem based on a combination of analytic reduction and finite veri-fication organized over a dyadic hierarchy.The argument proceeds by reducing the problem to odd multiplesof 3 using an anti-9 lifting mechanism, and introducing a valuationparameter e(u) = v2(9u + 1) that governs the dynamics.For the regime e(u) ≥ 7, we construct an explicit analytic descentmap u 7 → u∗ = (u − 7)/64 which strictly decreases u while preservingconnected components of the Collatz graph.For the complementary regime e(u) ≤ 6, we introduce a recursivehierarchy of dyadic residue classes moduloMt = 9 · 214+6t,and associate to each leaf a certificate encoding a finite sequence ofaccelerated iterations together with a descent inequality.The key technical...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19476171
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19476171

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "REDERO, Julien, \"A computer-assisted well-founded descent for Collatz components under dyadic leaf certificates\", DOI:10.5281/zenodo.19476171 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19476171
