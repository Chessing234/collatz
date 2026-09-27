import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Régent, Xavier J., "The Collatz Conjecture for Numbskulls: A Guided Tour of Its Proof", 2026.

Title: The Collatz Conjecture for Numbskulls: A Guided Tour of Its Proof

Abstract (from harvested metadata, truncated):
This pedagogical document provides an accessible introduction to the Collatz Conjecture, also known as the Syracuse Conjecture or the 3x+1 problem, and offers a guided tour of the structural proof developed in the accompanying technical paper (The Syracuse Conjecture: a categorical resolution by transport of structure in the sense of Bourbaki). Rather than reproducing the formal proof line by line, it explains the underlying strategy through visual models, intuitive analogies, and progressively introduced mathematical concepts. This work is intended as an accessible entry point for readers interested in the Collatz problem, number theory, discrete dynamical systems, mathematical structures, and the philosophy of mathematics. Its purpose is to make the conceptual architecture visible to a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22342937
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22342937

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Régent, Xavier J., \"The Collatz Conjecture for Numbskulls: A Guided Tour of Its Proof\", DOI:10.5281/zenodo.22342937 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22342937
