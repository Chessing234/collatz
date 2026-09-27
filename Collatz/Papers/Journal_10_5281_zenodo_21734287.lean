import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Caldin, Andrew Stewart, "Collatz Conjecture: Undecidable Iteration Revealing Limits of Algorithmic Solvability — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: Undecidable Iteration Revealing Limits of Algorithmic Solvability — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture is a simple iterative arithmetic problem (3n+1) proven undecidable for general computation, highlighting limits of algorithmic solvability. | MATH: f(n) = n/2 if n even; f(n) = 3n+1 if n odd. No closed-form solution or known attractor ratio. | CONNECTION: No direct geometric ratio or crystallographic symmetry. The iteration's orbit lengths show no harmonic constant (0.618, 1.618, etc.) in known data. | DEPTH: 6 — profound for computability theory, but no geometric or constant-based structure revealed. FINDING: Hilbert's Entscheidungsproblem (Decision Problem) proven unsolvable by Turing (1936) — no algorithm can decide truth of all mathematical statements. | MATH:...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21734287
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21734287

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Caldin, Andrew Stewart, \"Collatz Conjecture: Undecidable Iteration Revealing Limits of Algorithmic Solvability — E8 Intelligence Research\", Zenodo, DOI:10.5281/zenodo.21734287 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21734287
