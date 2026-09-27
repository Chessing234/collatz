import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Undecidability of Collatz Orbits and the Limits of Formal Computation — E8 Intelligence Research", 2026.

Title: Undecidability of Collatz Orbits and the Limits of Formal Computation — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The Collatz Conjecture (3n+1) is the canonical example of an elementary iterative map whose global behavior is undecidable in practice, while Hilbert's Entscheidungsproblem proves some problems are formally uncomputable. | MATH: Collatz map: T(n) = n/2 if n even, 3n+1 if n odd. No closed-form solution; orbits conjectured to reach 1 for all n ∈ ℕ⁺. Uncomputability: Halting problem (Turing 1936) — no algorithm decides whether an arbitrary program halts. | CONNECTION: The Collatz map is a discrete dynamical system on ℤ⁺; its orbit structure resembles a 3-adic tree (root system A₁-like branching), but no known symmetry group or ratio governs it. No 0.618, 1.618, or base-60 structure app...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22325786
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22325786

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Undecidability of Collatz Orbits and the Limits of Formal Computation — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22325786 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22325786
