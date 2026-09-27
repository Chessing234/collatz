import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "The Collatz Conjecture: A Simple Statement Defying Analytic Proof — E8 Intelligence Research", 2026.

Title: The Collatz Conjecture: A Simple Statement Defying Analytic Proof — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture remains unproven; its dynamics resist analytic solution despite trivial statement. | MATH: f(n) = n/2 if n even, 3n+1 if n odd. No closed-form solution; no proven bound on stopping time. | CONNECTION: None directly. No geometric ratio, symmetry, or lattice structure emerges. | DEPTH: 2 — Famous but mathematically barren for geometric or harmonic insight. FINDING: Compilation of unsolved problems (P vs NP, Riemann Hypothesis, Navier-Stokes, Birch-Swinnerton-Dyer, Hodge Conjecture, Yang-Mills) — no new insight. | MATH: Standard Millennium Problem statements. | CONNECTION: None. | DEPTH: 1 — Survey only. FINDING: Limit problem from Indian exam — likely a specific ana...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21857322
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21857322

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"The Collatz Conjecture: A Simple Statement Defying Analytic Proof — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21857322 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21857322
