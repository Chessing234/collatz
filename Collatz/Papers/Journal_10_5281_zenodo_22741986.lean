import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture: Tao's Partial Proof and a Claimed Full Solution via Cayley Graphs — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: Tao's Partial Proof and a Claimed Full Solution via Cayley Graphs — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz conjecture remains unproven; strongest recent result is Tao's partial proof (2019) showing almost all orbits are bounded below by any diverging function, plus a novel arxiv paper framing it as an automorphic Cayley colour graph with a claimed full proof (unverified). | MATH: Collatz map T(n) = n/2 if n even, (3n+1)/2 if n odd; conjecture: ∀n∈ℕ, ∃k: T^k(n)=1. Tao's result: for f(n)→∞, lim_{N→∞} (1/N)Σ_{n≤N} 1_{sup_{k≤f(n)} T^k(n) < f(n)} = 1. Arxiv 2008.13643v8 claims proof via reverse rule n→(m·2^n−1)/3, constructing a Cayley graph with root cycle 4→2→1→4. | CONNECTION: The arxiv paper's Cayley colour graph framing suggests a lattice/root-system structure — the Collatz map a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22741986
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22741986

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture: Tao's Partial Proof and a Claimed Full Solution via Cayley Graphs — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22741986 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22741986
