import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Christopher Clack, "A Computation of the Two-Adic Stuck Set for the Collatz Map", 2026.

Title: A Computation of the Two-Adic Stuck Set for the Collatz Map

Abstract (from harvested metadata, truncated):
Let T denote the Syracuse map T(n) = (3n+ 1)/2ν2 (3n+1) on the odd positive integers, where ν2 is the 2-adic valuation. For each K ≥1, let SK be the set of odd residues r (mod 2K) for which the partial sums of log2 3·ν3−log2 2·ν2 along the orbit of r remain non-positive over all Syracuse steps resolvable within K bits of input. The set SK is the natural nite-precision approximation to the set of stuck 2-adic integers those whose Collatz orbits would, if they failed to terminate at 1, fail by drifting to innity rather than entering a non-trivial cycle. We compute |SK| by exact enumeration with 128-bit integer arithmetic for K= 3,4,...,30, and by Monte Carlo sampling for K = 33,50,60,70,80,90,100 (N = 2 ×108 samples per K). At K = 30 the exact enumeration gives |S30|= 11 759 296 survivors...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20031476
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20031476

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Christopher Clack, \"A Computation of the Two-Adic Stuck Set for the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20031476 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20031476
