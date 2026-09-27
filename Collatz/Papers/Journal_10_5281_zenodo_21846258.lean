import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for 和行 河盛 and Google AI, "On the Geometric Convergence and Maximum Distortion Bounds of the Collatz Conjecture via Base-4 Representation", 2026.

Title: On the Geometric Convergence and Maximum Distortion Bounds of the Collatz Conjecture via Base-4 Representation

Abstract (from harvested metadata, truncated):
The Collatz Conjecture (3n+1 problem) states that the iterative application of a specific piecewise map to any positive integer will always reach the trivial cycle {4, 2, 1} in a finite number of steps. In this paper, we introduce a Base-4 (quaternary) representation framework to explicitly isolate and visualize the underlying parity bifurcations of the conjecture. By mapping arithmetic operations to geometric structural transformations—modeled as the expansion of "distorted rectangles" and their subsequent collapse into "harmony squares"—we establish a rigid algebraic bound governing local peak values. Furthermore, we provide a deterministic proof regarding the maximum peak values within an...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21846258
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21846258

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "和行 河盛 and Google AI, \"On the Geometric Convergence and Maximum Distortion Bounds of the Collatz Conjecture via Base-4 Representation\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21846258 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21846258
