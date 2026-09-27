import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zhenmin Wang, "PFUSRC-080 Topological Morphogenesis of the Collatz Conjecture — From 3n+1 Iteration to 45° Biconical Interlayer Oscillation: Tracing a Number-Theoretic Problem to Its Geometric Boundary", 2026.

Title: PFUSRC-080 Topological Morphogenesis of the Collatz Conjecture — From 3n+1 Iteration to 45° Biconical Interlayer Oscillation: Tracing a Number-Theoretic Problem to Its Geometric Boundary

Abstract (from harvested metadata, truncated):
The Collatz conjecture (3n+1 problem) is a classic unsolved problem in number theory. Its iteration rule is: for any positive integer n, if n is odd, map n \to 3 n+1; if n is even, map n \to n / 2. The question is whether repeated iteration necessarily converges to 1 for all initial positive integers. Decades of computational verification have covered all positive integers up to 2^{68}, all of which converge, yet a complete rigorous proof remains elusive. This paper does not attempt a new proof within pure number theory. Instead, it repositions the problem through the PFUSRC topological morphogenesis framework. The core thesis is: the Collatz conjecture is not about proving whether a converg...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21317695
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21317695

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Zhenmin Wang, \"PFUSRC-080 Topological Morphogenesis of the Collatz Conjecture — From 3n+1 Iteration to 45° Biconical Interlayer Oscillation: Tracing a Number-Theoretic Problem to Its Geometric Boundary\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21317695 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21317695
