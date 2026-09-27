import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dyachenko, Eduard, "The Attractor Hole Model in the Collatz Conjecture", 2026.

Title: The Attractor Hole Model in the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The normalized odd Collatz map is analyzed as a discrete dynamical system in the ring of 2-adic integers. It is proven that the existence of periodic macro-cycles is equivalent to the solvability of a Diophantine system governed by an ensemble of projective $2 \times 2$ matrices. The finiteness of a macro-cycle is established to be consistent with the formation of invariant attractor hole windows. The topological isolation of these windows induces an overdetermined system of independent cyclic traversals, which strictly necessitates bitwise palindromic symmetry of the local 2-adic configurations (hole kernels). It is shown that for window widths $L \ge 9$, the fundamental incommensurability...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19064953
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19064953

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dyachenko, Eduard, \"The Attractor Hole Model in the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.19064953 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19064953
