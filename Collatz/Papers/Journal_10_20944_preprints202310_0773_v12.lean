import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "The Collatz Conjecture: A New Proof using Algebraic Inverse Trees", 2023.

Title: The Collatz Conjecture: A New Proof using Algebraic Inverse Trees

Abstract (from harvested metadata, truncated):
This paper presents a novel approach to demonstrate the Collatz Conjecture, an unsolved problem in mathematics stating that all positive integers will eventually converge to 1 when subjected to a recursive sequence of operations. We introduce Algebraic Inverse Trees (AITs), innovative data structures that characterize relationships within the Collatz sequence by tracing inverse transformations back to the origin. Leveraging properties unveiled through this inverted representation, including absence of non-trivial cycles and guaranteed convergence of paths, we construct a topological framework to formally prove that all trajectories invariably lead to 1 under the Collatz iterative process. This modern technique provides not only the machinery to manifest a rigorous proof, but also grants...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202310.0773.v12
-/

namespace Collatz.Papers.Journal_10_20944_preprints202310_0773_v12

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"The Collatz Conjecture: A New Proof using Algebraic Inverse Trees\", Preprints.org, DOI:10.20944/preprints202310.0773.v12 [2023]."

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

end Collatz.Papers.Journal_10_20944_preprints202310_0773_v12
