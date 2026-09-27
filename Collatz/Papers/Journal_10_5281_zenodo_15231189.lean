import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fathi, Kevin, "An Information-Theoretic Reframing of the Collatz Conjecture: From Heuristic Frequencies to Algorithmic Randomness", 2026.

Title: An Information-Theoretic Reframing of the Collatz Conjecture: From Heuristic Frequencies to Algorithmic Randomness

Abstract (from harvested metadata, truncated):
This paper presents a novel framework for analyzing the Collatz conjecture by reformulating the problem within the domain of symbolic dynamics and algorithmic information theory. We model the iterated application of the odd-step Collatz map, $T^{*}(n) = (3n+1)/2^{\nu_{2}(3n+1)}$, as a deterministic, confluent rewrite system. By applying the entropy-complexity correspondence for such systems, we establish a precise relationship between the algorithmic complexity of an integer and the information-theoretic properties of its trajectory. The core contribution of this work is the replacement of heuristic statistical assumptions, such as the Uniform Dip Frequency Conjecture, with a more fundamenta...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15231189
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15231189

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fathi, Kevin, \"An Information-Theoretic Reframing of the Collatz Conjecture: From Heuristic Frequencies to Algorithmic Randomness\", Zenodo, DOI:10.5281/zenodo.15231189 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_15231189
