import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Giuseppe Scollo, "ω-rewriting the Collatz Problem", 2004.

Title: ω-rewriting the Collatz Problem

Abstract (from harvested metadata, truncated):
The Collatz problem is comprised of two distinct, separate questions: existence of eventually periodic Collatz reductions with a nontrivial period, and existence of period-free Collatz reductions. This paper introduces a few distinct, related formalizations of the Collatz dynamics as term rewriting systems, using elementary concepts from the theory of state transition dynamics. Some of the subject systems act on finite terms, whereas others rewrite terms that are endowed with a countable, recursively defined structure. The latter presents a convenient framework for the investigation of extensions of the Collatz dynamics to dense systems.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5555/1227085.1227119
-/

namespace Collatz.Papers.Journal_10_5555_1227085_1227119

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Giuseppe Scollo, \"ω-rewriting the Collatz Problem\", Fundamenta Informaticae, DOI:10.5555/1227085.1227119 [2004]."

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

end Collatz.Papers.Journal_10_5555_1227085_1227119
