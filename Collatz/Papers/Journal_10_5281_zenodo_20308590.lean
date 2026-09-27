import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Su, Zhen, "A First-Principles Proof of the Collatz Conjecture", 2026.

Title: A First-Principles Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper presents a deductive analysis of the Collatz iteration, also known as the $3n+1$ problem, within the axiomatic system of natural numbers. The study proceeds solely from the properties of positive integers, including well-ordering, parity, and divisibility, without numerical induction, heuristic reasoning, or external assumptions. It is shown that no strictly increasing infinite orbits exist, all trajectories are globally bounded, and bounded sequences are eventually periodic. Further, through Diophantine analysis and parity arguments, all admissible cycles are classified. The results characterize the asymptotic behavior of all Collatz sequences.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20308590
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20308590

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Su, Zhen, \"A First-Principles Proof of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.20308590 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20308590
