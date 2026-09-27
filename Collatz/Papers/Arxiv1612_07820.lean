import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Timotéo Carletti and Duccio Fanelli, "Quantifying the degree of average contraction of Collatz orbits", arXiv:1612.07820 [2016].

Title: Quantifying the degree of average contraction of Collatz orbits

Abstract (from OpenAlex metadata, truncated):
We here elaborate on a quantitative argument to support the validity of the Collatz conjecture, also known as the (3x + 1) or Syracuse conjecture. The analysis is structured as follows. First, three distinct fixed points are found for the third iterate of the Collatz map, which hence organise in a period 3 orbit of the original map. These are 1, 2 and 4, the elements which define the unique attracting cycle, as hypothesised by Collatz. To carry out the calculation we write the positive integers in modulo 8 (mod8 ), obtain a closed analytical form for the associated map and determine the transitions that yield contracting or expanding iterates in the original, infinite-dimensional, space of positive integers. Then, we consider a Markov chain which runs on the reduced space of mod8 congruence classes of integers. The transition probabilities of the Markov chain are computed from the determ

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1612.07820
-/

namespace Collatz.Papers.Arxiv1612_07820

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Timot\u00e9o Carletti and Duccio Fanelli, \"Quantifying the degree of average contraction of Collatz orbits\", arXiv:1612.07820 [2016]."

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


end Collatz.Papers.Arxiv1612_07820
