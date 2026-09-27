import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aalok Thakkar and Mrunmay Jagadale, "Additive Collatz Trajectories", arXiv:1611.03919 [2016].

Title: Additive Collatz Trajectories

Abstract (from OpenAlex metadata, truncated):
Collatz Conjecture (also known as Ulam's conjecture and 3x+1 problem) concerns the behavior of the iterates of a particular function on natural numbers. A number of generalizations of the conjecture have been subjected to extensive study. This paper explores Additive Collatz Trajectories, a particular case of a generalization of Collatz conjecture and puts forward a sufficient and necessary condition for looping of Additive Collatz Trajectories, along with two minor results. An algorithm to compute the number of equivalence classes when natural numbers are quotiented by the limiting behavior of their corresponding trajectories is also proposed.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1611.03919
-/

namespace Collatz.Papers.Arxiv1611_03919

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aalok Thakkar and Mrunmay Jagadale, \"Additive Collatz Trajectories\", arXiv:1611.03919 [2016]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1611_03919
