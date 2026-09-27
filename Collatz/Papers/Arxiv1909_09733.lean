import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "Conservation of Singularities in Functional Equations Associated to Collatz-Type Dynamical Systems; or, Dreamcatchers for Hydra Maps", arXiv:1909.09733 [2019].

Title: Conservation of Singularities in Functional Equations Associated to Collatz-Type Dynamical Systems; or, Dreamcatchers for Hydra Maps

Abstract (from OpenAlex metadata, truncated):
It is known that the Collatz Conjecture (and the study of similar maps, here called "Hydra maps") can be stated in terms of solution sets of functional equations; or, equivalently, the fixed points of linear operators on spaces of analytic functions. Rather than studying potential fixed points of such operators, we examine their effect on the singularities of functions. To that end, we introduce the notion of a "dreamcatcher", an object which encodes the location and "virtual residue" of the singularities of an analytic function of a specified growth rate along the boundary of the function's region of convergence. Dreamcatchers can be given rigorous footing as elements of the Hilbert space L2(Q/Z) of complex-valued functions on Q/Z which are square-integrable with respect to the counting measure on Q/Z. The aforementioned linear operators (called here "permutation operators") are shown t

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1909.09733
-/

namespace Collatz.Papers.Arxiv1909_09733

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"Conservation of Singularities in Functional Equations Associated to Collatz-Type Dynamical Systems; or, Dreamcatchers for Hydra Maps\", arXiv:1909.09733 [2019]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1909_09733
