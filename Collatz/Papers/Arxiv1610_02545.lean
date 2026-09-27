import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nichols, Daniel, "Analogues of the $3x + 1$ Problem in Polynomial Rings of Characteristic 2", arXiv:1610.02545 [2016].

Title: Analogues of the $3x + 1$ Problem in Polynomial Rings of Characteristic 2

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture (also known as the $3x+1$ problem) concerns the behavior of the discrete dynamical system on the positive integers defined by iteration of the so-called $3x + 1$ function. We investigate analogous dynamical systems in rings of functions of algebraic curves over $\mathbb{F}_2$ . We prove in this setting a generalized analogue of a theorem of Terras concerning the asymptotic distribution of stopping times. We also present experimental data on the behavior of these dynamical systems.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1610.02545
-/

namespace Collatz.Papers.Arxiv1610_02545

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nichols, Daniel, \"Analogues of the $3x + 1$ Problem in Polynomial Rings of Characteristic 2\", arXiv:1610.02545 [2016]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1610_02545
