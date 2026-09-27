import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Leventides, John, Poulios, Costas, "Koopman operators and the $3x+1$-dynamical system", arXiv:2010.12987 [2020].

Title: Koopman operators and the $3x+1$-dynamical system

Abstract (from OpenAlex metadata, truncated):
The $3x+1$-problem (or Collatz problem) is a notorious conjecture in arithmetic. It can be viewed as iterating a map and, therefore, it is a dynamical system on the discrete space $\mathbb{N}$ of natural numbers. The emerging dynamical system is studied in the present work with methods from the theory of Koopman operators and $C^*$-algebras. This approach enables us to "lift" the $3x+1$-dynamical system from the state space (i.e the set $\mathbb{N}$) to spaces of functions defined on the state space, i.e. to sequence spaces. The advantage of this lifting is that the Collatz problem can be described via bounded linear operators, which consist an extensively studied area of Analysis. We study the properties of these operators and their relationship to the $3x+1$-problem. Furthermore, we use Fourier transform techniques to investigate the frequency content of the sequences of signs emerging

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2010.12987
-/

namespace Collatz.Papers.Arxiv2010_12987

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Leventides, John and Poulios, Costas, \"Koopman operators and the $3x+1$-dynamical system\", arXiv:2010.12987 [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2010_12987
