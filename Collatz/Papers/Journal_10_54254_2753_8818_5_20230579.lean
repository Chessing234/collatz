import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ge, Kevin, "Algorithm speed-ups of 3x+1 convergence verification sieves", 2023.

Title: Algorithm speed-ups of 3x+1 convergence verification sieves

Abstract (from harvested metadata, truncated):
The 3x+1 Conjecture is a notorious open elementary number theory problem for its deceitful triviality. Several algorithms described in the past for the numerical verification for the convergence, one of which implemented an improvement of sieves. However, most papers focused on theoretical aspects of the sieve, and empirical results were rarely discussed. This paper presents data from implementing sieves on a relatively high-level language, as well as some helpful unmentioned rudimentary algebraic facts about sieves. Several algorithms for convergence verification of the 3x+1 Problem had been developed since the 1970s. This paper tests an algorithm presented in a 1999 paper and explores the runtime growth to input size.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.54254/2753-8818/5/20230579
-/

namespace Collatz.Papers.Journal_10_54254_2753_8818_5_20230579

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ge, Kevin, \"Algorithm speed-ups of 3x+1 convergence verification sieves\", Theoretical and Natural Science, DOI:10.54254/2753-8818/5/20230579 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_54254_2753_8818_5_20230579
