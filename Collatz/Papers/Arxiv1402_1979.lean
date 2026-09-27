import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nik Lygerōs, Olivier Rozier, "Dynamique du problème $3x+1$ sur la droite réelle", arXiv:1402.1979 [2014].

Title: Dynamique du problème $3x+1$ sur la droite réelle

Abstract (from OpenAlex metadata, truncated):
The 3x+1 problem is a difficult conjecture dealing with quite a simple algorithm on the positive integers. A possible approach is to go beyond the discrete nature of the problem, following M. Chamberland who used an analytic extension to the half-line $\mathbb{R}^{+}$. We complete his results on the dynamic of the critical points and obtain a new formulation the 3x+1 problem. We clarify the links with the question of the existence of wandering intervals. Then, we extend the study of the dynamic to the half-line $\mathbb{R}^{-}$, in connection with the 3x-1 problem. Finally, we analyze the mean behaviour of real iterations near infinity and present a method based on a heuristic argument by R. E. Crandall in the discrete case. It follows that the average growth rate of the iterates is close to $(2+\sqrt{3})/4$ under a condition of uniform distribution modulo 2.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1402.1979
-/

namespace Collatz.Papers.Arxiv1402_1979

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nik Lyger\u014ds and Olivier Rozier, \"Dynamique du probl\u00e8me $3x+1$ sur la droite r\u00e9elle\", arXiv:1402.1979 [2014]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1402_1979
