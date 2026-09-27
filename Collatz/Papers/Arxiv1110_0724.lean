import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hassan, Sk. S., Choudhury, P. Pal, Nayak, B. K., Ghosh, A., Banerjee, J., "Integral Value Transformations: A Class of Affine Discrete Dynamical Systems and an Application", arXiv:1110.0724 [2011].

Title: Integral Value Transformations: A Class of Affine Discrete Dynamical Systems and an Application

Abstract (from arXiv metadata, truncated):
In this paper, the notion of Integral Value Transformations (IVTs), a class of Discrete Dynamical Maps has been introduced. Then notion of Affine Discrete Dynamical System (ADDS) in the light of IVTs is defined and some rudimentary mathematical properties of the system are depicted. Collatz Conjecture is one of the most enigmatic problems in 20th Century. The Conjecture was posed by German Mathematician L. Collatz in 1937. There are much advancement in generalizing and defining analogous conjectures, but even to the date, there is no fruitful result for the advancement for the settlement of the conjecture. We have made an effort to make a Collatz type problem in the domain of IVTs and we have been able to solve the problem in 2011 [1]. Here mainly, we have focused and inquired on Collatz-like ADDS. Finally, we have designed the Optimal Distributed and Parallel Environment (ODPE) in the l

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1110.0724
-/

namespace Collatz.Papers.Arxiv1110_0724

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hassan, Sk. S. et al., \"Integral Value Transformations: A Class of Affine Discrete Dynamical Systems and an Application\", arXiv:1110.0724 [2011]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1110_0724
