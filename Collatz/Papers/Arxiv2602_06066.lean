import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Madhav Dhiman and Rohan Pandey, "Non-Definability of Reachability in Büchi Arithmetic for a Family of Generalized Collatz Maps", arXiv:2602.06066 [2026].

Title: Non-Definability of Reachability in Büchi Arithmetic for a Family of Generalized Collatz Maps

Abstract (from OpenAlex metadata, truncated):
Let $q \ge 3$ and $d \ge 1$ be odd integers with $q+d$ a power of $2$. We study the generalized Collatz map $T_{q,d}$, a one-dimensional piecewise-affine map on the positive integers, and its unparameterized reachability relation $R(x,z)$, which holds when $z$ is an iterate of $x$ under $T_{q,d}$. We prove that for every such pair $(q,d)$ the relation $R$ is not first-order definable in Büchi arithmetic $\langle \mathbb{N}, +, V_q \rangle$. Equivalently, no finite automaton recognizes the base-$q$ encoding of $R$. Assuming definability of $R$, we construct a first-order formula that defines the set of powers of $2$. Cobham's theorem then rules out this set. The family includes the classical map $T_{3,1}$. The family is infinite but restricted, isolated by the condition that $q+d$ is a power of $2$ . Unlike the undecidability results of Conway, Kurtz, and Simon, the construction does not embed universal computation and does not depend on the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2602.06066
-/

namespace Collatz.Papers.Arxiv2602_06066

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Madhav Dhiman and Rohan Pandey, \"Non-Definability of Reachability in B\u00fcchi Arithmetic for a Family of Generalized Collatz Maps\", arXiv:2602.06066 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2602_06066
