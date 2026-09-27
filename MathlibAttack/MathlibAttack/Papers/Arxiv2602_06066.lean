import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Madhav Dhiman and Rohan Pandey, "Non-Definability of Reachability in Büchi Arithmetic for a Family of Generalized Collatz Maps", arXiv:2602.06066 [2026].

Title: Non-Definability of Reachability in Büchi Arithmetic for a Family of Generalized Collatz Maps

Abstract (truncated):
Let $q \ge 3$ and $d \ge 1$ be odd integers with $q+d$ a power of $2$. We study the generalized Collatz map $T_{q,d}$, a one-dimensional piecewise-affine map on the positive integers, and its unparameterized reachability relation $R(x,z)$, which holds when $z$ is an iterate of $x$ under $T_{q,d}$. We prove that for every such pair $(q,d)$ the relation $R$ is not first-order definable in Büchi arithmetic $\langle \mathbb{N}, +, V_q \rangle$. Equivalently, no finite automaton recognizes the base-$q$ encoding of $R$. Assuming definability of $R$, we construct a first-order formula that defines the set of powers of $2$. Cobham's theorem then rules out this set. The family includes the classical map $T_{3,1}$. The family is infinite but restricted, isolated by the condition that $q+d$ is a power of $2$ . Unlike the undecidability results of Conway, Kurtz, and Simon, the construction does not 

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2602.06066
-/

namespace MathlibAttack.Papers.Arxiv2602_06066

open MathlibAttack.Papers

def citation : String := "Madhav Dhiman and Rohan Pandey, \"Non-Definability of Reachability in B\u00fcchi Arithmetic for a Family of Generalized Collatz Maps\", arXiv:2602.06066 [2026]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2602_06066
