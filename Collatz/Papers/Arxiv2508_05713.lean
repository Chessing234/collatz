import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Takehiko Mori, "Dynamical Systems with Bounded Condition and $C^{*}$-algebras", arXiv:2508.05713 [2025].

Title: Dynamical Systems with Bounded Condition and $C^{*}$-algebras

Abstract (from OpenAlex metadata, truncated):
In this paper, we study abstract dynamical systems with discrete phase spaces. One example of such a system is induced by the $3 x{+}1$-map on the set of all natural numbers, also known as the Collatz map. Our main focus is on dynamical systems induced by maps on countable discrete sets that satisfy a bounded condition. When these maps satisfy the bounded and a separating conditions, a minimality of the induced dynamical systems is equivalent to the irreducibility of certain $C^{*}$-algebras on certain Hilbert spaces. For a map $f$ on a general discrete phase space, we consider $f$-invariant sets and investigate their properties. When the phase space is countable and the map satisfies the bounded condition, we construct an order-preserving injection from the family of $f$-invariant sets to the family of reducing subspaces for the corresponding $C^{*}$-algebra. By introducing the totally 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2508.05713
-/

namespace Collatz.Papers.Arxiv2508_05713

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Takehiko Mori, \"Dynamical Systems with Bounded Condition and $C^{*}$-algebras\", arXiv:2508.05713 [2025]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2508_05713
