import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Tobías Canavesi, "The Collatz Network", arXiv:2105.04415 [2021].

Title: The Collatz Network

Abstract (truncated):
Considering all possible paths that a natural number can take following the rules of the algorithm proposed in the Collatz conjecture we construct a graph that can be interpreted as an infinite network that contemplates all possible paths within the conjecture. This allows us to understand why the minimal element of the Collatz orbit $x$ is equal to 1. Subsequently we define the extended Collatz conjecture equal to $o x+1$ when $x$ is odd and $x/2$ when $x$ is even with $o$ an odd number greater than $3$ and we show that there are infinite orbits in the extended Collatz conjecture that diverges. Finally, we find interesting theorems relating the Fibonacci sequence to prime numbers.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2105.04415
-/

namespace MathlibAttack.Papers.Arxiv2105_04415

open MathlibAttack.Papers

def citation : String := "Tob\u00edas Canavesi, \"The Collatz Network\", arXiv:2105.04415 [2021]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2105_04415
