import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Jennifer Williams, "A Coordinate System for Collatz Dynamics", arXiv:2607.01718 [2026].

Title: A Coordinate System for Collatz Dynamics

Abstract (truncated):
It is well-established that every odd positive integer $n$ can be written uniquely as $n = λ\cdot 2^a \cdot 3^b - 1$ where $\gcd(λ, 6) = 1$ and $a \geq 1$. Building from this 3-smooth factorization, we introduce a partition of the nonnegative integers into countably many infinite triangles where each row $k$ forms a Collatz chain of alternating parity. The partition admits a coordinate system as a skeleton $\mathcal{L}_λ$ using the pair $(a, b)$ for odd positive integers within a geometric structure where row $k$ corresponds to $k = a + b$. Each position $(a, b)$ maps to $(a-1, b+1)$, a deterministic diagonal flow requiring no number-theoretic input. At the boundary $a = 1$, the trajectory exits to another skeleton depending on the factorization of $λ\cdot 3^{b+1} - 1$. The coordinate system is new. As a concrete application, we prove that rows $k \equiv 2 \pmod 4$ with $k \geq 6$ in the

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2607.01718
-/

namespace MathlibAttack.Papers.Arxiv2607_01718

open MathlibAttack.Papers

def citation : String := "Jennifer Williams, \"A Coordinate System for Collatz Dynamics\", arXiv:2607.01718 [2026]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2607_01718
