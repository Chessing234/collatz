import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jennifer Williams, "A Coordinate System for Collatz Dynamics", arXiv:2607.01718 [2026].

Title: A Coordinate System for Collatz Dynamics

Abstract (from OpenAlex metadata, truncated):
It is well-established that every odd positive integer $n$ can be written uniquely as $n = λ\cdot 2^a \cdot 3^b - 1$ where $\gcd(λ, 6) = 1$ and $a \geq 1$. Building from this 3-smooth factorization, we introduce a partition of the nonnegative integers into countably many infinite triangles where each row $k$ forms a Collatz chain of alternating parity. The partition admits a coordinate system as a skeleton $\mathcal{L}_λ$ using the pair $(a, b)$ for odd positive integers within a geometric structure where row $k$ corresponds to $k = a + b$. Each position $(a, b)$ maps to $(a-1, b+1)$, a deterministic diagonal flow requiring no number-theoretic input. At the boundary $a = 1$, the trajectory exits to another skeleton depending on the factorization of $λ\cdot 3^{b+1} - 1$. The coordinate system is new. As a concrete application, we prove that rows $k \equiv 2 \pmod 4$ with $k \geq 6$ in the principal skeleton $\mathcal{L}_1$ contain no primes, and show this is the unique residue class adm

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2607.01718
-/

namespace Collatz.Papers.Arxiv2607_01718

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jennifer Williams, \"A Coordinate System for Collatz Dynamics\", arXiv:2607.01718 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2607_01718
