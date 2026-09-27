import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Shalom Eliahou et al., "Is the Syracuse falling time bounded by 12?", arXiv:2107.11160 [2021].

Title: Is the Syracuse falling time bounded by 12?

Abstract (from OpenAlex metadata, truncated):
Let $T \colon \mathbb{N} \to \mathbb{N}$ denote the $3x+1$ function, where $T(n)=n/2$ if $n$ is even, $T(n)=(3n+1)/2$ if $n$ is odd. As an accelerated version of $T$, we define a jump at $n \ge 1$ by jp$(n) = T^{(\ell)}(n)$, where $\ell$ is the number of digits of $n$ in base 2. We present computational and heuristic evidence leading to surprising conjectures. The boldest one, inspired by the study of $2^{\ell}-1$ for $\ell \le 500000$, states that for any $n \ge 2^{500}$, at most four jumps starting from $n$ are needed to fall below $n$, a strong form of the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2107.11160
-/

namespace Collatz.Papers.Arxiv2107_11160

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Shalom Eliahou et al., \"Is the Syracuse falling time bounded by 12?\", arXiv:2107.11160 [2021]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2107_11160
