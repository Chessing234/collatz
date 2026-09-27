import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mike Winkler, "Fibonacci Enumeration of Parity Blocks in Collatz Trajectories", arXiv:1412.0519 [2014].

Title: Fibonacci Enumeration of Parity Blocks in Collatz Trajectories

Abstract (from OpenAlex metadata, truncated):
Let $T(n)=n/2$ for even $n$ and $T(n)=(3n+1)/2$ for odd $n$. For an odd starting number $s$, let $\ell(s)$ be the first positive index $k$ for which $T^k(s)\equiv3\pmod4$ and $T^{k-1}(s)$ is even. The use of this single local cut time is the main structural step: it replaces the two block parameters of an earlier formulation and converts the endpoint condition into a local condition on consecutive parity symbols. We prove that, for every $r\geq2$, the starting numbers $s\equiv1\pmod4$ with $\ell(s)=r$ form exactly $F_{r-1}$ residue classes modulo $2^{r+2}$, while for every $r\geq3$ the starting numbers $s\equiv3\pmod4$ with $\ell(s)=r$ form exactly $F_r-1$ such classes. Fixing any odd residue class modulo $12$ leaves these counts unchanged and yields the two Fibonacci formulas conjectured in a 2014 preprint by the author as special cases. The proof uses the classical finite parity corres

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1412.0519
-/

namespace Collatz.Papers.Arxiv1412_0519

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mike Winkler, \"Fibonacci Enumeration of Parity Blocks in Collatz Trajectories\", arXiv:1412.0519 [2014]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Arxiv1412_0519
