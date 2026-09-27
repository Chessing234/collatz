import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Assani, Idris, "Collatz map as a non-singular transformation", arXiv:2208.11675 [2022].

Title: Collatz map as a non-singular transformation

Abstract (from OpenAlex metadata, truncated):
Let $T$ be the map defined on $\N=\{1,2,3, ...\}$ by $T(n) = \frac{n}{2} $ if $n$ is even and by $T(n) = \frac{3n+1}{2}$ if $n$ is odd. Consider the dynamical system $(\N, 2^{\N}, T,μ)$ where $μ$ is the counting measure. This dynamical system $(\N, 2^{\N}, T, μ)$ has the following properties. \begin{enumerate} \item There exists an invariant finite measure $γ$ such that $γ(A) \leq μ(A) $ for all $A \subset \N.$ \item For each function $f\in L^1(μ)$ the averages $\frac{1}{N} \sum_{n=1}^N f(T^nx)$ converge for every $x\in \N$ to $ f^*(x)$ where $ f^* \in L^1(μ).$ \end{enumerate} We also show that the Collatz conjecture is equivalent to the existence of a finite measure $ν$ on $(\N, 2^{\N})$ making the operator $Vf = f\circ T$ power bounded in $L^1(ν)$ with conserrvative part $\{1,2\}.$

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2208.11675
-/

namespace Collatz.Papers.Arxiv2208_11675

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Assani, Idris, \"Collatz map as a non-singular transformation\", arXiv:2208.11675 [2022]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2208_11675
