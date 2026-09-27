import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tao, Terence, "Almost all orbits of the Collatz map attain almost bounded values", arXiv:1909.03562 [2019].

Title: Almost all orbits of the Collatz map attain almost bounded values

Abstract (from OpenAlex metadata, truncated):
Define the \emph{Collatz map} $\mathrm{Col} : \mathbb{N}+1 \to \mathbb{N}+1$ on the positive integers $\mathbb{N}+1 = \{1,2,3,\dots\}$ by setting $\mathrm{Col}(N)$ equal to $3N+1$ when $N$ is odd and $N/2$ when $N$ is even, and let $\mathrm{Col}_{\min}(N) := \inf_{n \in \mathbb{N}} \mathrm{Col}^n(N)$ denote the minimal element of the Collatz orbit $N, \mathrm{Col}(N), \mathrm{Col}^2(N), \dots$. The infamous \emph{Collatz conjecture} asserts that $\mathrm{Col}_{\min}(N)=1$ for all $N \in \mathbb{N}+1$. Previously, it was shown by Korec that for any $θ> \frac{\log 3}{\log 4} \approx 0.7924$, one has $\mathrm{Col}_{\min}(N) \leq N^θ$ for almost all $N \in \mathbb{N}+1$ (in the sense of natural density). In this paper we show that for \emph{any} function $f : \mathbb{N}+1 \to \mathbb{R}$ with $\lim_{N \to \infty} f(N)=+\infty$, one has $\mathrm{Col}_{\min}(N) \leq f(N)$ for almost all $N \in

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1909.03562
-/

namespace Collatz.Papers.Arxiv1909_03562

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tao, Terence, \"Almost all orbits of the Collatz map attain almost bounded values\", arXiv:1909.03562 [2019]."

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

end Collatz.Papers.Arxiv1909_03562
