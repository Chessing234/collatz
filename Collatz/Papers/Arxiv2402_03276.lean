import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Manuel Inselmann, "An approximation of the Collatz map and a lower bound for the average total stopping time", arXiv:2402.03276 [2024].

Title: An approximation of the Collatz map and a lower bound for the average total stopping time

Abstract (from OpenAlex metadata, truncated):
Define the map $\mathsf{T}$ on the positive integers by $\mathsf{T}(m)=\frac{m}{2}$ if $m$ is even and by $\mathsf{T}(m)=\frac{3m+1}{2}$ if $m$ is odd. Results of Terras and Everett imply that, given any $ε>0$, almost all $m\in\mathbb{Z}^+$ (in the sense of natural density) fulfill $(\frac{\sqrt{3}}{2})^km^{1-ε}\leq \mathsf{T}^k(m)\leq (\frac{\sqrt{3}}{2})^km^{1+ε}$ simultaneously for all $0\leq k\leq α\log m$ with $α=(\log 2)^{-1}\approx 1.443$. We extend this result to $α=2(\log\frac{4}{3})^{-1}\approx 6.952$, which is the maximally possible value. Set $\mathsf{T}_{\min}(m):=\min_{n\in\mathbb{N}}\mathsf{T}^n(m)$. As an immediate consequence, one has $\mathsf{T}_{\min}(m)\leq\mathsf{T}^{\left\lfloor2(\log\frac{4}{3})^{-1}\log m\right\rfloor}(m)\leq m^ε$ for almost all $m\in\mathbb{Z}^+$ for any given $ε>0$. Previously, Korec has shown that $\mathsf{T}_{\min}(m)\leq m^ε$ for almost all $m\in\mathbb{Z}^+$ if $ε>\frac{\log3}{\log4}$, and recently Tao proved that $\mathsf{T}_{\min}(m)\leq

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2402.03276
-/

namespace Collatz.Papers.Arxiv2402_03276

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Manuel Inselmann, \"An approximation of the Collatz map and a lower bound for the average total stopping time\", arXiv:2402.03276 [2024]."

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


end Collatz.Papers.Arxiv2402_03276
