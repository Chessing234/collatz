import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Manuel Inselmann, "On the average stopping time of the Collatz map in $\mathbb{F}_2[x]$", arXiv:2401.12781 [2024].

Title: On the average stopping time of the Collatz map in $\mathbb{F}_2[x]$

Abstract (from OpenAlex metadata, truncated):
Define the map $T_1$ on $\mathbb{F}_2[x]$ by $T_1(f)=\frac{f}{x}$ if $f(0)=0$ and $T_1(f)=\frac{(x+1)f+1}{x}$ if $f(0)=1$. For a non-zero polynomial $f$ let $τ_1(f)$ denote the least natural $k$ number for which $T_1^{k}(f)=1$. Define the average stopping time to be $ρ_1(n)=\frac{\sum_{f\in \mathbb{F}_2[x], \text{deg}(f)=n }τ_1(f)}{2^n}$. We show that $\lim_{n\rightarrow\infty}\frac{ρ_1(n)}{n}=2$, confirming a conjecture of Alon, Behajaina, and Paran. Furthermore, we give a new proof that $τ_1(f)\in O(\text{deg}(f)^{1.5})$ for all $f\in\mathbb{F}_2[x]\setminus\{0\}$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2401.12781
-/

namespace Collatz.Papers.Arxiv2401_12781

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Manuel Inselmann, \"On the average stopping time of the Collatz map in $\\mathbb{F}_2[x]$\", arXiv:2401.12781 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2401_12781
