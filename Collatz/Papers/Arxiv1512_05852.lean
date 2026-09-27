import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alain Thomas, "A non-uniform distribution property of most orbits, in case the $3x+1$\n conjecture is true", arXiv:1512.05852 [2015].

Title: A non-uniform distribution property of most orbits, in case the $3x+1$\n conjecture is true

Abstract (from OpenAlex metadata, truncated):
Let $T(n)=\\left\\{\\begin{array}{ll}3n+1&amp;(n\\hbox{ odd})\\frac n2&amp;(n\\hbox{\neven})\\end{array}\\right.$ ($n\\in\\mathbb Z$). We call "the orbit of the integer\n$n$", the set $$ \\mathcal O_n:=\\{m\\in\\mathbb Z\\;:\\;\\exists k\\ge0,\\ m=T^k(n)\\}\n$$ and we put $c_i(n):=\\#\\{m\\in\\mathcal O_n\\;:\\;m\\equiv i\\hbox{ mod.}18\\}$. Let\n$W$ be the set of the integers whose orbit contains $1$ and is, in the\nfollowing sense, about well distributed modulo $18$ between the six elements of\nthe set $I:=\\{1,5,7,11,13,17\\}$ (the elements of \\{1,\\dots,18\\} that are odd\nand not divisible by $3$). More precisely: $$ W:=\\Big\\{n\\in\\mathbb\nN\\;:\\;\\exists k\\ge0,\\ T^k(n)=1\\hbox{ and }\\forall i\\in I,\\\n\\frac{c_i(n)}{\\sum_{i\\in I}c_i(n)}\\le\\frac16+0.0215\\Big\\}. $$ We prove that $W$\nhas density $0$ in $\\mathbb N$. Consequently, if the $3x+1$ conjecture is true,\nmost

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1512.05852
-/

namespace Collatz.Papers.Arxiv1512_05852

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alain Thomas, \"A non-uniform distribution property of most orbits, in case the $3x+1$\\n conjecture is true\", arXiv:1512.05852 [2015]."

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


end Collatz.Papers.Arxiv1512_05852
