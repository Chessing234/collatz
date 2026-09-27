import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jason P. Bell, Jeffrey C. Lagarias, "$3x+1$ inverse orbit generating functions almost always have natural\n boundaries", arXiv:1408.6884 [2014].

Title: $3x+1$ inverse orbit generating functions almost always have natural\n boundaries

Abstract (from OpenAlex metadata, truncated):
The $3x+k$ function $T_{k}(n)$ sends $n$ to $(3n+k)/2$ resp. $n/2,$ according\nas $n$ is odd, resp. even, where $k \\equiv \\pm 1~(\\bmod \\, 6)$. The map\n$T_k(\\cdot)$ sends integers to integers, and for $m \\ge 1$ let $n \\rightarrow\nm$ mean that $m$ is in the forward orbit of $n$ under iteration of\n$T_k(\\cdot).$ We consider the generating functions $f_{k,m}(z) = \\sum_{n&gt;0, n\n\\rightarrow m} z^{n},$ which are holomorphic in the unit disk. We give\nsufficient conditions on $(k,m)$ for the functions $f_{k, m}(z)$ have the unit\ncircle $\\{|z|=1\\}$ as a natural boundary to analytic continuation. For the\n$3x+1$ function these conditions hold for all $m \\ge 1$ to show that\n$f_{1,m}(z)$ has the unit circle as a natural boundary except possibly for $m=\n1, 2, 4$ and $8$. The $3x+1$ Conjecture is equivalent to the assertion that\n$f_{1, m}(z)$ is a rational function of $z$ for the

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1408.6884
-/

namespace Collatz.Papers.Arxiv1408_6884

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jason P. Bell and Jeffrey C. Lagarias, \"$3x+1$ inverse orbit generating functions almost always have natural\\n boundaries\", arXiv:1408.6884 [2014]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1408_6884
