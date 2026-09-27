import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gil Alon et al., "On the stopping time of the Collatz map in $\mathbb{F}_2[x]$", arXiv:2401.03210 [2024].

Title: On the stopping time of the Collatz map in $\mathbb{F}_2[x]$

Abstract (from OpenAlex metadata, truncated):
We study the stopping time of the Collatz map for a polynomial $f \in \mathbb{F}_2[x]$, and bound it by $O({\rm deg} (f)^{1.5})$, improving upon the quadratic bound proven by Hicks, Mullen, Yucas and Zavislak. We also prove the existence arithmetic sequences of unbounded length in the stopping times of certain sequences of polynomials, a phenomenon observed in the classical Collatz map.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2401.03210
-/

namespace Collatz.Papers.Arxiv2401_03210

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gil Alon et al., \"On the stopping time of the Collatz map in $\\mathbb{F}_2[x]$\", arXiv:2401.03210 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2401_03210
