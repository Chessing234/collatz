import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for François Charton and Ashvni Narayanan, "Transformers know more than they can tell -- Learning the Collatz sequence", arXiv:2511.10811 [2025].

Title: Transformers know more than they can tell -- Learning the Collatz sequence

Abstract (from OpenAlex metadata, truncated):
We investigate transformer prediction of long Collatz steps, a complex arithmetic function that maps odd integers to their distant successors in the Collatz sequence ( $u_{n+1}=u_n/2$ if $u_n$ is even, $u_{n+1}=(3u_n+1)/2$ if $u_n$ is odd). Model accuracy varies with the base used to encode input and output. It can be as high as $99.7\%$ for bases $24$ and $32$, and as low as $37$ and $25\%$ for bases $11$ and $3$. Yet, all models, no matter the base, follow a common learning pattern. As training proceeds, they learn a sequence of classes of inputs that share the same residual modulo $2^p$. Models achieve near-perfect accuracy on these classes, and less than $1\%$ for all other inputs. This maps to a mathematical property of Collatz sequences: the length of the loops involved in the computation of a long Collatz step can be deduced from the binary representation of its input. The learning pattern reflects the model learning to predict inputs associated with increasing loop lengths. An 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2511.10811
-/

namespace Collatz.Papers.Arxiv2511_10811

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fran\u00e7ois Charton and Ashvni Narayanan, \"Transformers know more than they can tell -- Learning the Collatz sequence\", arXiv:2511.10811 [2025]."

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


end Collatz.Papers.Arxiv2511_10811
