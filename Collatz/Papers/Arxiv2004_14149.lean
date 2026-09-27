import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Shûichi Ichikawa, Natsumi Kobayashi, "Preliminary study of custom computing hardware for the 3x+1 problem", arXiv:2004.14149 [2004].

Title: Preliminary study of custom computing hardware for the 3x+1 problem

Abstract (from OpenAlex metadata, truncated):
The 3x+1 problem is a simple but unsolved problem in number theory. Though computational verifications have been attempted for this problem, they are very time-consuming. This study describes the custom hardware designs for the 3x +1 problem, and discusses the feasibility of acceleration. A prototype hardware was implemented and evaluated with an Altera FPGA.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2004.14149
-/

namespace Collatz.Papers.Arxiv2004_14149

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sh\u00fbichi Ichikawa and Natsumi Kobayashi, \"Preliminary study of custom computing hardware for the 3x+1 problem\", arXiv:2004.14149 [2004]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2004_14149
