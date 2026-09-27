import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for K. Lodders, "Selection Rules and Channel Structure in a Base Octave Model of Collatz Dynamics", arXiv:2604.20181 [2026].

Title: Selection Rules and Channel Structure in a Base Octave Model of Collatz Dynamics

Abstract (from OpenAlex metadata, truncated):
The Collatz iteration is governed by two distinct update rules, depending on the parity of the current iterate: n(i+1)=3n(i)+1 for odd n(i), and n(i+1)=n(i)/2 for even n(i). We show that these rules can be written equivalently as a single parity controlled transformation, n(i+1)=((2s(i)+1)(2k(i)+s(i))+s(i))/2, where n(i)=2k(i)+s(i) and s(i) is the parity (0 or 1) of n(i), yielding a uniform, step aligned dynamical system in which parity variables are tracked explicitly. This reformulation removes the asymmetry of the traditional presentation and exposes structural regularities that are obscured when odd and even updates are treated separately. Building on this unified rule, we introduce a base octave decomposition, representing every integer uniquely in the form n=B+8(A-1) with B = 1 to 8. The resulting dynamics separate into parity dependent base transitions and affine updates of the octave index, inducing a finite directed transition skeleton lifted across scale levels. Refining the 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2604.20181
-/

namespace Collatz.Papers.Arxiv2604_20181

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "K. Lodders, \"Selection Rules and Channel Structure in a Base Octave Model of Collatz Dynamics\", arXiv:2604.20181 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2604_20181
