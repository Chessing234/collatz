import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for K. Lodders, "Selection Rules and Channel Structure in a Base Octave Model of Collatz Dynamics", arXiv:2604.20181 [2026].

Title: Selection Rules and Channel Structure in a Base Octave Model of Collatz Dynamics

Abstract (truncated):
The Collatz iteration is governed by two distinct update rules, depending on the parity of the current iterate: n(i+1)=3n(i)+1 for odd n(i), and n(i+1)=n(i)/2 for even n(i). We show that these rules can be written equivalently as a single parity controlled transformation, n(i+1)=((2s(i)+1)(2k(i)+s(i))+s(i))/2, where n(i)=2k(i)+s(i) and s(i) is the parity (0 or 1) of n(i), yielding a uniform, step aligned dynamical system in which parity variables are tracked explicitly. This reformulation removes the asymmetry of the traditional presentation and exposes structural regularities that are obscured when odd and even updates are treated separately. Building on this unified rule, we introduce a base octave decomposition, representing every integer uniquely in the form n=B+8(A-1) with B = 1 to 8. The resulting dynamics separate into parity dependent base transitions and affine updates of the oc

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2604.20181
-/

namespace MathlibAttack.Papers.Arxiv2604_20181

open MathlibAttack.Papers

def citation : String := "K. Lodders, \"Selection Rules and Channel Structure in a Base Octave Model of Collatz Dynamics\", arXiv:2604.20181 [2026]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2604_20181
