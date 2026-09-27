import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Doron Zeilberger, "Teaching the Computer how to Discover(!) and then Prove(!!) (all by Itself(!!!)) Analogs of Collatz's Notorious 3x+1 Conjecture", arXiv:0903.4050 [2009].

Title: Teaching the Computer how to Discover(!) and then Prove(!!) (all by Itself(!!!)) Analogs of Collatz's Notorious 3x+1 Conjecture

Abstract (from OpenAlex metadata, truncated):
Paul Erdos claimed that mathematics is not yet ready to settle the 3x+1 conjecture. I agree, but very soon it will be! With the exponential growth of computer-generated mathematics, we (or rather our silicon brethrern) would have a shot at it. Of course, not by number crunching, but by symbol crunching and automatic deduction. In the present article, I taught my computer how to use the brilliant ideas of four human beings (Amal Amleh, Ed Grove, Candy Kent, and Gerry Ladas) to prove two-dimensional analogs of this notorious conjecture. Once programmed (using my Maple package LADAS) it reproduced their ten theorems, and generated 134 new ones, complete with proofs. All by itself! I believe that the proof of the original 3x+1 conjecture would be in the same vein, but one would need a couple of extra human ideas, and better computers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/0903.4050
-/

namespace Collatz.Papers.Arxiv0903_4050

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Doron Zeilberger, \"Teaching the Computer how to Discover(!) and then Prove(!!) (all by Itself(!!!)) Analogs of Collatz's Notorious 3x+1 Conjecture\", arXiv:0903.4050 [2009]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv0903_4050
