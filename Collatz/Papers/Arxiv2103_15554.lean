import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Brian M. Gurbaxani, "An Engineering and Statistical Look at the Collatz (3n + 1) Conjecture", arXiv:2103.15554 [2021].

Title: An Engineering and Statistical Look at the Collatz (3n + 1) Conjecture

Abstract (from OpenAlex metadata, truncated):
The famous (3n + 1) or Collatz conjecture has admitted some progress over the last several decades towards the conclusion that the conjecture is true (i.e. that all Collatz sequences will eventually reach a value of one), but has stubbornly resisted a proof. Many professional mathematicians have applied an impressive array of machinery to its analysis, and discovered some limits or boundaries to where violations of the Collatz conjecture must be, if they exist. Here we attempt to look at the conjecture differently than most mathematicians or number theorists, i.e. we will study the conjecture from the points of view of a statistician/data scientist and of an engineer. As a statistician or data scientist, we look at Collatz sequences as if they were sequences found in nature, like a collection of time series produced by some natural process, ignoring for the time being their completely deterministic origins. As an engineer, we try to tinker with Collatz sequences to see what makes them 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2103.15554
-/

namespace Collatz.Papers.Arxiv2103_15554

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Brian M. Gurbaxani, \"An Engineering and Statistical Look at the Collatz (3n + 1) Conjecture\", arXiv:2103.15554 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2103_15554
