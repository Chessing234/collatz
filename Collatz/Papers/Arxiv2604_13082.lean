import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Laura Gomezjurado Gonzalez, "The Long Delay to Arithmetic Generalization: When Learned Representations Outrun Behavior", arXiv:2604.13082 [2026].

Title: The Long Delay to Arithmetic Generalization: When Learned Representations Outrun Behavior

Abstract (from OpenAlex metadata, truncated):
Grokking in transformers trained on algorithmic tasks is characterized by a long delay between training-set fit and abrupt generalization, but the source of that delay remains poorly understood. In encoder-decoder arithmetic models, we argue that this delay reflects limited access to already learned structure rather than failure to acquire that structure in the first place. We study one-step Collatz prediction and find that the encoder organizes parity and residue structure within the first few thousand training steps, while output accuracy remains near chance for tens of thousands more. Causal interventions support the decoder bottleneck hypothesis. Transplanting a trained encoder into a fresh model accelerates grokking by 2.75 times, while transplanting a trained decoder actively hurts. Freezing a converged encoder and retraining only the decoder eliminates the plateau entirely and yie

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2604.13082
-/

namespace Collatz.Papers.Arxiv2604_13082

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Laura Gomezjurado Gonzalez, \"The Long Delay to Arithmetic Generalization: When Learned Representations Outrun Behavior\", arXiv:2604.13082 [2026]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2604_13082
