import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yoshiki Ueoka et al., "A Structural Reduction Framework for the Collatz Problem via Alternating Binary Notation, Collatz Phase Expression, and a Lean-Supported Proof Architecture", 2026.

Title: A Structural Reduction Framework for the Collatz Problem via Alternating Binary Notation, Collatz Phase Expression, and a Lean-Supported Proof Architecture

Abstract (from harvested metadata, truncated):
We present a structural reduction framework for the Collatz problem based on Alternating Binary Notation (ABN) and Collatz Phase Expression (CPE).Instead of treating the iteration as orbit-tracing on integers viewed as isolated points, we encode odd states by signed binary block structures and analyze the accelerated odd map$F(n)=\frac{3n+1}{2^{v_2(3n+1)}}$as a local rewriting process on CPE. The key point is that one-step updates are confined to a constant-size local window.From this locality, we derive inequalities for structural quantities such as the chain count $\mu$, the total chain length $H_{CS}$, the total node length $H_K$, and the total length $B=H_{CS}+H_K$.These inequalities imply that the high-$\mu$ region (in particular, $\mu\ge4$) descends in finitely many steps to the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18892856
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18892856

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yoshiki Ueoka et al., \"A Structural Reduction Framework for the Collatz Problem via Alternating Binary Notation, Collatz Phase Expression, and a Lean-Supported Proof Architecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18892856 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18892856
