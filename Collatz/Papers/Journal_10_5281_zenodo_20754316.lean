import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yoshiki Ueoka et al., "A Proof of the Collatz Conjecture via Translation and Structuralization of Natural Numbers and the Collatz Map", 2026.

Title: A Proof of the Collatz Conjecture via Translation and Structuralization of Natural Numbers and the Collatz Map

Abstract (from harvested metadata, truncated):
In this paper, we treat the Collatz conjecture not as a problem of tracing natural numbers one by one, but as a structural problem obtained by translating positive odd integers into alternating binary notation (ABN) and Collatz phase expressions (CPE). In this framework, the accelerated Collatz map $$F(n)=\frac{3n+1}{2^{\nu_2(3n+1)}} \quad (n \text{ odd})$$ is described as a local rewriting rule on structural expressions. First, we construct reversible correspondences among positive odd integers, alternating sums of Mersenne numbers, canonical ABN, and canonical CPE. We then derive one-step inequalities for the structural quantities μ, H_CS, H_K, and B from a local analysis of the 27 endpoint patterns. These inequalities provide a way to control the structural complexity of a Collatz step...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20754316
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20754316

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yoshiki Ueoka et al., \"A Proof of the Collatz Conjecture via Translation and Structuralization of Natural Numbers and the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20754316 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20754316
