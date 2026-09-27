import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Haoyu Ma et al., "Xmark: Dynamic Software Watermarking Using Collatz Conjecture", 2019.

Title: Xmark: Dynamic Software Watermarking Using Collatz Conjecture

Abstract (from harvested metadata, truncated):
Dynamic software watermarking is one of the major countermeasures against software licensing violations. However, conventional dynamic watermarking approaches have exhibited a number of weaknesses including exploitable payload semantics, exploitable embedding/recognition procedures, and weak correlation between payload and subject software. This paper presents a novel dynamic watermarking method, Xmark, which leverages a well-known unsolved mathematical problem referred to as the Collatz conjecture. Our method works by transforming selected conditional constructs (which originally belonged to the software to be watermarked) with a control flow obfuscation technique based on Collatz conjecture. These obfuscation routines are built in a particular way such that they are able to express a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/tifs.2019.2908071
-/

namespace Collatz.Papers.Journal_10_1109_tifs_2019_2908071

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Haoyu Ma et al., \"Xmark: Dynamic Software Watermarking Using Collatz Conjecture\", IEEE Transactions on Information Forensics and Security, DOI:10.1109/tifs.2019.2908071 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_tifs_2019_2908071
