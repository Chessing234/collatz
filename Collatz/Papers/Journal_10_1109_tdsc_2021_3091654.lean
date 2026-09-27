import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Haoyu Ma et al., "Secure Repackage-Proofing Framework for Android Apps Using Collatz Conjecture", 2021.

Title: Secure Repackage-Proofing Framework for Android Apps Using Collatz Conjecture

Abstract (from harvested metadata, truncated):
App repackaging has been raising serious concerns about the health of the Android ecosystem, and repackage-proofing is an important mitigation against threat of such attacks. However, existing app repackage-proofing schemes were only evaluated against trivial adversaries simulated using analyzers for other purposes (e.g., disclosing privacy leakage vulnerabilities), hence were shown “effective” mainly because their key programming features were not even supported by those toolkits. Furthermore, existing works have also neglected dynamic adversaries capable of manipulating victim apps at runtime, making them vulnerable against such stronger opponents. In this article, we propose a novel repackage-proofing framework, which deploys distributed detection and response sites into the subject...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/tdsc.2021.3091654
-/

namespace Collatz.Papers.Journal_10_1109_tdsc_2021_3091654

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Haoyu Ma et al., \"Secure Repackage-Proofing Framework for Android Apps Using Collatz Conjecture\", IEEE Transactions on Dependable and Secure Computing, DOI:10.1109/tdsc.2021.3091654 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_tdsc_2021_3091654
