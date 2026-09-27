import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yoshiki Ueoka et al., "Resonant Gap Certificates and Rooted Dyadic Ancestry in Finite Collatz Record Ladders", 2026.

Title: Resonant Gap Certificates and Rooted Dyadic Ancestry in Finite Collatz Record Ladders

Abstract (from harvested metadata, truncated):
We study first passages between consecutive dyadic record thresholds for the shortcut Collatz map, using shifted coordinates in which the two branches are \(\A(x)=3x/2\) on even states and \(\B(x)=(x+1)/2\) on odd states. A record endpoint carries a terminal layer of suffixes whose linear multipliers exceed one. If this layer does not reach the beginning of the transition, the first failed suffix occurs at a one-sided \(2\)--\(3\) resonance depth and satisfies an exact reserve identity. The reserve splits into geometric threshold undershoot and normalized affine deficit. A discrete one-sixth gap separates the exact two-phase word from every nonextremal word. The normalized affine deficit obe...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21766609
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21766609

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yoshiki Ueoka et al., \"Resonant Gap Certificates and Rooted Dyadic Ancestry in Finite Collatz Record Ladders\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21766609 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21766609
