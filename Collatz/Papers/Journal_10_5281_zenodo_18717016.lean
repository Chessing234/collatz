import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Janik John, "Combinatorial Saturation and Machine-Checked Reduction of the Collatz Conjecture", 2026.

Title: Combinatorial Saturation and Machine-Checked Reduction of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The branch locus of the Syracuse map saturates at exactly $\mathbf{21{,}632}$cells. We reduce the Collatz conjecture to a finite-state mixing problem onthis saturated core: six structural properties, ranging from Diophantinedeficit bounds to $2$-adic residue equidistribution, are each machine-checkedin Lean~4 to be equivalent to the full conjecture, and all six concern thedynamics of trajectories confined to the same $21{,}632$ branch cells on the$(2,3)$-torus at resolutions $k \geq 216 = 2^3 \cdot 3^3$. The saturation isestablished by exhaustive computation over $2.5 \times 10^{13}$ trajectory stepsfrom $N = 10^{11}$ starting values, and is stable across three orders ofmagnitude in starting...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18717016
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18717016

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Janik John, \"Combinatorial Saturation and Machine-Checked Reduction of the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18717016 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18717016
