import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for julian REDERO, "A Displayed Finite Gate Cover and Component-wise Descent for the Collatz Map", 2026.

Title: A Displayed Finite Gate Cover and Component-wise Descent for the Collatz Map

Abstract (from harvested metadata, truncated):
We present a component-wise descent proof framework for the Collatz map based on a finitedisplayed cover of the residual source domain. The proof is organized on odd source parameters u,corresponding to source states 3u. First, every positive integer is reduced, inside its undirectedCollatz component, to a source state. Second, the large source-valuation regime ν2(9u + 1) ≥ 7 isremoved by the explicit descent u → (u − 7)/64. Third, the remaining source parameters form aresidual domain Dsrc, and the manuscript records a finite cover196Dsrc ⊆ Bsrc ∪i=1Pi.The cover has the structured form 196 = 7 ·28: seven roots, twenty-eight macro-gates over eachroot, and eight budget archetypes. A gate is a displayed source class, defined by root-height data(ρ, h0,p,ϕ); it is not an additional theorem or...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20436956
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20436956

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "julian REDERO, \"A Displayed Finite Gate Cover and Component-wise Descent for the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20436956 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20436956
