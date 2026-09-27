import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for FarhadAliabdali Aliabdali, "Collatz Analysis Two Stage Tree and Multiset Calculus", 2026.

Title: Collatz Analysis Two Stage Tree and Multiset Calculus

Abstract (from harvested metadata, truncated):
The Collatz map T(n)=n/2 for even n and T(n)=3n+1 for odd n admits classical affine descriptions via parity vectors. The shortcut map compresses each odd event into the macro step (3n+1)/2, obscuring intermediate algebraic states. We introduce a two-stage branching formalism that decomposes the odd-step operation into two explicit sub-operations: a rewrite step R (expressing n=2x+1) followed by a forced follow-up C (mapping x→3x+2). This decomposition reveals intermediate states invisible in classical parity-vector representations and yields an explicit monomial expansion for the trajectory offset σ_N (w). We prove that complete two-stage words compress under RC→O to recover the standard aff...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.24108/preprints-3114186
-/

namespace Collatz.Papers.Journal_10_24108_preprints_3114186

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "FarhadAliabdali Aliabdali, \"Collatz Analysis Two Stage Tree and Multiset Calculus\", DOI:10.24108/preprints-3114186 [2026]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_24108_preprints_3114186
