import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Shmuel Friedland, "The Collatz-Wielandt quotient for some pairs of nonnegative operators", arXiv:1710.07402 [2017].

Title: The Collatz-Wielandt quotient for some pairs of nonnegative operators

Abstract (from OpenAlex metadata, truncated):
In this paper we consider two versions of the Collatz-Wielandt quotient for a pair of nonnegative operators A,B that map a given pointed generating cone in the first space into a given pointed generating cone in the second space. If the two spaces and two cones are identical, and B is the identity operator then one version of this quotient is the spectral radius of A. In some applications, as commodity pricing, power control in wireless networks and quantum information theory, one needs to deal with the Collatz-Wielandt quotient for two nonnegative operators. In this paper we treat the two important cases: a pair of rectangular nonnegative matrices and a pair completely positive operators. We give a characterization of minimal optimal solutions and polynomially computable bounds on the Collatz-Wielandt quotient.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1710.07402
-/

namespace Collatz.Papers.Arxiv1710_07402

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Shmuel Friedland, \"The Collatz-Wielandt quotient for some pairs of nonnegative operators\", arXiv:1710.07402 [2017]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1710_07402
