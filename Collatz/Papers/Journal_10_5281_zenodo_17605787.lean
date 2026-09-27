import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Matsuura, Yoshihito, "A Finite–Depth Structural Resolution of the Collatz Dynamics via Hierarchical Height Functions and Mother Chains", 2025.

Title: A Finite–Depth Structural Resolution of the Collatz Dynamics via Hierarchical Height Functions and Mother Chains

Abstract (from harvested metadata, truncated):
This preprint presents a finite–depth structural resolution of the Collatz dynamics. Two independent descent mechanisms are established: A hierarchical height function H(n) satisfying the monotonicity propertyH(T(n)) \le H(n), together with a formally proved finiteness of each levelset C(M)=\{n:H(n)=M\} via an injective reconstruction lemma. The Mother Chain framework, an inverse structural system defined for allodd integers, supported by a formal residue–3 lemma and producing strictlydecreasing sequences under the mother map. Both descent mechanisms are well-founded and independent. Their combination forces termination of every Collatz orbit, yielding a complete finite–depth structural proof of convergence. A companion Coq kernel formalizing the core components of the proof is published...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17605787
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17605787

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Matsuura, Yoshihito, \"A Finite–Depth Structural Resolution of the Collatz Dynamics via Hierarchical Height Functions and Mother Chains\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17605787 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17605787
