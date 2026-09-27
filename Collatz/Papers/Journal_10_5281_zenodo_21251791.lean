import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Николай Архипов, "« The Collatz Conjecture: Final Proof through Parabolic Cascade and Lyapunov Contraction»", 2026.

Title: « The Collatz Conjecture: Final Proof through Parabolic Cascade and Lyapunov Contraction»

Abstract (from harvested metadata, truncated):
This paper presents a complete proof of the Collatz conjecture (the 3n+1 problem), based on its structural model: regular quadruples, their interlocking (overlap), and the universal governing equation 3x²−4x−4=0 with roots 2 and −2/3. The proof rests on three key elements: (1) the telescopic product of constant terms of interlocked parabolas, (2) the negative Lyapunov exponent λ ≈ −0.288, which guarantees global contraction of the system, (3) a proof by contradiction that excludes the existence of other closed cycles through the mutual primality of powers of two and three. This work completes Arkhipov's 2026 research program and puts an end to a problem that has remained open since 1937.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21251791
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21251791

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Николай Архипов, \"« The Collatz Conjecture: Final Proof through Parabolic Cascade and Lyapunov Contraction»\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21251791 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_21251791
