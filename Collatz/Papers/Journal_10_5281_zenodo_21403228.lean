import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Griff gurwell, "The Transcript and the Comma The Collatz Conjecture Through the Unified Prime Lattice", 2026.

Title: The Transcript and the Comma The Collatz Conjecture Through the Unified Prime Lattice

Abstract (from harvested metadata, truncated):
The Collatz conjecture—that repeatedly applying “halve if even, triple‑plus‑one if odd” always reaches 1—has resisted proof for nearly a century. This paper shows that the Collatz map is natively described by the Prime Lattice Coherence Framework because it is built entirely from the framework’s own generators, 2 and 3. Three new theorems are proved: (A) every odd‑step output 3n+1 lands in the Hard Wall zone modulo 9; (B) every halving step flips the number’s zone between Hard Wall and Temporal; (C) the mod‑9 zone of each odd trajectory element is completely determined by the parity of the preceding run of halvings—the trajectory’s zone sequence is a direct transcript of its own 2‑adic valua...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21403228
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21403228

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Griff gurwell, \"The Transcript and the Comma The Collatz Conjecture Through the Unified Prime Lattice\", Zenodo, DOI:10.5281/zenodo.21403228 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21403228
