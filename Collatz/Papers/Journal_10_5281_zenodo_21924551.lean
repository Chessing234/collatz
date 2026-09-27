import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for ABD ALMOMEN ALNEEL ADAM MOHAMED ALNEEL, "*The Siege Principle: A Finite Descent Proof of the Collatz Conjecture via Monotonic Potential Collapse", 2026.

Title: *The Siege Principle: A Finite Descent Proof of the Collatz Conjecture via Monotonic Potential Collapse

Abstract (from harvested metadata, truncated):
We present a complete proof of the Collatz Conjecture, also known as the 3n+1 problem. The proof is established through the "Siege Principle," a novel framework based on finite descent and monotonic potential collapse. We define a potential function $E_k = \ln(n_k)$ for the Collatz sequence. We prove that for any starting natural number $n_0$, the sequence must enter a finite transient phase, after which it is confined to a strictly decreasing chain of potential values. The core of the proof relies on two pillars. First, we establish the Odd Step Compression Lemma, which demonstrates that any odd term $n_{odd}$ is immediately mapped to an even term $3n_{odd}+1$, and subsequently divided by a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21924551
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21924551

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "ABD ALMOMEN ALNEEL ADAM MOHAMED ALNEEL, \"*The Siege Principle: A Finite Descent Proof of the Collatz Conjecture via Monotonic Potential Collapse\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21924551 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21924551
