import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Clifford Keeble, "Negative Feedback: The Collatz Conjecture as a Discrete Control System", 2026.

Title: Negative Feedback: The Collatz Conjecture as a Discrete Control System

Abstract (from harvested metadata, truncated):
The Collatz conjecture is reframed as a discrete feedback control problem. The plant is the set of odd positive integers; the controller is the Syracuse map T(n) = (3n + 1)/2^k; the reference signal is the constant 1; and the feedback element is the +1 operation. The sign of this feedback — positive or negative — is shown to determine convergence completely. Negative feedback (3n + 1) routes every expansion class (S3) unconditionally into contraction classes (S5, S1), constituting a one-step error correction at every Syracuse iteration. Positive feedback (3n − 1) routes contraction classes back into expansion, producing the known cycles of that system. The Lyapunov function V = n/2^(Σk), proved strictly decreasing at every step, provides the formal stability certificate: no non-trivial...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18976342
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18976342

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Clifford Keeble, \"Negative Feedback: The Collatz Conjecture as a Discrete Control System\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18976342 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18976342
