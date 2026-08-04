import Collatz.Basic
import Collatz.Accelerated

/-! Lean notes for Jeffrey C. Lagarias,
"The 3x+1 problem and its generalizations",
The American Mathematical Monthly 92 (1985), 3--23.

Lagarias's survey gives the standard `3x+1` map `C(n) = n/2` for even `n`
and `3n+1` for odd `n`, the accelerated map `T(n) = n/2` for even `n` and
`(3n+1)/2` for odd `n`, and the stopping-time formulation.  It records the
standard equivalences between these formulations.

This file proves the elementary one-step expansion facts and records the
main open conjectures and their equivalences as propositions.

Source: J. C. Lagarias, The 3x+1 problem and its generalizations,
Amer. Math. Monthly 92 (1985), 3--23.
-/

namespace Collatz.Papers.Lagarias1985

/-- Exact source tracked by this file. -/
def citation : String :=
  "Jeffrey C. Lagarias, The 3x+1 problem and its generalizations, Amer. Math. Monthly 92 (1985), 3--23."

/-- The standard Collatz conjecture: every positive orbit under `Collatz.step`
reaches `1`. -/
def standardCollatzConjecture : Prop :=
  ∀ n : Nat, n > 0 → ∃ k : Nat, Collatz.orbit k n = 1

/-- The accelerated Collatz conjecture: every integer `n > 1` has an
accelerated orbit that reaches `1`. -/
def acceleratedCollatzConjecture : Prop :=
  ∀ n : Nat, n > 1 → ∃ k : Nat, Collatz.acceleratedOrbit k n = 1

/-- On a positive even input, one accelerated step equals one standard step. -/
theorem acceleratedStep_even {n : Nat} (_hn : n > 0) (heven : n % 2 = 0) :
    Collatz.acceleratedStep n = Collatz.orbit 1 n := by
  have hn0 : n ≠ 0 := by omega
  have h1 : Collatz.step n = n / 2 := by
    simp [Collatz.step, heven, hn0]
  simp [Collatz.acceleratedStep, heven, Collatz.orbit, h1]

/-- On a positive odd input, one accelerated step equals two standard steps. -/
theorem acceleratedStep_odd {n : Nat} (_hn : n > 0) (hodd : n % 2 = 1) :
    Collatz.acceleratedStep n = Collatz.orbit 2 n := by
  have hn0 : n ≠ 0 := by omega
  have h1 : Collatz.step n = 3 * n + 1 := by
    simp [Collatz.step, hodd, hn0]
  have h2 : Collatz.step (3 * n + 1) = (3 * n + 1) / 2 := by
    have : (3 * n + 1) % 2 = 0 := by omega
    simp [Collatz.step, this]
  simp [Collatz.acceleratedStep, hodd, Collatz.orbit, h1, h2]

/-- The accelerated orbit of a positive input embeds into the standard orbit:
for every `k` there is a positive `M` such that `T^k(n) = C^M(n)`. -/
def acceleratedOrbit_embeds_in_standard : Prop :=
  ∀ n : Nat, n > 0 → ∀ k : Nat, ∃ M : Nat,
    Collatz.acceleratedOrbit k n = Collatz.orbit M n

/-- If the accelerated orbit reaches `1`, then the standard orbit reaches `1`.
This is the easy direction of the equivalence between the two conjectures. -/
def accelerated_reaches_one_implies_standard : Prop :=
  ∀ n : Nat, n > 0 →
    (∃ k : Nat, Collatz.acceleratedOrbit k n = 1) →
      ∃ k : Nat, Collatz.orbit k n = 1

/-- The standard and accelerated Collatz conjectures are equivalent.
Recorded as a proposition; a full formal proof requires the indexing argument
that extracts an accelerated orbit from a standard orbit. -/
def collatzConjecturesEquivalent : Prop :=
  standardCollatzConjecture ↔ acceleratedCollatzConjecture

/-- Stopping-time formulation: the conjecture is equivalent to the statement
that every `n > 1` has a finite stopping time under the accelerated map.
The forward direction is proved; the converse is recorded. -/
theorem reaches_one_of_finite_stopping_time {n : Nat} (_hn : 1 < n)
    (h : Collatz.hasFiniteStoppingTime n)
    (H : ∀ m : Nat, m < n → ∃ k : Nat, Collatz.acceleratedOrbit k m = 1) :
    ∃ k : Nat, Collatz.acceleratedOrbit k n = 1 := by
  cases h with | intro j h =>
  cases h with | intro hj1 hj =>
  have hH := H (Collatz.acceleratedOrbit j n) hj
  cases hH with | intro k hk =>
  have hjk : Collatz.acceleratedOrbit (j + k) n
      = Collatz.acceleratedOrbit k (Collatz.acceleratedOrbit j n) := by
    rw [Collatz.acceleratedOrbit_add k j n]
    rw [Nat.add_comm]
  exact ⟨j + k, by rw [hjk, hk]⟩

/-- The converse of `reaches_one_of_finite_stopping_time`: if every `n > 1`
has a finite accelerated orbit, then every `n > 1` has a finite stopping
time.  Recorded as a proposition. -/
def finiteStoppingTimeOfReachesOne : Prop :=
  ∀ n : Nat, 1 < n →
    (∃ k : Nat, Collatz.acceleratedOrbit k n = 1) →
      Collatz.hasFiniteStoppingTime n

end Collatz.Papers.Lagarias1985
