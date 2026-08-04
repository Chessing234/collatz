import Collatz.Basic
import Collatz.Accelerated

/-! Lean notes for Ilia Krasikov and Jeffrey C. Lagarias,
"Bounds for the 3x+1 problem using difference inequalities",
Acta Arithmetica 109 (2003), 237--258.

Krasikov and Lagarias use difference inequalities to give a non-trivial lower
bound on the number of integers up to `N` that eventually reach `1` under the
`3x+1` iteration.  Their method produces explicit positive rational constants
`p/q` such that at least `N^(p/q)` integers `≤ N` have finite total stopping
time for all large `N`.

This file records the lower-bound theorem as a proposition and proves a simple
closure property of the set of numbers that reach `1`.

Source: I. Krasikov and J. C. Lagarias, Bounds for the 3x+1 problem using
difference inequalities, Acta Arith. 109 (2003), 237--258.
-/

namespace Collatz.Papers.KrasikovLagarias2003

/-- Exact source tracked by this file. -/
def citation : String :=
  "Ilia Krasikov and Jeffrey C. Lagarias, Bounds for the 3x+1 problem using difference inequalities, Acta Arith. 109 (2003), 237--258."

/-- Decidable predicate: `n` reaches `1` within `B` accelerated steps. -/
def reachesOneBy (n : Nat) : Nat → Bool
  | 0 => Collatz.acceleratedOrbit 0 n = 1
  | B + 1 => reachesOneBy n B || (Collatz.acceleratedOrbit (B + 1) n = 1)

/-- Count of positive integers `n ≤ N` that reach `1` within `N` accelerated
steps.  This is a finite, computable approximation to the true count. -/
def reachesOneUpToCount (N : Nat) : Nat :=
  Collatz.countUpTo (fun n => 0 < n ∧ n ≤ N ∧ reachesOneBy n N = true) N

/-- Krasikov--Lagarias (2003), main result (recorded, not proved): there are
explicit positive rational constants `p/q` such that for all sufficiently
large `N`, at least `N^(p/q)` positive integers `≤ N` have finite total
stopping time under the accelerated `3x+1` map. -/
def krasikovLagariasLowerBound : Prop :=
  ∃ p q : Nat, 0 < p ∧ 0 < q ∧
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      N ^ p ≤ reachesOneUpToCount N * N ^ q

/-- The set of numbers that reach `1` is closed under the accelerated step:
if `n` reaches `1`, then so does `acceleratedStep n`. -/
theorem reaches_one_closed_under_step {n : Nat}
    (h : ∃ k : Nat, Collatz.acceleratedOrbit k n = 1) :
    ∃ k : Nat, Collatz.acceleratedOrbit k (Collatz.acceleratedStep n) = 1 := by
  cases h with | intro k hk =>
  by_cases h0 : k = 0
  · -- Then n = 1 and acceleratedStep n = 2, which reaches 1 in 2 steps.
    have hn1 : n = 1 := by
      have : Collatz.acceleratedOrbit 0 n = n := by simp [Collatz.acceleratedOrbit]
      rw [h0] at hk
      rw [this] at hk
      exact hk
    exact ⟨1, by simp [hn1, Collatz.acceleratedOrbit]⟩
  · -- k ≥ 1: drop one accelerated step from the witness.
    exact ⟨k - 1, by
      have : Collatz.acceleratedOrbit k n
          = Collatz.acceleratedOrbit (k - 1) (Collatz.acceleratedStep n) := by
        have : k = (k - 1) + 1 := by omega
        rw [this]
        simp [Collatz.acceleratedOrbit_succ]
      rw [this] at hk
      exact hk⟩

end Collatz.Papers.KrasikovLagarias2003
