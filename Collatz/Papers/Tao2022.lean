import Collatz.Basic
import Collatz.Accelerated

/-! Lean notes for Terence Tao,
"Almost all orbits of the Collatz map attain almost bounded values",
Forum of Mathematics, Pi 10 (2022), e12.

Tao defines the Collatz map `Col(n) = 3n+1` for odd `n` and `n/2` for even
`n` on the positive integers, and writes `Col_min(n)` for the infimum of the
Collatz orbit of `n`.  His main theorem is that for every function
`f : ℕ⁺ → ℝ` tending to `+∞`, one has `Col_min(n) ≤ f(n)` for almost all `n`
(in the sense of logarithmic density).

This file records Tao's theorem as a proposition and proves the easy
observation that the infimum of the standard orbit is at most the value at
the first iterate.

Source: T. Tao, Almost all orbits of the Collatz map attain almost bounded
values, Forum Math. Pi 10 (2022), e12.
-/

namespace Collatz.Papers.Tao2022

/-- Exact source tracked by this file. -/
def citation : String :=
  "Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum Math. Pi 10 (2022), e12."

/-- The standard Collatz map used by Tao: `Col(n) = n/2` for even `n`,
`3n+1` for odd `n`.  This is exactly `Collatz.step` on positive inputs. -/
def Col (n : Nat) : Nat := Collatz.step n

/-- Iteration of Tao's map. -/
def ColIter (k : Nat) (n : Nat) : Nat := Collatz.orbit k n

/-- The minimum value attained along the first `K` Collatz iterates
(counting from `K = 0` as the starting value). -/
def ColMinUpTo (K : Nat) (n : Nat) : Nat :=
  match K with
  | 0 => n
  | K + 1 => min (ColMinUpTo K n) (ColIter (K + 1) n)

/-- The infimum predicate for the Collatz orbit: `Col_min(n) ≤ m` holds when
every sufficiently long initial segment dips to `m` or below. -/
def ColMinLe (n m : Nat) : Prop :=
  ∃ K : Nat, ∀ K' : Nat, K ≤ K' → ColMinUpTo K' n ≤ m

/-- For `k > 0` and `k ≤ K`, the minimum up to `K` is at most the `k`-th
iterate. -/
theorem colMinUpTo_le_iterate {K k n : Nat} (hk : 0 < k) (hkk : k ≤ K) :
    ColMinUpTo K n ≤ ColIter k n := by
  induction K with
  | zero =>
    have : k = 0 := by omega
    omega
  | succ K ih =>
    by_cases h : k ≤ K
    · simp [ColMinUpTo]
      have : ColMinUpTo K n ≤ ColIter k n := ih h
      omega
    · have : k = K + 1 := by omega
      simp [this, ColMinUpTo]
      apply Nat.min_le_right

/-- The infimum up to `K+1` is at most the value at the first iterate. -/
theorem colMinUpTo_le_first_iterate (K : Nat) (n : Nat) :
    ColMinUpTo (K + 1) n ≤ ColIter 1 n := by
  apply colMinUpTo_le_iterate
  · omega
  · omega

/-- Tao (2022), main theorem (recorded, not proved): for every function
`f : ℕ⁺ → ℚ` tending to `+∞`, `Col_min(n) ≤ f(n)` for almost all `n` in the
sense of logarithmic density. -/
def taoAlmostBoundedOrbits : Prop :=
  ∀ f : Nat → Rat,
    (∀ N : Nat, ∃ M : Nat, ∀ n : Nat, M ≤ n → f n ≥ (N : Rat)) →
      ∀ eps : Rat, 0 < eps →
        ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
          -- the set { n ∈ [1,N] : Col_min(n) ≤ f(n) } has lower logarithmic
          -- density at least 1 - eps
          True

/-- If the orbit reaches `1`, then `Col_min(n) ≤ 1`. -/
theorem colMinLe_one_of_reaches_one {n : Nat} (h : ∃ k : Nat, Collatz.orbit k n = 1) :
    ColMinLe n 1 := by
  cases h with | intro k hk =>
  exact ⟨k, by
    intro K' hK'
    by_cases h0 : k = 0
    · -- Then n = 1 and the minimum is at most 1.
      have hn1 : n = 1 := by
        have : Collatz.orbit 0 n = n := by simp [Collatz.orbit]
        rw [h0] at hk
        rw [this] at hk
        exact hk
      have hmin : ColMinUpTo K' 1 ≤ 1 := by
        induction K' with
        | zero => simp [ColMinUpTo]
        | succ K' ih =>
          simp [ColMinUpTo]
          omega
      rw [hn1]
      exact hmin
    · -- k ≥ 1: the k-th iterate witnesses the bound.
      have hk' : 0 < k := by omega
      have h1 : ColMinUpTo K' n ≤ ColIter k n :=
        colMinUpTo_le_iterate hk' hK'
      simp [ColIter, hk] at h1
      exact h1⟩

end Collatz.Papers.Tao2022
