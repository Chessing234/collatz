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

/-- Harmonic weight of a set of positive integers up to N. This is a
mathematical definition using classical membership, not an orbit-search
algorithm with a time cutoff. -/
noncomputable def harmonicMass (P : Nat → Prop) (N : Nat) : Rat := by
  classical
  exact ((List.range N).map fun k =>
    if P (k+1) then (1 : Rat) / ((k+1 : Nat) : Rat) else 0).sum

/-- Logarithmic density one, normalized by the full harmonic sum.
Only positive integers are counted, so division by zero is absent. -/
def LogDensityOne (P : Nat → Prop) : Prop :=
  ∀ eps : Rat, 0 < eps → ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
    (1-eps) * harmonicMass (fun _ => True) N ≤ harmonicMass P N

/-- The orbit has an iterate below a rational bound. The quantifier is
unbounded: replacing it by a search to depth N would be a different statement. -/
def OrbitBelow (n : Nat) (bound : Rat) : Prop :=
  ∃ k : Nat, (ColIter k n : Rat) ≤ bound

/-- Tao's almost-bounded conclusion restricted to rational-valued growth
functions, recorded as a proposition, NOT proved here. The density is
logarithmic, not natural, and the bound must tend to infinity.

Earlier versions ended in True and therefore did not encode the claimed
conclusion. This definition uses the actual orbit predicate and harmonic
weights. No theorem in this module asserts this proposition. -/
def taoAlmostBoundedOrbits : Prop :=
  ∀ f : Nat → Rat,
    (∀ N : Nat, ∃ M : Nat, ∀ n : Nat, M ≤ n → f n ≥ (N : Rat)) →
      LogDensityOne (fun n => OrbitBelow n (f n))

/-- Empty cutoffs have zero mass. -/
theorem harmonicMass_zero (P : Nat → Prop) : harmonicMass P 0 = 0 := by
  simp [harmonicMass]

/-- The empty set has zero mass for every cutoff. -/
theorem harmonicMass_empty (N : Nat) : harmonicMass (fun _ => False) N = 0 := by
  induction N with
  | zero => simp [harmonicMass]
  | succ N ih =>
    simpa [harmonicMass, List.range_succ, List.map_append, List.sum_append, Rat.add_zero] using ih

/-- Singleton cutoff tests the actual set membership at the positive input 1. -/
theorem harmonicMass_one (P : Nat → Prop) [Decidable (P 1)] :
    harmonicMass P 1 = (if P 1 then 1 else 0) := by
  classical
  simp [harmonicMass, List.range_succ, Rat.add_zero, Rat.zero_add, show (1 : Rat) / 1 = 1 by exact Rat.mul_inv_cancel 1 (by decide)]

/-- Reaching one supplies an orbit-bound witness whenever the bound is at least one. -/
theorem orbitBelow_of_reaches_one {n : Nat} {bound : Rat}
    (h : ∃ k : Nat, Collatz.orbit k n = 1) (hb : 1 ≤ bound) : OrbitBelow n bound := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  simpa [ColIter, hk] using hb

/-- An orbit-bound witness above the starting value needs no iteration. -/
theorem orbitBelow_of_start_le {n : Nat} {bound : Rat} (h : (n : Rat) ≤ bound) :
    OrbitBelow n bound := ⟨0, h⟩

/-- The orbit predicate has content: no positive orbit reaches a value at most zero. -/
theorem not_orbitBelow_zero {n : Nat} (hn : 0 < n) : ¬ OrbitBelow n 0 := by
  intro ⟨k, hk⟩
  have hp : 0 < ColIter k n := Collatz.orbit_positive hn k
  have hc : (ColIter k n : Rat) ≤ (0 : Nat) := hk
  have hz := Rat.natCast_le_natCast.mp hc
  omega

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
