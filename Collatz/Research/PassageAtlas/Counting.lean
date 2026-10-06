import Collatz.Research.PassageAtlas.Horizon
import Collatz.Research.PassageAtlas.Census

namespace Collatz.Research.PassageAtlas
open PeriodicCounting StoppingAtlas

/-- Exact first-descent counting on the shifted positive window [2,N+2). -/
def actualEventB (k n : Nat) : Bool := decide
  (1 ≤ k ∧ acceleratedOrbit k (n + 2) < n + 2 ∧
    ∀ j : Fin k, 1 ≤ j.val → ¬ acceleratedOrbit j.val (n + 2) < n + 2)

/-- The computable bounded-prefix predicate is precisely exact stopping. -/
theorem actualEvent_spec (k n : Nat) : actualEventB k n = true ↔ stoppingTime (n + 2) k := by
  rw [actualEventB, decide_eq_true_eq]
  constructor
  · rintro ⟨hk, hd, hp⟩
    exact ⟨hk, hd, fun j hj hjk => hp ⟨j, hjk⟩ hj⟩
  · rintro ⟨hk, hd, hp⟩
    exact ⟨hk, hd, fun j hj => hp j.val hj j.isLt⟩

/-- Transfer the coefficient event to actual stopping throughout the new horizon. -/
theorem actualEvent_eq {k : Nat} (hk : k ≤ 2592) : actualEventB k = firstEventB k := by
  funext n
  apply Bool.eq_iff_iff.mpr
  rw [actualEvent_spec, firstEventB, decide_eq_true_eq]
  exact stopping_iff_firstLight_le_2592 (n := n + 2) (by omega) hk

/-- All finite-window coefficient counting identities now apply to actual stopping. -/
theorem actual_count_eq {k : Nat} (hk : k ≤ 2592) (N : Nat) :
    countBelow (actualEventB k) N = countBelow (firstEventB k) N := by
  rw [actualEvent_eq hk]

/-- Exact stopping events have a complete finite period-count decomposition. -/
theorem actual_count_div_mod {k : Nat} (hk : k ≤ 2592) (N : Nat) :
    countBelow (actualEventB k) N =
      (N / 2 ^ k) * countBelow (actualEventB k) (2 ^ k) +
        countBelow (actualEventB k) (N % 2 ^ k) := by
  rw [actualEvent_eq hk]
  exact firstEvent_count_div_mod k N

/-- The 173/32768 numerator describes actual exact stopping, not just coefficients. -/
theorem actual_period_fifteen : countBelow (actualEventB 15) 32768 = 173 := by
  rw [actual_count_eq (by decide)]
  exact period_count_fifteen

/-- Actual exact stopping at fifteen has a uniform error bound at arbitrary cutoffs. -/
theorem actual_depth_fifteen_error (N : Nat) :
    32768 * countBelow (actualEventB 15) N ≤ N * 173 + 5638935 ∧
    N * 173 ≤ 32768 * countBelow (actualEventB 15) N + 5638935 := by
  rw [actual_count_eq (by decide)]
  exact depth_fifteen_error N

/-- Natural density A/M using arbitrarily fine integer precision.
For q>0 and N>0 the two bounds give error at most 1/(q*M). -/
def HasRationalDensity (P : Nat → Bool) (A M : Nat) : Prop :=
  0 < M ∧ ∀ q : Nat, 0 < q → ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
    q * (M * countBelow P N) ≤ q * (N * A) + N ∧
    q * (N * A) ≤ q * (M * countBelow P N) + N

/-- A uniform finite discrepancy supplies a rational natural-density limit. -/
theorem rationalDensity_of_error (P : Nat → Bool) (A M E : Nat) (hM : 0 < M)
    (h : ∀ N, M * countBelow P N ≤ N * A + E ∧
      N * A ≤ M * countBelow P N + E) : HasRationalDensity P A M := by
  refine ⟨hM, ?_⟩
  intro q _
  refine ⟨q * E, ?_⟩
  intro N hN
  have hu := Nat.mul_le_mul_left q (h N).1
  have hl := Nat.mul_le_mul_left q (h N).2
  rw [Nat.mul_add] at hu hl
  constructor <;> omega

/-- Exact accelerated stopping at fifteen has rational natural density 173/32768. -/
theorem actual_density_fifteen : HasRationalDensity (actualEventB 15) 173 32768 :=
  rationalDensity_of_error _ _ _ 5638935 (by decide) actual_depth_fifteen_error

/-- Complete periods have exact counts, independent of the remainder estimate. -/
theorem actual_full_periods (q : Nat) :
    countBelow (actualEventB 15) (q * 32768) = q * 173 := by
  have h := count_mul_add (firstEventB 15) (2 ^ 15) q 0 (firstEvent_period 15)
  rw [period_count_fifteen, count_zero, Nat.add_zero, Nat.add_zero] at h
  rw [actualEvent_eq (by decide)]
  exact h

end Collatz.Research.PassageAtlas
