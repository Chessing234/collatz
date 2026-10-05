import Collatz.Exploration.TimeChange

/-!
# First descent is preserved by the explicit Collatz time change

An arbitrary descent witness only yields inequalities between step counts.
A *first* descent witness gives an exact correspondence. The omitted odd
expansion cannot be a first descent, since its retained predecessor is smaller.
Thus the first standard descent time is exactly `clock n j`, where `j` is the
first accelerated descent time. The endpoint values also agree.

This is a conditional identity of stopping times, not an assertion that either
stopping time exists for every positive integer.
-/
namespace Collatz.Exploration.FirstDescent

open TimeChange

/-- Strict descent at `k`, with every earlier standard value at least `n`. -/
def FirstStandard (n k : Nat) : Prop :=
  orbit k n < n ∧ ∀ i, i < k → n ≤ orbit i n

/-- Strict descent at `j`, with every earlier accelerated value at least `n`. -/
def FirstAccelerated (n j : Nat) : Prop :=
  acceleratedOrbit j n < n ∧ ∀ i, i < j → n ≤ acceleratedOrbit i n

/-- The clock preserves the order of accelerated indices. -/
theorem clock_mono (n : Nat) {a b : Nat} (hab : a ≤ b) :
    clock n a ≤ clock n b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases he : a = b+1
    · subst a; exact Nat.le_refl _
    · have hprev := ih (by omega)
      have := clock_lt_succ n b
      omega

/-- Positive clock increments make this time change strictly increasing. -/
theorem clock_strict (n : Nat) {a b : Nat} (hab : a < b) :
    clock n a < clock n b := by
  have hfirst := clock_lt_succ n a
  have hlast := clock_mono n (a := a+1) (b := b) (by omega)
  omega

/-- A smaller standard boundary time must have a smaller accelerated index. -/
theorem index_lt_of_clock_lt {n a b : Nat} (h : clock n a < clock n b) : a < b := by
  by_cases hab : a < b
  · exact hab
  · have := clock_mono n (a := b) (b := a) (by omega)
    omega

/-- An accelerated first drop becomes a standard first drop at its clock time. -/
theorem standard_first_of_accelerated {n j : Nat}
    (hj : FirstAccelerated n j) : FirstStandard n (clock n j) := by
  refine ⟨by rw [orbit_at_clock]; exact hj.1, ?_⟩
  intro k hk
  obtain ⟨i, hi | hi⟩ := clock_cover n k
  · have hit : clock n i < clock n j := by omega
    have hil := index_lt_of_clock_lt hit
    rw [hi.2]
    exact hj.2 i hil
  · have hit : clock n i < clock n j := by omega
    have hil := index_lt_of_clock_lt hit
    rw [hi.2.2]
    have := hj.2 i hil
    omega

/-- A standard first drop occurs at a boundary and is accelerated-first too. -/
theorem accelerated_first_of_standard {n k : Nat}
    (hk : FirstStandard n k) :
    ∃ j, k = clock n j ∧ FirstAccelerated n j := by
  obtain ⟨j, hj | hj⟩ := clock_cover n k
  · refine ⟨j, hj.1, ?_, ?_⟩
    · rw [← hj.2]
      exact hk.1
    · intro i hi
      have hit : clock n i < k := by rw [hj.1]; exact clock_strict n hi
      have hmin := hk.2 (clock n i) hit
      rw [orbit_at_clock] at hmin
      exact hmin
  · have hmin := hk.2 (clock n j) (by omega)
    rw [orbit_at_clock] at hmin
    have hdrop := hk.1
    rw [hj.2.2] at hdrop
    omega

/-- Exact stopping-time translation, expressed without partial functions. -/
theorem first_standard_iff (n k : Nat) :
    FirstStandard n k ↔ ∃ j, k = clock n j ∧ FirstAccelerated n j := by
  constructor
  · exact accelerated_first_of_standard
  · rintro ⟨j, rfl, hj⟩
    exact standard_first_of_accelerated hj

/-- The first descent endpoint agrees under both conventions. -/
theorem first_endpoint {n k j : Nat} (ht : k = clock n j) :
    orbit k n = acceleratedOrbit j n := by
  rw [ht, orbit_at_clock]

/-- A first standard drop is never the odd expansion between clock boundaries. -/
theorem first_not_omitted {n k j : Nat} (hk : FirstStandard n k)
    (ht : k = clock n j+1) (ho : acceleratedOrbit j n % 2 = 1) : False := by
  have hmin := hk.2 (clock n j) (by omega)
  rw [orbit_at_clock] at hmin
  have hdrop := hk.1
  rw [ht, orbit_inside_odd ho] at hdrop
  omega

/-- A descent time cannot be zero in either convention. -/
theorem first_times_positive {n k j : Nat}
    (hk : FirstStandard n k) (hj : FirstAccelerated n j) : 0 < k ∧ 0 < j := by
  have hs := hk.1
  have ha := hj.1
  constructor
  · by_cases he : k = 0
    · rw [he, orbit_zero_steps] at hs; omega
    · omega
  · by_cases he : j = 0
    · rw [he, acceleratedOrbit_zero] at ha; omega
    · omega

/-- First standard descent times obey the same factor-two clock bounds. -/
theorem first_time_bounds {n k : Nat} (hk : FirstStandard n k) :
    ∃ j, FirstAccelerated n j ∧ j ≤ k ∧ k ≤ 2*j := by
  obtain ⟨j, ht, hj⟩ := accelerated_first_of_standard hk
  obtain ⟨hlo, hhi⟩ := clock_bounds n j
  exact ⟨j, hj, by omega, by omega⟩

/-- A trajectory has at most one first standard descent time. -/
theorem standard_unique {n a b : Nat}
    (ha : FirstStandard n a) (hb : FirstStandard n b) : a = b := by
  by_cases hab : a < b
  · have := hb.2 a hab
    have := ha.1
    omega
  · by_cases hba : b < a
    · have := ha.2 b hba
      have := hb.1
      omega
    · omega

/-- A trajectory has at most one first accelerated descent time. -/
theorem accelerated_unique {n a b : Nat}
    (ha : FirstAccelerated n a) (hb : FirstAccelerated n b) : a = b := by
  by_cases hab : a < b
  · have := hb.2 a hab
    have := ha.1
    omega
  · by_cases hba : b < a
    · have := ha.2 b hba
      have := hb.1
      omega
    · omega

/-- Existence of an arbitrary standard drop supplies a first drop. -/
theorem standard_first_exists {n : Nat} (h : ∃ k, orbit k n < n) :
    ∃ k, FirstStandard n k := by
  obtain ⟨k, hk, hmin⟩ := Minimum.exists_min h
  refine ⟨k, hk, ?_⟩
  intro i hi
  have := hmin i hi
  omega

/-- Existence of an arbitrary accelerated drop supplies a first drop. -/
theorem accelerated_first_exists {n : Nat}
    (h : ∃ k, acceleratedOrbit k n < n) : ∃ k, FirstAccelerated n k := by
  obtain ⟨k, hk, hmin⟩ := Minimum.exists_min h
  refine ⟨k, hk, ?_⟩
  intro i hi
  have := hmin i hi
  omega

/-- Existence, unlike the numerical clock value, is convention independent. -/
theorem first_exists_iff (n : Nat) :
    (∃ k, FirstStandard n k) ↔ (∃ j, FirstAccelerated n j) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, _, hj⟩ := accelerated_first_of_standard hk
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨clock n j, standard_first_of_accelerated hj⟩

end Collatz.Exploration.FirstDescent
