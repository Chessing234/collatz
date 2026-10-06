import Collatz.Strategy.FirstDescentResidue

/-!
# First descent is a controlled-scale landing

First descent always arrives in `[n/2,n)`, because the last step is a halving
and its input has not yet gone below n. This does not imply that a uniform
number of steps reaches that interval. The existence of a first descent
remains a premise in the general theorems here.
-/

namespace Collatz.FirstDescentResidue

/-- Every state before a first descent is at least the original input. -/
theorem before_first_descent {n k : Nat} (hk : stoppingTime n k)
    (j : Nat) (hj : j < k) : n ≤ acceleratedOrbit j n := by
  by_cases hj0 : j = 0
  · subst j
    simp
  · have h := hk.2.2 j (by omega) hj
    omega

/-- The first-descent endpoint lies between half the input and the input. -/
theorem landing_scale {n k : Nat} (hk : stoppingTime n (k + 1)) :
    n ≤ 2 * acceleratedOrbit (k + 1) n ∧ acceleratedOrbit (k + 1) n < n := by
  have he := last_state_even hk
  have hb := before_first_descent hk k (by omega)
  have hstep : acceleratedOrbit (k + 1) n = acceleratedOrbit k n / 2 := by
    rw [acceleratedOrbit_succ_step]
    simp only [acceleratedStep, if_pos he]
  have hprev : acceleratedOrbit k n = 2 * acceleratedOrbit (k + 1) n := by
    rw [hstep]
    omega
  exact ⟨by omega, hk.2.1⟩

/-- The scale bound stated for any valid stopping index. -/
theorem landing_scale_general {n k : Nat} (hk : stoppingTime n k) :
    n ≤ 2 * acceleratedOrbit k n ∧ acceleratedOrbit k n < n := by
  obtain ⟨j, hj⟩ : ∃ j : Nat, k = j + 1 := ⟨k - 1, by have := hk.1; omega⟩
  rw [hj] at hk ⊢
  exact landing_scale hk

/-- For odd starting values the first-descent endpoint is strictly above half. -/
theorem odd_landing_above_half {n k : Nat} (hn : n % 2 = 1)
    (hk : stoppingTime n k) : n < 2 * acceleratedOrbit k n := by
  have hb := (landing_scale_general hk).1
  omega

/-- An even starting value lands at exactly half its original value. -/
theorem even_landing_exact_half {n k : Nat} (hn : 0 < n) (he : n % 2 = 0)
    (hk : stoppingTime n k) : 2 * acceleratedOrbit k n = n := by
  have hk1 := stoppingTime_unique hk (stoppingTime_of_even hn he)
  rw [hk1]
  simp only [acceleratedOrbit_succ, acceleratedOrbit_zero, acceleratedStep, if_pos he]
  omega

/-- The halving lower bound is attained precisely by even initial values. -/
theorem landing_at_half_iff_even {n k : Nat} (hn : 0 < n) (hk : stoppingTime n k) :
    2 * acceleratedOrbit k n = n ↔ n % 2 = 0 := by
  constructor
  · intro h
    omega
  · exact fun he => even_landing_exact_half hn he hk

/-- All first-descent endpoints from a positive input stay positive. -/
theorem landing_positive {n k : Nat} (hn : 0 < n) (hk : stoppingTime n k) :
    0 < acceleratedOrbit k n := by
  have hb := (landing_scale_general hk).1
  omega

/-- The first-descent landing cannot lie below a prescribed half-scale target. -/
theorem no_landing_below_half_target {n k m : Nat} (hk : stoppingTime n k)
    (hm : 2 * m ≤ n) : ¬ acceleratedOrbit k n < m := by
  have hb := (landing_scale_general hk).1
  omega

/-- The interval from n to half of n cannot be skipped by first descent. -/
theorem target_crossing_requires_later_steps {n k m : Nat}
    (hk : stoppingTime n k) (hm : 2 * m ≤ n) : m ≤ acceleratedOrbit k n := by
  have hb := (landing_scale_general hk).1
  omega

end Collatz.FirstDescentResidue
