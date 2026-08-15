import Collatz.Structure.OrbitMinSieve

/-!
# Forced steps at the lower bound

`OrbitMin.three_mul_le_five_mul` gives `3(k−1) ≤ 5·a(m,k)` for the orbit minimum
of a counterexample, i.e.

`a(m,k) ≥ ⌈3(k−1)/5⌉ =: ℓ(k)`.

The bound `ℓ` increases at three out of every five scales.  Since the odd-step
count grows by at most one per step —

`a(m,k+1) = a(m,k) + (T^k(m) mod 2)`

— a scale where `a(m,k)` sits *exactly* at `ℓ(k)` and `ℓ` increments leaves no
slack: the next step **must** be an odd step.

**If `a(m,k) = ℓ(k)` and `ℓ(k+1) > ℓ(k)`, then `T^k(m)` is odd.**

So the orbit minimum cannot linger at its lower bound and then halve; every time
it is tight, the dynamics are forced.  This is the first constraint in the
project on *which* steps a counterexample takes, rather than on how many.
-/

namespace Collatz
namespace ForcedSteps

open Reach Congruence AccCycle OrbitMin

/-! ## The lower bound function -/

/-- `oddLower k = ⌈3(k−1)/5⌉`, the least odd-step count compatible with
heaviness at scale `k`. -/
def oddLower (k : Nat) : Nat := (3 * (k - 1) + 4) / 5

/-- The orbit minimum's odd-step count is at least `oddLower k`. -/
theorem oddLower_le {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat} (hk : 2 ^ k ≤ m) :
    oddLower k ≤ oddCount m k := by
  have hbound := three_mul_le_five_mul hn hm hmin hk
  rw [oddLower]
  omega

/-- The bound increments at three of every five scales. -/
theorem oddLower_succ_cases (k : Nat) :
    oddLower (k + 1) = oddLower k ∨ oddLower (k + 1) = oddLower k + 1 := by
  rw [oddLower, oddLower]
  omega

/-! ## The forcing lemma -/

/-- **A tight scale forces an odd step.**  If the odd-step count is exactly at
its lower bound at scale `k`, and the bound increases at `k+1`, then the step
taken at time `k` must be an odd step. -/
theorem step_forced_odd {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat}
    (hk : 2 ^ (k + 1) ≤ m)
    (htight : oddCount m k = oddLower k)
    (hjump : oddLower k < oddLower (k + 1)) :
    acceleratedOrbit k m % 2 = 1 := by
  have hnext : oddLower (k + 1) ≤ oddCount m (k + 1) := oddLower_le hn hm hmin hk
  have hstep : oddCount m (k + 1) = oddCount m k + acceleratedOrbit k m % 2 :=
    Density.oddCount_succ_last m k
  have hpar := Arith.mod_two_eq_zero_or_one (acceleratedOrbit k m)
  omega

/-- Contrapositive: a halving step at time `k` forces slack at scale `k`. -/
theorem slack_of_even_step {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat}
    (hk : 2 ^ (k + 1) ≤ m)
    (heven : acceleratedOrbit k m % 2 = 0)
    (hjump : oddLower k < oddLower (k + 1)) :
    oddLower k < oddCount m k := by
  have hkk : (2:Nat) ^ k ≤ m := Nat.le_trans (Arith.two_pow_le_two_pow (by omega)) hk
  have hlow : oddLower k ≤ oddCount m k := oddLower_le hn hm hmin hkk
  by_cases htight : oddCount m k = oddLower k
  · exfalso
    have hodd := step_forced_odd hn hm hmin hk htight hjump
    omega
  · omega

/-! ## Concrete forced scales

The bound jumps at `k = 2, 3, 5, 7, 8, 10, …`; at each of those a tight count
forces an odd step. -/

theorem jump_two : oddLower 1 < oddLower 2 := by decide
theorem jump_three : oddLower 2 < oddLower 3 := by decide
theorem jump_five : oddLower 4 < oddLower 5 := by decide
theorem jump_seven : oddLower 6 < oddLower 7 := by decide
theorem jump_eight : oddLower 7 < oddLower 8 := by decide
theorem jump_ten : oddLower 9 < oddLower 10 := by decide

/-- At scale `7`, a tight odd-step count forces the seventh step to be odd. -/
theorem forced_at_seven {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hk : 2 ^ 7 ≤ m)
    (htight : oddCount m 6 = oddLower 6) :
    acceleratedOrbit 6 m % 2 = 1 :=
  step_forced_odd hn hm hmin hk htight jump_seven

/-- At scale `10`, likewise. -/
theorem forced_at_ten {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hk : 2 ^ 10 ≤ m)
    (htight : oddCount m 9 = oddLower 9) :
    acceleratedOrbit 9 m % 2 = 1 :=
  step_forced_odd hn hm hmin hk htight jump_ten

/-! ## Two tight scales in a row -/

/-- **Consecutive tight scales force consecutive odd steps.**  If the count is
tight at `k` and again at `k+1`, and the bound jumps at both, then both steps
are odd. -/
theorem two_forced {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat}
    (hk : 2 ^ (k + 2) ≤ m)
    (ht1 : oddCount m k = oddLower k) (ht2 : oddCount m (k + 1) = oddLower (k + 1))
    (hj1 : oddLower k < oddLower (k + 1)) (hj2 : oddLower (k + 1) < oddLower (k + 2)) :
    acceleratedOrbit k m % 2 = 1 ∧ acceleratedOrbit (k + 1) m % 2 = 1 := by
  have hk1 : 2 ^ (k + 1) ≤ m := Nat.le_trans (Arith.two_pow_le_two_pow (by omega)) hk
  refine ⟨step_forced_odd hn hm hmin hk1 ht1 hj1, ?_⟩
  exact step_forced_odd hn hm hmin hk ht2 hj2

end ForcedSteps
end Collatz
