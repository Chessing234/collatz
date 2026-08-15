import Collatz.Structure.CycleExtremes

/-!
# Powers of two dividing a cycle point

If a cycle point is divisible by `2 ^ k`, the next `k` steps are all halvings —
each intermediate value is still even — so the accelerated map simply divides:

`T^k(y) = y / 2 ^ k`   whenever   `2 ^ k ∣ y`.

The quotient is therefore another point of the same cycle, hence at least the
cycle's least point `m`.  So

**`2 ^ k · m ≤ y`   whenever   `2 ^ k ∣ y`.**

In words: *a cycle point cannot be divisible by a large power of two unless it is
correspondingly large.*  A hypothetical cycle whose least point is at least
`102 400` therefore contains no point divisible by `2 ^ k` below `102 400 · 2 ^ k`,
which rules out, for instance, any cycle point that is a large power of two times
something small.

The lemma `accOrbit_halving` is of independent use: it is the only place in the
project where a *whole block* of accelerated steps is computed in closed form.
-/

namespace Collatz
namespace CycleValuation

open Reach AccCycle CycleExtremes

/-! ## A block of halvings in closed form -/

/-- **A run of halvings.**  If `2 ^ k` divides `y`, the first `k` accelerated
steps from `y` are all halvings, and `T^k(y) = y / 2 ^ k`. -/
theorem accOrbit_halving : ∀ (k y : Nat), 2 ^ k ∣ y → acceleratedOrbit k y = y / 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro y _
    simp [acceleratedOrbit]
  | succ k ih =>
    intro y hdvd
    -- `y` is even, so the first step halves
    have heven : y % 2 = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have h2 : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
      rw [h2, Nat.mul_assoc] at hc
      omega
    have hstep : acceleratedStep y = y / 2 := by
      rw [acceleratedStep, if_pos heven]
    -- and `2 ^ k` divides the half
    have hdvd' : 2 ^ k ∣ y / 2 := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have h2 : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
      rw [h2, Nat.mul_assoc] at hc
      omega
    rw [acceleratedOrbit, hstep, ih (y / 2) hdvd', Nat.div_div_eq_div_mul,
      ← Arith.two_pow_succ]

/-! ## The valuation bound on a cycle -/

/-- **A cycle point divisible by `2 ^ k` is at least `2 ^ k` times the least
point.**  Halving `k` times lands on another point of the same cycle. -/
theorem two_pow_mul_min_le {n m k i : Nat}
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hdvd : 2 ^ k ∣ acceleratedOrbit i n) :
    2 ^ k * m ≤ acceleratedOrbit i n := by
  -- the `k`-fold halving of this point is again on the orbit
  have hhalf : acceleratedOrbit (k + i) n = acceleratedOrbit i n / 2 ^ k := by
    rw [← acceleratedOrbit_add]
    exact accOrbit_halving k (acceleratedOrbit i n) hdvd
  have hge : m ≤ acceleratedOrbit i n / 2 ^ k := by
    have := hmin (k + i)
    rw [hhalf] at this
    exact this
  -- and multiplying back recovers the point exactly
  obtain ⟨c, hc⟩ := hdvd
  have hpow : 0 < 2 ^ k := Arith.two_pow_pos k
  have hquot : acceleratedOrbit i n / 2 ^ k = c := by
    rw [hc]
    exact Nat.mul_div_cancel_left c hpow
  rw [hquot] at hge
  rw [hc]
  exact Nat.mul_le_mul_left _ hge

/-- Restated: on a cycle, a large power of two dividing a point forces the point
to be large. -/
theorem le_of_dvd_cyclePoint {n m k i : Nat}
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hdvd : 2 ^ k ∣ acceleratedOrbit i n) (hm : 102400 ≤ m) :
    102400 * 2 ^ k ≤ acceleratedOrbit i n := by
  have hbound := two_pow_mul_min_le hmin hdvd
  have hmul : 2 ^ k * 102400 ≤ 2 ^ k * m := Nat.mul_le_mul_left _ hm
  have hcomm : 2 ^ k * 102400 = 102400 * 2 ^ k := Nat.mul_comm _ _
  omega

/-- The greatest point of a cycle obeys the same bound, which is the sharpest
instance since the greatest point carries the largest power of two. -/
theorem cycleMax_of_dvd {n m L k : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hdvd : 2 ^ k ∣ cycleMax n L) : 2 ^ k * m ≤ cycleMax n L := by
  obtain ⟨i, _, hval⟩ := cycleMax_attained h
  rw [hval] at hdvd ⊢
  exact two_pow_mul_min_le hmin hdvd

/-- **No cycle point is a small multiple of a large power of two.**  A cycle
point of the form `2 ^ k · c` with `c` below the least point cannot exist. -/
theorem not_small_odd_part {n m k c i : Nat}
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hval : acceleratedOrbit i n = 2 ^ k * c) (hc : c < m) : False := by
  have hdvd : 2 ^ k ∣ acceleratedOrbit i n := ⟨c, hval⟩
  have hbound := two_pow_mul_min_le hmin hdvd
  rw [hval] at hbound
  have hpow : 0 < 2 ^ k := Arith.two_pow_pos k
  have hlt : 2 ^ k * c < 2 ^ k * m := Arith.mul_lt_mul_of_pos_left hc hpow
  omega

end CycleValuation
end Collatz
