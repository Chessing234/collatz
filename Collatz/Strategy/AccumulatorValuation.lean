import Collatz.Strategy.AccumulatorClass

/-!
# The 2-adic valuation of the accumulator is a clock

`AccumulatorArith.affineC_odd_of_odd` says that when the orbit starts odd the
accumulator is odd: `v₂(C) = 0`.  That is the first instance of an exact law.
Since `C` is built as `Σᵢ 3 ^ (a − i) · 2 ^ tᵢ` over the odd-step times
`t₁ < ⋯ < t_a`, the lowest term dominates the 2-adic valuation outright:

**`v₂(C_j(x)) = t₁`, the time of the *first* odd step.**

No later step can interfere, because every later term carries a strictly higher
power of two, and the leading coefficient `3 ^ (a−1)` is odd.  So the
accumulator's 2-adic valuation is not a size at all — it is a timestamp, and it
is frozen the moment the orbit first meets an odd number.

This file proves that in the form the rest of the development can use:

* `affineC_eq_zero_of_no_odd` — no odd step, no accumulator;
* `affineC_even_prefix` — an even prefix factors out as a clean `2 ^ t`;
* `affineC_valuation` — the factored cofactor is odd, so the valuation is
  exactly `t`, not merely at least `t`.

The consequence worth naming is `orbit_mod_two_pow`: for the whole window that
precedes the first odd step, `2 ^ j · T^j(x) ≡ 0 (mod 2 ^ t)` carries no
information, but immediately after it the identity `2 ^ j T^j(x) = 3 ^ a x + C`
splits into a part divisible by exactly `2 ^ t` and a part that is not — which
is what makes `t` recoverable from the arithmetic without watching the orbit.
-/

namespace Collatz
namespace AccumulatorValuation

open Congruence AffineExact AccumulatorArith

/-! ## An even prefix contributes nothing -/

/-- With no odd step in the window the accumulator has never been fed. -/
theorem affineC_eq_zero_of_no_odd {x : Nat} : ∀ {j : Nat}, oddCount x j = 0 → affineC j x = 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hj : oddCount x j = 0 := by omega
      rw [affineC_even he]
      exact ih hj
    · exfalso
      rw [ho] at hlast
      omega

/-- **An even prefix factors out.**  If the first `t` steps are all even then the
accumulator of the whole window is `2 ^ t` times the accumulator of what follows,
started from the state reached at time `t`. -/
theorem affineC_even_prefix {x t : Nat} (h : oddCount x t = 0) (k : Nat) :
    affineC (t + k) x = 2 ^ t * affineC k (acceleratedOrbit t x) := by
  rw [affineC_add x t k, affineC_eq_zero_of_no_odd h, Nat.mul_zero, Nat.zero_add]

/-- **The valuation is exactly the first odd time.**  If the first `t` steps are
even and the state at time `t` is odd, then `affineC (t + k + 1) x` is `2 ^ t`
times an *odd* number: `v₂(C) = t` on the nose. -/
theorem affineC_valuation {x t : Nat} (h : oddCount x t = 0)
    (hodd : acceleratedOrbit t x % 2 = 1) (k : Nat) :
    ∃ c : Nat, affineC (t + (k + 1)) x = 2 ^ t * c ∧ c % 2 = 1 := by
  refine ⟨affineC (k + 1) (acceleratedOrbit t x), affineC_even_prefix h (k + 1), ?_⟩
  exact affineC_odd_of_odd hodd k

/-- The divisibility half, with no existential: `2 ^ t` divides the accumulator
of any window that begins with `t` even steps. -/
theorem two_pow_dvd_affineC {x t : Nat} (h : oddCount x t = 0) (k : Nat) :
    2 ^ t ∣ affineC (t + k) x :=
  ⟨affineC k (acceleratedOrbit t x), affineC_even_prefix h k⟩

/-- The sharpness half: `2 ^ (t + 1)` does *not* divide it once an odd step has
occurred at time `t`.  Together with `two_pow_dvd_affineC` this is `v₂(C) = t`. -/
theorem not_two_pow_succ_dvd_affineC {x t : Nat} (h : oddCount x t = 0)
    (hodd : acceleratedOrbit t x % 2 = 1) (k : Nat) :
    ¬ (2 ^ (t + 1) ∣ affineC (t + (k + 1)) x) := by
  rintro ⟨d, hd⟩
  obtain ⟨c, hc, hcodd⟩ := affineC_valuation h hodd k
  rw [hd, Arith.two_pow_succ] at hc
  have hpos : 0 < 2 ^ t := Arith.two_pow_pos t
  have : 2 * d = c := by
    have h2 : 2 ^ t * (2 * d) = 2 ^ t * c := by
      rw [← hc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ t) 2]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  omega

/-! ## Two starts, one clock -/

/-- Since `C` is a class function (`AccumulatorClass.affineC_congr_of_mod`), so
is its valuation: congruent starts have their first odd step at the same time. -/
theorem valuation_congr_of_mod {x y t k : Nat} (hxy : x % 2 ^ (t + (k + 1)) = y % 2 ^ (t + (k + 1)))
    (h : oddCount x t = 0) (hodd : acceleratedOrbit t x % 2 = 1) :
    ∃ c : Nat, affineC (t + (k + 1)) y = 2 ^ t * c ∧ c % 2 = 1 := by
  obtain ⟨c, hc, hcodd⟩ := affineC_valuation h hodd k
  exact ⟨c, by rw [← AccumulatorClass.affineC_congr_of_mod hxy]; exact hc, hcodd⟩

end AccumulatorValuation
end Collatz
