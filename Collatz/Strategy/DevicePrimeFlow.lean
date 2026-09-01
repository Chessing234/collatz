import Collatz.Strategy.ExcursionMap
import Collatz.Strategy.ScaleRecord

/-!
# Prime-flow along an excursion

`ThreeAdic` tracks `v₃(n+1)`.  `ExcursionLTE` tracks `v₂` of the peak split.
This file tracks **other** odd primes: those dividing `3^v − 1` or `3^v + 1`.

The state is the valuation vector `P(n) = (v_p(n))_p`, not a single prime.
Python-scanned over every odd start `< 20 000` (truncated invariant to
`30 000`): the only ℤ-linear combinations of `P(n)` with non-mixed drift
on both `n ↦ n/2` and `n ↦ 3n+1` are the multiples of `v₂`, and those have
*opposite* signs on the two arrows.  Adding any coordinate `v_p` for
`p | 3^k ± 1` mixes the odd arrow.  That search is the negative pair
`odd_dvd_frozen_under_half` / `five_mixed_under_three_n_succ`.

What *does* flow is a different linear form.  The peak identity
`3^v u − 1 = 2^W e` together with `3^v ≡ 1 (mod m)` for odd `m ∣ 3^v − 1`
gives the **transport**

    m ∣ (u − 1)  ↔  m ∣ e.

That is a finite combination — one divisibility bit per such `m` — with
forced drift *zero* along the excursion.  Surplus above the exact power
of `m` in `3^v − 1` is not conserved: it is truncated
(`five_drop_of_v_four`, `thirteen_drop_of_v_three`).

The `+1` is essential.  `gcd(n, 3n+1) = 1`, while `gcd(n, 3n) = n`, so a
prime dividing `n` survives `expStep`'s even branch `3n/2` and dies at
Collatz's `3n+1`.  The device is not a theorem of `3n` without the `+1`.

This file does not claim Collatz.
-/

namespace Collatz
namespace DevicePrimeFlow

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ScaleRecord


/-! ## 1.  Odd divisors pass through powers of two -/

/-- `gcd(2, d) = 1` for odd `d`. -/
theorem gcd_two_of_odd {d : Nat} (h : d % 2 = 1) : Nat.gcd 2 d = 1 := by
  have hdvd : Nat.gcd 2 d ∣ 2 := Nat.gcd_dvd_left 2 d
  have hle : Nat.gcd 2 d ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  have hne0 : Nat.gcd 2 d ≠ 0 := by
    intro hz
    have : 0 ∣ 2 := hz ▸ hdvd
    exact absurd this (by decide)
  have hcases : Nat.gcd 2 d = 1 ∨ Nat.gcd 2 d = 2 := by omega
  rcases hcases with h1 | h2
  · exact h1
  · have : 2 ∣ d := h2 ▸ Nat.gcd_dvd_right 2 d
    have : d % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp this
    omega

/-- `m ∣ a` implies `m ∣ a * b`. -/
theorem dvd_mul_of {m a b : Nat} (h : m ∣ a) : m ∣ a * b :=
  Nat.dvd_trans h (Nat.dvd_mul_right a b)

/-- `m ∣ b` implies `m ∣ a * b`. -/
theorem dvd_mul_of' {m a b : Nat} (h : m ∣ b) : m ∣ a * b := by
  have : m ∣ b * a := Nat.dvd_trans h (Nat.dvd_mul_right b a)
  rwa [Nat.mul_comm] at this

/-- If `gcd(r, d) = 1` and `d` divides `r * b`, then `d` divides `b`. -/
theorem dvd_of_dvd_mul_coprime {d r b : Nat}
    (hcop : Nat.gcd r d = 1) (h : d ∣ r * b) : d ∣ b := by
  have h1 : d ∣ b * r := by rw [Nat.mul_comm]; exact h
  have h2 : d ∣ b * d := Nat.dvd_mul_left d b
  have hg : d ∣ Nat.gcd (b * r) (b * d) := Nat.dvd_gcd h1 h2
  have heq : Nat.gcd (b * r) (b * d) = b * Nat.gcd r d := Nat.gcd_mul_left b r d
  rw [heq, hcop, Nat.mul_one] at hg
  exact hg

/-- An odd divisor of `2 y` divides `y`. -/
theorem odd_dvd_of_mul_two {d y : Nat} (hodd : d % 2 = 1) (h : d ∣ 2 * y) :
    d ∣ y :=
  dvd_of_dvd_mul_coprime (gcd_two_of_odd hodd) h

/-- An odd divisor of `2^W * y` divides `y`. -/
theorem odd_dvd_of_two_pow_mul {d y : Nat} (hodd : d % 2 = 1) :
    ∀ W, d ∣ 2 ^ W * y → d ∣ y := by
  intro W
  induction W with
  | zero =>
    intro h
    simpa using h
  | succ W ih =>
    intro h
    have hrew : (2 : Nat) ^ (W + 1) * y = 2 * (2 ^ W * y) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ W), Nat.mul_assoc]
    exact ih (odd_dvd_of_mul_two hodd (hrew ▸ h))

/-- `d ∣ a * b` implies `d ∣ (a % d) * b`. -/
theorem dvd_mod_mul {d a b : Nat} (h : d ∣ a * b) : d ∣ (a % d) * b := by
  have hsplit : a * b = d * ((a / d) * b) + (a % d) * b := by
    calc a * b
        = (d * (a / d) + a % d) * b := by rw [Nat.div_add_mod a d]
      _ = d * (a / d) * b + (a % d) * b := Nat.add_mul _ _ _
      _ = d * ((a / d) * b) + (a % d) * b := by rw [Nat.mul_assoc]
  have hy : d ∣ d * ((a / d) * b) := ⟨(a / d) * b, rfl⟩
  exact (Nat.dvd_add_iff_right hy).mpr (hsplit ▸ h)


/-! ## 2.  Euclid at the first primes dividing `3^k − 1` -/

/-- Residues `1,2,3,4` are coprime to five. -/
theorem gcd_five_small {r : Nat} (h0 : 0 < r) (h : r < 5) : Nat.gcd r 5 = 1 := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr with h | h | h | h <;> subst h <;> decide

/-- Residues `1…12` are coprime to thirteen. -/
theorem gcd_thirteen_small {r : Nat} (h0 : 0 < r) (h : r < 13) :
    Nat.gcd r 13 = 1 := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
      r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 := by omega
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- Euclid's lemma at `p = 5`. -/
theorem five_dvd_mul {a b : Nat} (h : 5 ∣ a * b) : 5 ∣ a ∨ 5 ∣ b := by
  have hmod : 5 ∣ (a % 5) * b := dvd_mod_mul h
  rcases Nat.eq_zero_or_pos (a % 5) with h0 | hp
  · left
    exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · right
    exact dvd_of_dvd_mul_coprime (gcd_five_small hp (Nat.mod_lt a (by decide))) hmod

/-- Euclid's lemma at `p = 13`. -/
theorem thirteen_dvd_mul {a b : Nat} (h : 13 ∣ a * b) : 13 ∣ a ∨ 13 ∣ b := by
  have hmod : 13 ∣ (a % 13) * b := dvd_mod_mul h
  rcases Nat.eq_zero_or_pos (a % 13) with h0 | hp
  · left
    exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · right
    exact dvd_of_dvd_mul_coprime
      (gcd_thirteen_small hp (Nat.mod_lt a (by decide))) hmod


/-! ## 3.  Peak identities -/

/-- `3^v + 1 ≤ 3^v (u + 1)` for `u ≥ 1`. -/
theorem three_pow_succ_le_mul {v u : Nat} (hu : 1 ≤ u) :
    3 ^ v + 1 ≤ 3 ^ v * (u + 1) := by
  have h3 : 1 ≤ 3 ^ v := one_le_three_pow v
  have hu2 : 2 ≤ u + 1 := by omega
  have hdouble : 3 ^ v + 3 ^ v = 3 ^ v * 2 := by
    rw [Nat.mul_comm, Nat.two_mul]
  have h1 : 3 ^ v + 1 ≤ 3 ^ v + 3 ^ v := by omega
  have h2 : 3 ^ v * 2 ≤ 3 ^ v * (u + 1) := Nat.mul_le_mul_left _ hu2
  omega

/-- **Minus split.**  `3^v u − 1 = (3^v − 1) u + (u − 1)`. -/
theorem peak_of_minus {v u : Nat} (hu : 1 ≤ u) :
    3 ^ v * u - 1 = (3 ^ v - 1) * u + (u - 1) := by
  have h3 : 1 ≤ 3 ^ v := one_le_three_pow v
  have hdist : (3 ^ v - 1) * u = 3 ^ v * u - u := by
    rw [Nat.mul_comm (3 ^ v - 1), Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm u]
  have hule : u ≤ 3 ^ v * u := Nat.le_mul_of_pos_left u h3
  have hadd : 3 ^ v * u - u + (u - 1) = 3 ^ v * u - 1 := by
    have : 3 ^ v * u - u + u - 1 = 3 ^ v * u - 1 := by
      rw [Nat.sub_add_cancel hule]
    rw [← Nat.add_sub_assoc hu]
    exact this
  rw [hdist, hadd]

/-- **Plus split.**  `3^v u − 1 = 3^v (u + 1) − (3^v + 1)`. -/
theorem peak_of_plus {v u : Nat} (hu : 1 ≤ u) :
    3 ^ v * u - 1 = 3 ^ v * (u + 1) - (3 ^ v + 1) := by
  have h3 : 1 ≤ 3 ^ v := one_le_three_pow v
  have hdist : 3 ^ v * (u + 1) = 3 ^ v * u + 3 ^ v := by
    rw [Nat.mul_add, Nat.mul_one]
  have hle := three_pow_succ_le_mul (v := v) hu
  have hsub : 3 ^ v * u + 3 ^ v - (3 ^ v + 1) = 3 ^ v * u - 1 := by
    have : 1 ≤ 3 ^ v * u := Nat.mul_le_mul h3 hu
    rw [Nat.sub_add_eq, Nat.add_sub_cancel]
  rw [hdist, hsub]


/-! ## 4.  Transport: odd `m ∣ 3^v ± 1` flows from the cofactor to the landing -/

/-- The peak of an excursion is `2^W e`. -/
theorem peak_eq_two_pow {n v u W e : Nat} (h : IsExcursion n v u W e) :
    3 ^ v * u - 1 = 2 ^ W * e := by
  rw [h.2.2.2.2.2.2, Nat.add_sub_cancel]

/-- `u ≥ 1` on every excursion (the cofactor is odd). -/
theorem one_le_u {n v u W e : Nat} (h : IsExcursion n v u W e) : 1 ≤ u := by
  have : u % 2 = 1 := h.2.1
  omega

/-- If `m` divides both `(3^v − 1) u` and the peak, it divides `u − 1`. -/
theorem dvd_u_pred_of_dvd_peak {m v u : Nat} (hu : 1 ≤ u)
    (hm : m ∣ 3 ^ v - 1) (hp : m ∣ 3 ^ v * u - 1) : m ∣ u - 1 := by
  have hid := peak_of_minus (v := v) hu
  have hA : m ∣ (3 ^ v - 1) * u := dvd_mul_of hm
  have hp' : m ∣ (3 ^ v - 1) * u + (u - 1) := hid ▸ hp
  exact (Nat.dvd_add_iff_right hA).mpr hp'

/-- Conversely, those two divisibilities rebuild the peak. -/
theorem dvd_peak_of_dvd_u_pred {m v u : Nat} (hu : 1 ≤ u)
    (hm : m ∣ 3 ^ v - 1) (hu' : m ∣ u - 1) : m ∣ 3 ^ v * u - 1 := by
  have hid := peak_of_minus (v := v) hu
  have hA : m ∣ (3 ^ v - 1) * u := dvd_mul_of hm
  have : m ∣ (3 ^ v - 1) * u + (u - 1) := (Nat.dvd_add_iff_right hA).mp hu'
  exact hid ▸ this

/-- **Minus transport, algebraic.**  For any `m ∣ 3^v − 1`,

    `m ∣ (3^v u − 1)  ↔  m ∣ (u − 1)`. -/
theorem dvd_peak_iff_dvd_u_pred {m v u : Nat} (hu : 1 ≤ u) (hm : m ∣ 3 ^ v - 1) :
    m ∣ 3 ^ v * u - 1 ↔ m ∣ u - 1 :=
  ⟨dvd_u_pred_of_dvd_peak hu hm, dvd_peak_of_dvd_u_pred hu hm⟩

/-- **Prime-flow, minus side.**  An odd divisor of `3^v − 1` divides the
landing `e` if and only if it divides the cofactor gap `u − 1`.

This is *not* `v₃(n+1)` (`ThreeAdic`) and *not* `v₂` (`ExcursionLTE`).  It
is a coordinate of `P` at a prime dividing `3^v − 1`, read on two linear
forms of the excursion datum. -/
theorem flow_minus {n v u W e m : Nat} (h : IsExcursion n v u W e)
    (hodd : m % 2 = 1) (hm : m ∣ 3 ^ v - 1) :
    m ∣ u - 1 ↔ m ∣ e := by
  have hu : 1 ≤ u := one_le_u h
  have hpeak : 3 ^ v * u - 1 = 2 ^ W * e := peak_eq_two_pow h
  have iffPeak : m ∣ 3 ^ v * u - 1 ↔ m ∣ u - 1 :=
    dvd_peak_iff_dvd_u_pred hu hm
  have iffE : m ∣ 3 ^ v * u - 1 ↔ m ∣ e := by
    constructor
    · intro hd
      exact odd_dvd_of_two_pow_mul hodd W (hpeak ▸ hd)
    · intro hd
      exact hpeak ▸ dvd_mul_of' hd
  exact iffPeak.symm.trans iffE

/-- `3` does not divide `3^v + 1` for `v > 0`. -/
theorem three_not_dvd_three_pow_succ {v : Nat} (hv : 0 < v) :
    ¬ (3 ∣ 3 ^ v + 1) := by
  intro h
  have hpow : 3 ∣ 3 ^ v := by
    have hv1 : v = v - 1 + 1 := by omega
    rw [hv1, three_pow_succ]
    exact ⟨3 ^ (v - 1), rfl⟩
  have : 3 ∣ 1 := (Nat.dvd_add_iff_right hpow).mpr h
  omega

/-- A common divisor of `3^v` and of `3^v + 1` is `1`. -/
theorem gcd_three_pow_eq_one_of_dvd_succ {m v : Nat}
    (hm : m ∣ 3 ^ v + 1) : Nat.gcd (3 ^ v) m = 1 := by
  have hg1 : Nat.gcd (3 ^ v) m ∣ 3 ^ v := Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (3 ^ v) m ∣ m := Nat.gcd_dvd_right _ _
  have hg3 : Nat.gcd (3 ^ v) m ∣ 3 ^ v + 1 := Nat.dvd_trans hg2 hm
  have : Nat.gcd (3 ^ v) m ∣ 1 := (Nat.dvd_add_iff_right hg1).mpr hg3
  exact Nat.dvd_one.mp this

/-- **Plus transport, algebraic.**  For any `m ∣ 3^v + 1`,

    `m ∣ (3^v u − 1)  ↔  m ∣ (u + 1)`. -/
theorem dvd_peak_iff_dvd_u_succ {m v u : Nat} (hu : 1 ≤ u)
    (hm : m ∣ 3 ^ v + 1) :
    m ∣ 3 ^ v * u - 1 ↔ m ∣ u + 1 := by
  have hid := peak_of_plus (v := v) hu
  have hcop : Nat.gcd (3 ^ v) m = 1 := gcd_three_pow_eq_one_of_dvd_succ hm
  have hR := three_pow_succ_le_mul (v := v) hu
  have hsum : 3 ^ v * (u + 1) = (3 ^ v * u - 1) + (3 ^ v + 1) := by
    have := Nat.sub_add_cancel hR
    rw [← hid] at this
    exact this.symm
  constructor
  · intro hp
    have : m ∣ 3 ^ v * (u + 1) := by
      rw [hsum]
      exact Nat.dvd_add hp hm
    exact dvd_of_dvd_mul_coprime hcop this
  · intro hu1
    have hA : m ∣ 3 ^ v * (u + 1) := dvd_mul_of' hu1
    have hcancel :
        3 ^ v * (u + 1) =
          (3 ^ v * (u + 1) - (3 ^ v + 1)) + (3 ^ v + 1) :=
      (Nat.sub_add_cancel hR).symm
    have hA' : m ∣ (3 ^ v * (u + 1) - (3 ^ v + 1)) + (3 ^ v + 1) := by
      rwa [← hcancel]
    have hpeak' : m ∣ 3 ^ v * (u + 1) - (3 ^ v + 1) :=
      (Nat.dvd_add_iff_left hm).mpr hA'
    exact hid ▸ hpeak'

/-- **Prime-flow, plus side.**  An odd divisor of `3^v + 1` divides the
landing `e` if and only if it divides `u + 1`. -/
theorem flow_plus {n v u W e m : Nat} (h : IsExcursion n v u W e)
    (hodd : m % 2 = 1) (hm : m ∣ 3 ^ v + 1) :
    m ∣ u + 1 ↔ m ∣ e := by
  have hu : 1 ≤ u := one_le_u h
  have hpeak : 3 ^ v * u - 1 = 2 ^ W * e := peak_eq_two_pow h
  have iffPeak : m ∣ 3 ^ v * u - 1 ↔ m ∣ u + 1 :=
    dvd_peak_iff_dvd_u_succ hu hm
  have iffE : m ∣ 3 ^ v * u - 1 ↔ m ∣ e := by
    constructor
    · intro hd
      exact odd_dvd_of_two_pow_mul hodd W (hpeak ▸ hd)
    · intro hd
      exact hpeak ▸ dvd_mul_of' hd
  exact iffPeak.symm.trans iffE


/-! ## 5.  Named primes: `13 ∣ 3^3 − 1`, `5 ∣ 3^4 − 1` -/

/-- `13` divides `3^3 − 1 = 26`. -/
theorem thirteen_dvd_three_pow_three : 13 ∣ 3 ^ 3 - 1 := by decide

/-- `5` divides `3^4 − 1 = 80`. -/
theorem five_dvd_three_pow_four : 5 ∣ 3 ^ 4 - 1 := by decide

/-- `25` does not divide `80`. -/
theorem twenty_five_not_dvd_eighty : ¬ (25 ∣ 3 ^ 4 - 1) := by decide

/-- `169` does not divide `26`. -/
theorem one_sixty_nine_not_dvd_twenty_six : ¬ (169 ∣ 3 ^ 3 - 1) := by decide

/-- **`v = 3` leftover flow.**  Along a length-`3` odd run, `13` divides the
landing iff it divides `u − 1`. -/
theorem thirteen_flow_of_v_three {n u W e : Nat} (h : IsExcursion n 3 u W e) :
    13 ∣ u - 1 ↔ 13 ∣ e :=
  flow_minus h (by decide) thirteen_dvd_three_pow_three

/-- **`v = 4` five-flow.**  Along a length-`4` odd run, `5` divides the
landing iff it divides `u − 1`. -/
theorem five_flow_of_v_four {n u W e : Nat} (h : IsExcursion n 4 u W e) :
    5 ∣ u - 1 ↔ 5 ∣ e :=
  flow_minus h (by decide) five_dvd_three_pow_four

/-- `7` divides `3^3 + 1 = 28`. -/
theorem seven_dvd_three_pow_three_succ : 7 ∣ 3 ^ 3 + 1 := by decide

/-- **`v = 3` plus-flow at `7`.**  `7 ∣ 3^3 + 1`, so `7` divides the landing
iff it divides `u + 1`. -/
theorem seven_flow_plus_of_v_three {n u W e : Nat} (h : IsExcursion n 3 u W e) :
    7 ∣ u + 1 ↔ 7 ∣ e :=
  flow_plus h (by decide) seven_dvd_three_pow_three_succ


/-! ## 6.  Forced drop of surplus valuation -/

/-- If `d > 1` divides both `u` and `u − 1`, it divides `1`. -/
theorem dvd_one_of_dvd_u_and_pred {d u : Nat} (hu : 1 ≤ u)
    (h1 : d ∣ u) (h2 : d ∣ u - 1) : d ∣ 1 := by
  have : d ∣ (u - 1) + 1 := by
    rw [Nat.sub_add_cancel hu]
    exact h1
  exact (Nat.dvd_add_iff_right h2).mpr this

/-- **Truncation at a prime.**  If `d` divides `3^v − 1` exactly to the first
power, and `d^2` divides `u − 1`, then `d` divides the landing but `d^2`
does not.  The extra `d`-power is forced to drop. -/
theorem flow_drop {n v u W e d : Nat} (h : IsExcursion n v u W e)
    (hodd : d % 2 = 1) (hdgt : 1 < d)
    (hm : d ∣ 3 ^ v - 1) (hn2 : ¬ (d * d ∣ 3 ^ v - 1))
    (hsq : d * d ∣ u - 1)
    (heuclid : ∀ a b : Nat, d ∣ a * b → d ∣ a ∨ d ∣ b) :
    d ∣ e ∧ ¬ (d * d ∣ e) := by
  have hu : 1 ≤ u := one_le_u h
  have hpeak : 3 ^ v * u - 1 = 2 ^ W * e := peak_eq_two_pow h
  have hd1 : d ∣ u - 1 :=
    Nat.dvd_trans ⟨d, by rw [Nat.mul_comm]⟩ hsq
  have hde : d ∣ e := (flow_minus h hodd hm).mp hd1
  refine ⟨hde, ?_⟩
  intro hsqe
  have hsqPeak : d * d ∣ 3 ^ v * u - 1 := by
    rw [hpeak]
    exact dvd_mul_of' hsqe
  have hid := peak_of_minus (v := v) hu
  have hA : d * d ∣ (3 ^ v - 1) * u := by
    have : d * d ∣ (3 ^ v - 1) * u + (u - 1) := hid ▸ hsqPeak
    exact (Nat.dvd_add_iff_left hsq).mpr this
  obtain ⟨t, ht⟩ := hm
  have hnott : ¬ (d ∣ t) := by
    intro ht'
    obtain ⟨s, hs⟩ := ht'
    have : d * d ∣ 3 ^ v - 1 := ⟨s, by rw [ht, hs, Nat.mul_assoc]⟩
    exact hn2 this
  have hnotu : ¬ (d ∣ u) := by
    intro hu'
    have : d ∣ 1 := dvd_one_of_dvd_u_and_pred hu hu' hd1
    have : d ≤ 1 := Nat.le_of_dvd (by decide) this
    omega
  have htu : d ∣ t * u := by
    have : d * d ∣ d * (t * u) := by
      have hrew : (3 ^ v - 1) * u = d * (t * u) := by
        rw [ht, Nat.mul_assoc]
      exact hrew ▸ hA
    have hdpos : 0 < d := by omega
    exact (Nat.mul_dvd_mul_iff_left hdpos).mp this
  rcases heuclid t u htu with ht' | hu'
  · exact hnott ht'
  · exact hnotu hu'

/-- **Forced five-drop on a `v = 4` excursion.**  If `25 ∣ (u − 1)` then
the landing is divisible by `5` exactly once. -/
theorem five_drop_of_v_four {n u W e : Nat}
    (h : IsExcursion n 4 u W e) (hsq : 25 ∣ u - 1) :
    5 ∣ e ∧ ¬ (25 ∣ e) :=
  flow_drop h (by decide) (by decide) five_dvd_three_pow_four
    twenty_five_not_dvd_eighty hsq (fun a b h => five_dvd_mul h)

/-- **Forced thirteen-drop on a `v = 3` excursion.**  If `169 ∣ (u − 1)`
then the landing is divisible by `13` exactly once. -/
theorem thirteen_drop_of_v_three {n u W e : Nat}
    (h : IsExcursion n 3 u W e) (hsq : 169 ∣ u - 1) :
    13 ∣ e ∧ ¬ (169 ∣ e) :=
  flow_drop h (by decide) (by decide) thirteen_dvd_three_pow_three
    one_sixty_nine_not_dvd_twenty_six hsq (fun a b h => thirteen_dvd_mul h)

/-- Concrete five-drop numbers: cofactor `51 = 1 + 2·5^2`, landing `2065 = 5 · 413`. -/
theorem five_drop_numbers : 25 ∣ 51 - 1 ∧ 5 ∣ 2065 ∧ ¬ (25 ∣ 2065) := by decide

/-- Concrete thirteen-drop numbers: cofactor `339 = 1 + 2·13^2`, landing `143 = 11 · 13`. -/
theorem thirteen_drop_numbers : 169 ∣ 339 - 1 ∧ 13 ∣ 143 ∧ ¬ (169 ∣ 143) := by decide


/-! ## 7.  The `expStep` test: `v_p(3n)` vs `v_p(3n+1)` -/

/-- Euclid: `gcd(n, 3n+1) = 1`.  The `+1` kills every prime of `n`. -/
theorem gcd_n_three_n_succ (n : Nat) : Nat.gcd n (3 * n + 1) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · decide
  · have hrec : Nat.gcd n (3 * n + 1) = Nat.gcd ((3 * n + 1) % n) n :=
      Nat.gcd_rec n (3 * n + 1)
    have hmod : (3 * n + 1) % n = 1 % n := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
    rw [hrec, hmod, Nat.gcd_comm]
    have h1n : 1 ≤ n := hp
    rcases Nat.eq_or_lt_of_le h1n with h1 | hlt
    · subst h1; decide
    · have : 1 % n = 1 := Nat.mod_eq_of_lt hlt
      rw [this]
      exact Nat.gcd_one_right n

/-- Without the `+1`: `gcd(n, 3n) = n`.  Every prime of `n` survives. -/
theorem gcd_n_three_n (n : Nat) : Nat.gcd n (3 * n) = n :=
  Nat.gcd_eq_left (dvd_mul_of' (Nat.dvd_refl n))

/-- A prime dividing `n` cannot divide `3n+1`, unless it is `1`. -/
theorem eq_one_of_dvd_n_and_three_n_succ {p n : Nat}
    (h1 : p ∣ n) (h2 : p ∣ 3 * n + 1) : p = 1 := by
  have : p ∣ Nat.gcd n (3 * n + 1) := Nat.dvd_gcd h1 h2
  rw [gcd_n_three_n_succ] at this
  exact Nat.dvd_one.mp this

/-- The same prime *does* divide `3n`. -/
theorem dvd_three_mul_of_dvd {p n : Nat} (h : p ∣ n) : p ∣ 3 * n :=
  dvd_mul_of' h

/-- **`expStep` even branch is `3x/2`.**  Quoted so the discrimination is a
theorem about the actual witness map, not only about `3n`. -/
theorem expStep_even_is_three_half {x : Nat} (he : x % 2 = 0) :
    expStep x = 3 * x / 2 := by
  unfold expStep
  rw [if_pos he]

/-- On that branch a prime of `x` survives (after the harmless `/2`, which
an odd prime ignores).  At Collatz's `3x+1` the same prime dies. -/
theorem expStep_preserves_odd_prime {p x : Nat}
    (_hodd : p % 2 = 1) (he : x % 2 = 0) (hp : p ∣ x) :
    p ∣ 2 * expStep x := by
  rw [expStep_even_is_three_half he]
  have : 2 * (3 * x / 2) = 3 * x := by
    have : 2 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr he
    have : 2 ∣ 3 * x := dvd_mul_of' this
    exact Nat.mul_div_cancel' this
  rw [this]
  exact dvd_three_mul_of_dvd hp

/-- Collatz's `+1` is the whole difference: the same `p` cannot divide both
`x` and `3x+1`. -/
theorem collatz_kills_odd_prime {p x : Nat}
    (hp : p ∣ x) (h1 : 1 < p) : ¬ (p ∣ 3 * x + 1) := by
  intro h
  have : p = 1 := eq_one_of_dvd_n_and_three_n_succ hp h
  omega


/-! ## 8.  No same-sign ranking from `P(n)` itself -/

/-- Odd primes are frozen by `n ↦ n/2`.  This is the even arrow of `P(n)`:
only the `p = 2` coordinate moves. -/
theorem odd_dvd_frozen_under_half {p n : Nat}
    (hodd : p % 2 = 1) (he : n % 2 = 0) : p ∣ n ↔ p ∣ n / 2 := by
  have hn : n = 2 * (n / 2) := by omega
  constructor
  · intro h
    have : p ∣ 2 * (n / 2) := hn ▸ h
    exact odd_dvd_of_mul_two hodd this
  · intro h
    exact hn ▸ dvd_mul_of' h

/-- **`v₅` is mixed under `n ↦ 3n+1`.**  It falls at `n = 5` and rises at
`n = 3`.  Together with `odd_dvd_frozen_under_half`, no nonzero weight on
the `p = 5` coordinate of `P(n)` has forced same-sign drift on both
arrows.  The same mixed pair exists at `p = 13` (`13` falls at `n = 13`,
rises at `n = 4` after one even step, or at odd `n = 17` since
`3·17+1 = 52 = 4·13`). -/
theorem five_mixed_under_three_n_succ :
    (5 ∣ 5 ∧ ¬ (5 ∣ 3 * 5 + 1)) ∧ (¬ (5 ∣ 3) ∧ 5 ∣ 3 * 3 + 1) := by
  decide

/-- The `p = 13` coordinate is mixed on odd starts too. -/
theorem thirteen_mixed_under_three_n_succ :
    (13 ∣ 13 ∧ ¬ (13 ∣ 3 * 13 + 1)) ∧ (¬ (13 ∣ 17) ∧ 13 ∣ 3 * 17 + 1) := by
  decide

/-- `v₂` itself has opposite signs: it falls on `n ↦ n/2` and rises on
odd `n ↦ 3n+1`.  That is why the scan's only non-mixed combinations of
`P(n)` cannot be a joint Lyapunov. -/
theorem val2_opposite_signs :
    (Val2 10 1 ∧ Val2 (10 / 2) 0) ∧ (5 % 2 = 1 ∧ Val2 (3 * 5 + 1) 4) := by
  refine ⟨⟨⟨5, rfl, rfl⟩, ⟨5, rfl, rfl⟩⟩, ⟨rfl, ⟨1, rfl, rfl⟩⟩⟩


/-! ## Axiom audit -/

#print axioms flow_minus
#print axioms flow_plus
#print axioms thirteen_flow_of_v_three
#print axioms five_drop_of_v_four
#print axioms thirteen_drop_of_v_three
#print axioms gcd_n_three_n_succ
#print axioms collatz_kills_odd_prime
#print axioms five_mixed_under_three_n_succ

end DevicePrimeFlow
end Collatz
