import Collatz.Strategy.ExcursionBlock
import Collatz.Strategy.ExcursionClock
import Collatz.Strategy.ExcursionPlusFive

/-!
# Longer `(2, 1)` light chains, then remainder `1` or `3`

Each `(v, W) = (2, 1)` step grows by `9/8` (`eight_clock`).  After `k`
lights the remainder of `v₂(· + 5)` is `1`, `2`, or `3`.  This file treats
the two contracting exits:

* remainder `1`: landing `e ≡ 1 (mod 4)`, next run `v' = 1`.  The `W' = 1`
  bound is `3/4` relative to that landing, so the product is
  `(9/8)^k · (3/4)`.
* remainder `3`: landing `e ≡ 3 (mod 16)`, next run `v' = 2` with `W' ≥ 2`.
  The `W' = 2` bound is `9/16`, so the product is `(9/8)^k · (9/16)`.

Whenever that product is strictly less than one, the `W`-minimum upper
bound already sits below the original start (and every larger `W` as
well).  When it exceeds one, the same comparison becomes a **growth law**
at the minimum `W'`, and a drop only after one extra halving.

  rem `1`:  `k = 2` gives `243/256 < 1` (drops at `W' = 1`);
            `k = 3` gives `2187/2048 > 1` (grows at `W' = 1`, drops at
            `W' ≥ 2`).

  rem `3`:  `k = 3` gives `6561/8192 < 1`;
            `k = 4` gives `59049/65536 < 1`;
            `k = 5` gives `531441/524288 > 1` (grows at `W' = 2`, drops
            at `W' ≥ 3`).

The one-step rem-`1` class is `lemmaX_of_eleven_mod_thirtytwo`; the
two-step rem-`3` class is `lemmaX_of_two_light_then_three`.  This file
does not claim Collatz: rem-`2` exits, and the growing `W'`-minimum
families above, remain.
-/

namespace Collatz
namespace ExcursionLightK

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionBlock Collatz.ExcursionClock Collatz.ExcursionExit
open Collatz.ExcursionPlusFive


/-! ## 1.  Fuel after `k` lights -/

/-- Two consecutive `(2, 1)` steps with remainder `1` at the second
landing force `v₂(n + 5) = 7`. -/
theorem two_light_then_one_fuel {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (hrem : Val2 (e2 + 5) 1) : Val2 (n + 5) 7 := by
  have hmid : Val2 (e + 5) 4 := by
    have := val2_plus_five_shift h2 hrem
    simpa using this
  have := val2_plus_five_shift h1 hmid
  simpa using this

/-- Three consecutive `(2, 1)` steps with remainder `1` force
`v₂(n + 5) = 10`. -/
theorem three_light_then_one_fuel {n u e u2 e2 u3 e3 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (hrem : Val2 (e3 + 5) 1) :
    Val2 (n + 5) 10 := by
  have h2' : Val2 (e2 + 5) 4 := by
    have := val2_plus_five_shift h3 hrem
    simpa using this
  have h1' : Val2 (e + 5) 7 := by
    have := val2_plus_five_shift h2 h2'
    simpa using this
  have := val2_plus_five_shift h1 h1'
  simpa using this

/-- Three consecutive `(2, 1)` steps with remainder `3` force
`v₂(n + 5) = 12`. -/
theorem three_light_then_three_fuel {n u e u2 e2 u3 e3 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (hrem : Val2 (e3 + 5) 3) :
    Val2 (n + 5) 12 := by
  have h2' : Val2 (e2 + 5) 6 := by
    have := val2_plus_five_shift h3 hrem
    simpa using this
  have h1' : Val2 (e + 5) 9 := by
    have := val2_plus_five_shift h2 h2'
    simpa using this
  have := val2_plus_five_shift h1 h1'
  simpa using this

/-- Four consecutive `(2, 1)` steps with remainder `3` force
`v₂(n + 5) = 15`. -/
theorem four_light_then_three_fuel {n u e u2 e2 u3 e3 u4 e4 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (hrem : Val2 (e4 + 5) 3) : Val2 (n + 5) 15 := by
  have h3' : Val2 (e3 + 5) 6 := by
    have := val2_plus_five_shift h4 hrem
    simpa using this
  have h2' : Val2 (e2 + 5) 9 := by
    have := val2_plus_five_shift h3 h3'
    simpa using this
  have h1' : Val2 (e + 5) 12 := by
    have := val2_plus_five_shift h2 h2'
    simpa using this
  have := val2_plus_five_shift h1 h1'
  simpa using this

/-- Five consecutive `(2, 1)` steps with remainder `3` force
`v₂(n + 5) = 18`. -/
theorem five_light_then_three_fuel {n u e u2 e2 u3 e3 u4 e4 u5 e5 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (h5 : IsExcursion e4 2 u5 1 e5) (hrem : Val2 (e5 + 5) 3) :
    Val2 (n + 5) 18 := by
  have h4' : Val2 (e4 + 5) 6 := by
    have := val2_plus_five_shift h5 hrem
    simpa using this
  have h3' : Val2 (e3 + 5) 9 := by
    have := val2_plus_five_shift h4 h4'
    simpa using this
  have h2' : Val2 (e2 + 5) 12 := by
    have := val2_plus_five_shift h3 h3'
    simpa using this
  have h1' : Val2 (e + 5) 15 := by
    have := val2_plus_five_shift h2 h2'
    simpa using this
  have := val2_plus_five_shift h1 h1'
  simpa using this


/-! ## 2.  Exit residues -/

/-- Remainder `1` is `e ≡ 1 (mod 4)`. -/
theorem e_one_mod_four {e : Nat} (hrem : Val2 (e + 5) 1) : e % 4 = 1 := by
  have : (e + 5) % 4 = 2 := Val2.one_iff.mp hrem
  omega

/-- Remainder `3` is `e ≡ 3 (mod 16)`. -/
theorem e_three_mod_sixteen {e : Nat} (hrem : Val2 (e + 5) 3) :
    e % 16 = 3 := by
  have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
  have : (e + 5) % 16 = 8 := by
    have := Val2.mod hrem
    rwa [hpow] at this
  omega

/-- Every `(2, 1)` start is at least `11`. -/
theorem eleven_le_of_light {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    11 ≤ n := by
  have hmod : n % 16 = 11 := (v_two_W_one_iff h).mp ⟨rfl, rfl⟩
  omega


/-! ## 3.  `W`-upper bounds on the exit excursion -/

/-- **`W ≥ 1` upper bound** on a `v = 1` landing: `4 e ≤ 3 m + 1`, with
equality at `W = 1`.  Relative to `m` this is the factor `3/4`. -/
theorem landing_upper_of_v_one {m um Wm em : Nat}
    (h : IsExcursion m 1 um Wm em) : 4 * em ≤ 3 * m + 1 := by
  have hnu : m + 1 = 2 * um := by
    have := h.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  have hpeak : 3 * um = 2 ^ Wm * em + 1 := by
    have := h.2.2.2.2.2.2
    rw [Nat.pow_one] at this
    exact this
  have hW : 1 ≤ Wm := IsExcursion.one_le_W h
  have h2 : 2 ≤ 2 ^ Wm := two_le_two_pow (by omega)
  have hle : 2 * em ≤ 3 * um - 1 := by
    have hmul : 2 * em ≤ 2 ^ Wm * em := Nat.mul_le_mul_right em h2
    have : 2 ^ Wm * em = 3 * um - 1 := by omega
    omega
  omega

/-- Equality case of the `v = 1`, `W = 1` bound. -/
theorem landing_eq_of_v_one_W_one {m um em : Nat}
    (h : IsExcursion m 1 um 1 em) : 4 * em = 3 * m + 1 := by
  have hnu : m + 1 = 2 * um := by
    have := h.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  have hpeak : 3 * um = 2 * em + 1 := by
    have := h.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this
  omega

/-- **`W ≥ 2` upper bound** on a `v = 1` landing: `8 e ≤ 3 m + 1`. -/
theorem landing_upper_of_v_one_W_ge_two {m um Wm em : Nat}
    (h : IsExcursion m 1 um Wm em) (hW : 2 ≤ Wm) :
    8 * em ≤ 3 * m + 1 := by
  have hnu : m + 1 = 2 * um := by
    have := h.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  have hpeak : 3 * um = 2 ^ Wm * em + 1 := by
    have := h.2.2.2.2.2.2
    rw [Nat.pow_one] at this
    exact this
  have h4 : 4 ≤ 2 ^ Wm := by
    have : (2 : Nat) ^ 2 ≤ 2 ^ Wm := two_pow_le_two_pow hW
    simpa using this
  have hle : 4 * em ≤ 3 * um - 1 := by
    have hmul : 4 * em ≤ 2 ^ Wm * em := Nat.mul_le_mul_right em h4
    have : 2 ^ Wm * em = 3 * um - 1 := by omega
    omega
  omega

private theorem four_le_two_pow {W : Nat} (hW : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

/-- **`W ≥ 2` upper bound** on a `v = 2` landing: `16 e ≤ 9 m + 5`, with
equality at `W = 2`.  Relative to `m` this is the factor `9/16`. -/
theorem landing_upper_of_v_two_W_ge_two {m um Wm em : Nat}
    (h : IsExcursion m 2 um Wm em) (hW : 2 ≤ Wm) :
    16 * em ≤ 9 * m + 5 := by
  have hnu : m + 1 = 4 * um := by
    have := h.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * um = 2 ^ Wm * em + 1 := by
    have := h.2.2.2.2.2.2
    rw [show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have h4 := four_le_two_pow hW
  have hle : 4 * em ≤ 9 * um - 1 := by
    have hmul : 4 * em ≤ 2 ^ Wm * em := Nat.mul_le_mul_right em h4
    have : 2 ^ Wm * em = 9 * um - 1 := by omega
    omega
  have hscale : 4 * (9 * um - 1) = 9 * m + 5 := by omega
  have hmul : 4 * (4 * em) ≤ 4 * (9 * um - 1) := Nat.mul_le_mul_left 4 hle
  have h16 : (16 : Nat) * em = 4 * (4 * em) := by omega
  omega

/-- Equality case of the `v = 2`, `W = 2` bound. -/
theorem landing_eq_of_v_two_W_two {m um em : Nat}
    (h : IsExcursion m 2 um 2 em) : 16 * em = 9 * m + 5 := by
  have hnu : m + 1 = 4 * um := by
    have := h.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * um = 4 * em + 1 := by
    have := h.2.2.2.2.2.2
    rw [show (3 : Nat) ^ 2 = 9 by decide, show (2 : Nat) ^ 2 = 4 by decide]
      at this
    exact this
  omega

private theorem eight_le_two_pow {W : Nat} (hW : 3 ≤ W) : 8 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 3 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

/-- **`W ≥ 3` upper bound** on a `v = 2` landing: `32 e ≤ 9 m + 5`. -/
theorem landing_upper_of_v_two_W_ge_three {m um Wm em : Nat}
    (h : IsExcursion m 2 um Wm em) (hW : 3 ≤ Wm) :
    32 * em ≤ 9 * m + 5 := by
  have hnu : m + 1 = 4 * um := by
    have := h.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * um = 2 ^ Wm * em + 1 := by
    have := h.2.2.2.2.2.2
    rw [show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have h8 := eight_le_two_pow hW
  have hle : 8 * em ≤ 9 * um - 1 := by
    have hmul : 8 * em ≤ 2 ^ Wm * em := Nat.mul_le_mul_right em h8
    have : 2 ^ Wm * em = 9 * um - 1 := by omega
    omega
  have hscale : 4 * (9 * um - 1) = 9 * m + 5 := by omega
  have hmul : 4 * (8 * em) ≤ 4 * (9 * um - 1) := Nat.mul_le_mul_left 4 hle
  have h32 : (32 : Nat) * em = 4 * (8 * em) := by omega
  omega


/-! ## 4.  Clock composition -/

/-- Integer form of one `(2, 1)` step. -/
theorem one_light_clock {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    8 * e = 9 * n + 5 := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_two_W_one h
  omega

/-- Compose one more light step onto an affine clock
`a e = b n + c`. -/
theorem compose_light_clock {n e e' a b c : Nat}
    (hclock : a * e = b * n + c) (h8 : 8 * e' = 9 * e + 5) :
    8 * a * e' = 9 * b * n + (9 * c + 5 * a) := by
  have hL : 8 * a * e' = a * (8 * e') := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hdist : a * (9 * e + 5) = a * (9 * e) + a * 5 := Nat.mul_add a (9 * e) 5
  have h9 : a * (9 * e) = 9 * (a * e) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h5 : a * 5 = 5 * a := Nat.mul_comm _ _
  have hdist2 : 9 * (b * n + c) = 9 * (b * n) + 9 * c := Nat.mul_add 9 (b * n) c
  have h9b : 9 * (b * n) = 9 * b * n := by simp [Nat.mul_assoc]
  calc
    8 * a * e' = a * (8 * e') := hL
    _ = a * (9 * e + 5) := by rw [h8]
    _ = a * (9 * e) + a * 5 := hdist
    _ = 9 * (a * e) + 5 * a := by rw [h9, h5]
    _ = 9 * (b * n + c) + 5 * a := by rw [hclock]
    _ = 9 * (b * n) + 9 * c + 5 * a := by rw [hdist2, Nat.add_assoc]
    _ = 9 * b * n + (9 * c + 5 * a) := by rw [h9b, Nat.add_assoc]

/-- Two-step clock: `64 e₂ = 81 n + 85`. -/
theorem two_light_clock {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2) :
    64 * e2 = 81 * n + 85 := by
  have h := compose_light_clock (one_light_clock h1) (one_light_clock h2)
  have ha : (8 : Nat) * 8 = 64 := by decide
  have hb : (9 : Nat) * 9 = 81 := by decide
  have hc : (9 : Nat) * 5 + 5 * 8 = 85 := by decide
  rw [ha, hb, hc] at h
  exact h

/-- Three-step clock: `512 e₃ = 729 n + 1085`. -/
theorem three_light_clock {n u e u2 e2 u3 e3 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) : 512 * e3 = 729 * n + 1085 := by
  have h := compose_light_clock (two_light_clock h1 h2) (one_light_clock h3)
  have ha : (8 : Nat) * 64 = 512 := by decide
  have hb : (9 : Nat) * 81 = 729 := by decide
  have hc : (9 : Nat) * 85 + 5 * 64 = 1085 := by decide
  rw [ha, hb, hc] at h
  exact h

/-- Four-step clock: `4096 e₄ = 6561 n + 12325`. -/
theorem four_light_clock {n u e u2 e2 u3 e3 u4 e4 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4) :
    4096 * e4 = 6561 * n + 12325 := by
  have h :=
    compose_light_clock (three_light_clock h1 h2 h3) (one_light_clock h4)
  have ha : (8 : Nat) * 512 = 4096 := by decide
  have hb : (9 : Nat) * 729 = 6561 := by decide
  have hc : (9 : Nat) * 1085 + 5 * 512 = 12325 := by decide
  rw [ha, hb, hc] at h
  exact h

/-- Five-step clock: `32768 e₅ = 59049 n + 131405`. -/
theorem five_light_clock {n u e u2 e2 u3 e3 u4 e4 u5 e5 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (h5 : IsExcursion e4 2 u5 1 e5) :
    32768 * e5 = 59049 * n + 131405 := by
  have h :=
    compose_light_clock (four_light_clock h1 h2 h3 h4) (one_light_clock h5)
  have ha : (8 : Nat) * 4096 = 32768 := by decide
  have hb : (9 : Nat) * 6561 = 59049 := by decide
  have hc : (9 : Nat) * 12325 + 5 * 4096 = 131405 := by decide
  rw [ha, hb, hc] at h
  exact h


/-! ## 5.  Compose a clock with a `W`-bound -/

/-- From `a e = b n + c` and `p e' ≤ q e + r`, the composite bound
`a p e' ≤ q b n + (q c + r a)`. -/
theorem compose_mul_bound {n e e' a b c p q r : Nat}
    (hclock : a * e = b * n + c) (hbound : p * e' ≤ q * e + r) :
    a * p * e' ≤ q * b * n + (q * c + r * a) := by
  have hL : a * p * e' = a * (p * e') := by simp [Nat.mul_assoc]
  have hmul : a * (p * e') ≤ a * (q * e + r) := Nat.mul_le_mul_left a hbound
  have hdist : a * (q * e + r) = a * (q * e) + a * r := Nat.mul_add a (q * e) r
  have hq : a * (q * e) = q * (a * e) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hr : a * r = r * a := Nat.mul_comm _ _
  have hdist2 : q * (b * n + c) = q * (b * n) + q * c := Nat.mul_add q (b * n) c
  have hqb : q * (b * n) = q * b * n := by simp [Nat.mul_assoc]
  calc
    a * p * e' = a * (p * e') := hL
    _ ≤ a * (q * e + r) := hmul
    _ = a * (q * e) + a * r := hdist
    _ = q * (a * e) + r * a := by rw [hq, hr]
    _ = q * (b * n + c) + r * a := by rw [hclock]
    _ = q * (b * n) + q * c + r * a := by rw [hdist2, Nat.add_assoc]
    _ = q * b * n + (q * c + r * a) := by rw [hqb, Nat.add_assoc]

/-- Equality form of `compose_mul_bound`. -/
theorem compose_mul_eq {n e e' a b c p q r : Nat}
    (hclock : a * e = b * n + c) (heq : p * e' = q * e + r) :
    a * p * e' = q * b * n + (q * c + r * a) := by
  have hL : a * p * e' = a * (p * e') := by simp [Nat.mul_assoc]
  have hdist : a * (q * e + r) = a * (q * e) + a * r := Nat.mul_add a (q * e) r
  have hq : a * (q * e) = q * (a * e) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hr : a * r = r * a := Nat.mul_comm _ _
  have hdist2 : q * (b * n + c) = q * (b * n) + q * c := Nat.mul_add q (b * n) c
  have hqb : q * (b * n) = q * b * n := by simp [Nat.mul_assoc]
  calc
    a * p * e' = a * (p * e') := hL
    _ = a * (q * e + r) := by rw [heq]
    _ = a * (q * e) + a * r := hdist
    _ = q * (a * e) + r * a := by rw [hq, hr]
    _ = q * (b * n + c) + r * a := by rw [hclock]
    _ = q * (b * n) + q * c + r * a := by rw [hdist2, Nat.add_assoc]
    _ = q * b * n + (q * c + r * a) := by rw [hqb, Nat.add_assoc]


/-! ## 6.  Integer comparisons for the contracting products -/

/-- `(9/8)² · (3/4) = 243/256`: `243 n + 319 < 256 n` once `n ≥ 123`
(every two-light rem-`1` start). -/
private theorem drop_coeff_two_one {n : Nat} (h : 123 ≤ n) :
    243 * n + 319 < 256 * n := by
  have h13 : 319 < 13 * n := by
    have hmin : 13 * 123 ≤ 13 * n := Nat.mul_le_mul_left 13 h
    have hnum : (319 : Nat) < 13 * 123 := by decide
    omega
  have hsum : (243 : Nat) + 13 = 256 := by decide
  have hsplit : 243 * n + 13 * n = 256 * n := by rw [← Nat.add_mul, hsum]
  omega

/-- `(9/8)³ · (3/8) = 2187/4096`: `2187 n + 3767 < 4096 n` once `n ≥ 11`. -/
private theorem drop_coeff_three_one {n : Nat} (h : 11 ≤ n) :
    2187 * n + 3767 < 4096 * n := by
  have h1909 : 3767 < 1909 * n := by
    have hmin : 1909 * 11 ≤ 1909 * n := Nat.mul_le_mul_left 1909 h
    have hnum : (3767 : Nat) < 1909 * 11 := by decide
    omega
  have hsum : (2187 : Nat) + 1909 = 4096 := by decide
  have hsplit : 2187 * n + 1909 * n = 4096 * n := by rw [← Nat.add_mul, hsum]
  omega

/-- `(9/8)³ · (9/16) = 6561/8192`. -/
private theorem drop_coeff_three_three {n : Nat} (h : 11 ≤ n) :
    6561 * n + 12325 < 8192 * n := by
  have h1631 : 12325 < 1631 * n := by
    have hmin : 1631 * 11 ≤ 1631 * n := Nat.mul_le_mul_left 1631 h
    have hnum : (12325 : Nat) < 1631 * 11 := by decide
    omega
  have hsum : (6561 : Nat) + 1631 = 8192 := by decide
  have hsplit : 6561 * n + 1631 * n = 8192 * n := by rw [← Nat.add_mul, hsum]
  omega

/-- `(9/8)⁴ · (9/16) = 59049/65536`.  Needs `n ≥ 21` (true of every
four-light rem-`3` start). -/
private theorem drop_coeff_four_three {n : Nat} (h : 21 ≤ n) :
    59049 * n + 131405 < 65536 * n := by
  have h6487 : 131405 < 6487 * n := by
    have hmin : 6487 * 21 ≤ 6487 * n := Nat.mul_le_mul_left 6487 h
    have hnum : (131405 : Nat) < 6487 * 21 := by decide
    omega
  have hsum : (59049 : Nat) + 6487 = 65536 := by decide
  have hsplit : 59049 * n + 6487 * n = 65536 * n := by
    rw [← Nat.add_mul, hsum]
  omega

/-- `(9/8)⁵ · (9/32) = 531441/1048576`. -/
private theorem drop_coeff_five_three {n : Nat} (h : 11 ≤ n) :
    531441 * n + 1346485 < 1048576 * n := by
  have h517135 : 1346485 < 517135 * n := by
    have hmin : 517135 * 11 ≤ 517135 * n := Nat.mul_le_mul_left 517135 h
    have hnum : (1346485 : Nat) < 517135 * 11 := by decide
    omega
  have hsum : (531441 : Nat) + 517135 = 1048576 := by decide
  have hsplit : 531441 * n + 517135 * n = 1048576 * n := by
    rw [← Nat.add_mul, hsum]
  omega


/-! ## 7.  Two lights then rem `1`: drops even at `W' = 1` -/

/-- **Two consecutive `(2, 1)` steps with remainder `1` drop below the
original start.**  The third excursion is `v = 1`; the `W = 1` upper
bound is already `(243 n + 319) / 256 < n`. -/
theorem lemmaX_of_two_light_then_one {n u e u2 e2 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (hrem : Val2 (e2 + 5) 1) (_hn : 1 < n) :
    ∃ e3 : Nat, ExChain n e3 ∧ e3 < n := by
  have he4 := e_one_mod_four hrem
  have he2odd : e2 % 2 = 1 := h2.2.2.1
  obtain ⟨v3, u3, W3, e3, hex3⟩ := exists_excursion he2odd
  have hv3 : v3 = 1 := (v_eq_one_iff hex3).mpr he4
  subst hv3
  have h4 := landing_upper_of_v_one hex3
  have h64 := two_light_clock h1 h2
  have h256 := compose_mul_bound h64 h4
  have hL : (64 : Nat) * 4 = 256 := by decide
  have hR : (3 : Nat) * 81 = 243 := by decide
  have hc : (3 : Nat) * 85 + 1 * 64 = 319 := by decide
  rw [hL, hR, hc] at h256
  have hfuel := two_light_then_one_fuel h1 h2 hrem
  have hn123 : 123 ≤ n := by
    have : (2 : Nat) ^ 7 ≤ n + 5 := Val2.le hfuel
    have hpow : (2 : Nat) ^ 7 = 128 := by decide
    omega
  have hcoeff := drop_coeff_two_one hn123
  have hdrop : e3 < n := by
    have : 256 * e3 < 256 * n := Nat.lt_of_le_of_lt h256 hcoeff
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨e3, ?_, hdrop⟩
  exact ExChain.cons ⟨2, u, 1, h1⟩
    (ExChain.cons ⟨2, u2, 1, h2⟩ (ExChain.one ⟨1, u3, W3, hex3⟩))


/-! ## 8.  Three lights then rem `1`: drop at `W' ≥ 2`, grow at `W' = 1` -/

/-- The `W' ≥ 2` comparison: `4096 e₄ ≤ 2187 n + 3767`. -/
theorem compose_three_one_W_two {n e3 e4 : Nat}
    (h512 : 512 * e3 = 729 * n + 1085) (h8 : 8 * e4 ≤ 3 * e3 + 1) :
    4096 * e4 ≤ 2187 * n + 3767 := by
  have h := compose_mul_bound h512 h8
  have hL : (512 : Nat) * 8 = 4096 := by decide
  have hR : (3 : Nat) * 729 = 2187 := by decide
  have hc : (3 : Nat) * 1085 + 1 * 512 = 3767 := by decide
  rw [hL, hR, hc] at h
  exact h

/-- **Three lights then rem `1` with `W' ≥ 2` drop.** -/
theorem lemmaX_of_three_light_then_one_heavy {n u e u2 e2 u3 e3 u4 W4 e4 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (_hrem : Val2 (e3 + 5) 1)
    (h4 : IsExcursion e3 1 u4 W4 e4) (hW : 2 ≤ W4) : e4 < n := by
  have h8 := landing_upper_of_v_one_W_ge_two h4 hW
  have h512 := three_light_clock h1 h2 h3
  have h4096 := compose_three_one_W_two h512 h8
  have hn11 := eleven_le_of_light h1
  have hcoeff := drop_coeff_three_one hn11
  have : 4096 * e4 < 4096 * n := Nat.lt_of_le_of_lt h4096 hcoeff
  exact Nat.lt_of_mul_lt_mul_left this

/-- Packaged Lemma X, assuming the next `v = 1` excursion is heavy. -/
theorem lemmaX_of_three_light_then_one {n u e u2 e2 u3 e3 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (hrem : Val2 (e3 + 5) 1) (_hn : 1 < n)
    (hheavy : ∀ u4 W4 e4 : Nat, IsExcursion e3 1 u4 W4 e4 → 2 ≤ W4) :
    ∃ e4 : Nat, ExChain n e4 ∧ e4 < n := by
  have he4 := e_one_mod_four hrem
  have he3odd : e3 % 2 = 1 := h3.2.2.1
  obtain ⟨v4, u4, W4, e4, hex4⟩ := exists_excursion he3odd
  have hv4 : v4 = 1 := (v_eq_one_iff hex4).mpr he4
  subst hv4
  have hW : 2 ≤ W4 := hheavy u4 W4 e4 hex4
  have hlt := lemmaX_of_three_light_then_one_heavy h1 h2 h3 hrem hex4 hW
  refine ⟨e4, ?_, hlt⟩
  exact ExChain.cons ⟨2, u, 1, h1⟩
    (ExChain.cons ⟨2, u2, 1, h2⟩
      (ExChain.cons ⟨2, u3, 1, h3⟩ (ExChain.one ⟨1, u4, W4, hex4⟩)))

/-- Exact `W' = 1` identity after three lights: `2048 e₄ = 2187 n + 3767`. -/
theorem compose_three_one_W_one_eq {n e3 e4 : Nat}
    (h512 : 512 * e3 = 729 * n + 1085) (h4 : 4 * e4 = 3 * e3 + 1) :
    2048 * e4 = 2187 * n + 3767 := by
  have h := compose_mul_eq h512 h4
  have hL : (512 : Nat) * 4 = 2048 := by decide
  have hR : (3 : Nat) * 729 = 2187 := by decide
  have hc : (3 : Nat) * 1085 + 1 * 512 = 3767 := by decide
  rw [hL, hR, hc] at h
  exact h

/-- **Growth law.**  Three lights then rem `1` with `W' = 1` satisfies
`n < e₄`.  The product `(9/8)³ · (3/4) = 2187/2048 > 1` is an identity,
not a special witness. -/
theorem grows_of_three_light_then_one_W_one {n u e u2 e2 u3 e3 u4 e4 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (_hrem : Val2 (e3 + 5) 1)
    (h4 : IsExcursion e3 1 u4 1 e4) : n < e4 := by
  have heq := landing_eq_of_v_one_W_one h4
  have h512 := three_light_clock h1 h2 h3
  have h2048 := compose_three_one_W_one_eq h512 heq
  have hn11 := eleven_le_of_light h1
  have hcoeff : 2048 * n < 2187 * n + 3767 := by
    have hsum : (2048 : Nat) + 139 = 2187 := by decide
    have hsplit : 2048 * n + 139 * n = 2187 * n := by rw [← Nat.add_mul, hsum]
    have hpos : 0 < 139 * n := by omega
    omega
  have : 2048 * n < 2048 * e4 := by
    rw [h2048]
    exact hcoeff
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy.**  After three `(2, 1)` steps with remainder `1`, the next
`v = 1` excursion either drops (`W' ≥ 2`) or grows (`W' = 1`). -/
theorem dichotomy_three_light_then_one {n u e u2 e2 u3 e3 u4 W4 e4 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (hrem : Val2 (e3 + 5) 1)
    (h4 : IsExcursion e3 1 u4 W4 e4) : (2 ≤ W4 ∧ e4 < n) ∨ (W4 = 1 ∧ n < e4) := by
  have hW1 : 1 ≤ W4 := IsExcursion.one_le_W h4
  rcases Nat.eq_or_lt_of_le hW1 with hW | hW
  · subst hW
    exact Or.inr ⟨rfl, grows_of_three_light_then_one_W_one h1 h2 h3 hrem h4⟩
  · have hW2 : 2 ≤ W4 := by omega
    exact Or.inl ⟨hW2, lemmaX_of_three_light_then_one_heavy h1 h2 h3 hrem h4 hW2⟩


/-! ## 9.  Three lights then rem `3`: drops at `W' ≥ 2` -/

theorem compose_three_three_W_two {n e3 e4 : Nat}
    (h512 : 512 * e3 = 729 * n + 1085) (h16 : 16 * e4 ≤ 9 * e3 + 5) :
    8192 * e4 ≤ 6561 * n + 12325 := by
  have h := compose_mul_bound h512 h16
  have hL : (512 : Nat) * 16 = 8192 := by decide
  have hR : (9 : Nat) * 729 = 6561 := by decide
  have hc : (9 : Nat) * 1085 + 5 * 512 = 12325 := by decide
  rw [hL, hR, hc] at h
  exact h

/-- **Three consecutive `(2, 1)` steps with remainder `3` drop.**  The
fourth excursion is `v = 2`, `W ≥ 2`; the `W = 2` upper bound is already
`(6561 n + 12325) / 8192 < n`. -/
theorem lemmaX_of_three_light_then_three {n u e u2 e2 u3 e3 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (hrem : Val2 (e3 + 5) 3) (_hn : 1 < n) :
    ∃ e4 : Nat, ExChain n e4 ∧ e4 < n := by
  have he16 := e_three_mod_sixteen hrem
  have he3odd : e3 % 2 = 1 := h3.2.2.1
  obtain ⟨v4, u4, W4, e4, hex4⟩ := exists_excursion he3odd
  have ⟨hv4, hW4⟩ := (v_two_W_ge_two_iff hex4).mpr he16
  have hv4' : v4 = 2 := hv4
  subst hv4'
  have h16 := landing_upper_of_v_two_W_ge_two hex4 hW4
  have h512 := three_light_clock h1 h2 h3
  have h8192 := compose_three_three_W_two h512 h16
  have hn11 := eleven_le_of_light h1
  have hcoeff := drop_coeff_three_three hn11
  have hdrop : e4 < n := by
    have : 8192 * e4 < 8192 * n := Nat.lt_of_le_of_lt h8192 hcoeff
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨e4, ?_, hdrop⟩
  exact ExChain.cons ⟨2, u, 1, h1⟩
    (ExChain.cons ⟨2, u2, 1, h2⟩
      (ExChain.cons ⟨2, u3, 1, h3⟩ (ExChain.one ⟨2, u4, W4, hex4⟩)))


/-! ## 10.  Four lights then rem `3`: drops at `W' ≥ 2` -/

theorem compose_four_three_W_two {n e4 e5 : Nat}
    (h4096 : 4096 * e4 = 6561 * n + 12325) (h16 : 16 * e5 ≤ 9 * e4 + 5) :
    65536 * e5 ≤ 59049 * n + 131405 := by
  have h := compose_mul_bound h4096 h16
  have hL : (4096 : Nat) * 16 = 65536 := by decide
  have hR : (9 : Nat) * 6561 = 59049 := by decide
  have hc : (9 : Nat) * 12325 + 5 * 4096 = 131405 := by decide
  rw [hL, hR, hc] at h
  exact h

/-- **Four consecutive `(2, 1)` steps with remainder `3` drop.** -/
theorem lemmaX_of_four_light_then_three {n u e u2 e2 u3 e3 u4 e4 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (hrem : Val2 (e4 + 5) 3) (_hn : 1 < n) :
    ∃ e5 : Nat, ExChain n e5 ∧ e5 < n := by
  have he16 := e_three_mod_sixteen hrem
  have he4odd : e4 % 2 = 1 := h4.2.2.1
  obtain ⟨v5, u5, W5, e5, hex5⟩ := exists_excursion he4odd
  have ⟨hv5, hW5⟩ := (v_two_W_ge_two_iff hex5).mpr he16
  have hv5' : v5 = 2 := hv5
  subst hv5'
  have h16 := landing_upper_of_v_two_W_ge_two hex5 hW5
  have h4096 := four_light_clock h1 h2 h3 h4
  have h65536 := compose_four_three_W_two h4096 h16
  have hfuel := four_light_then_three_fuel h1 h2 h3 h4 hrem
  have hn21 : 21 ≤ n := by
    have : (2 : Nat) ^ 15 ≤ n + 5 := Val2.le hfuel
    have hpow : (2 : Nat) ^ 15 = 32768 := by decide
    omega
  have hcoeff := drop_coeff_four_three hn21
  have hdrop : e5 < n := by
    have : 65536 * e5 < 65536 * n := Nat.lt_of_le_of_lt h65536 hcoeff
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨e5, ?_, hdrop⟩
  exact ExChain.cons ⟨2, u, 1, h1⟩
    (ExChain.cons ⟨2, u2, 1, h2⟩
      (ExChain.cons ⟨2, u3, 1, h3⟩
        (ExChain.cons ⟨2, u4, 1, h4⟩ (ExChain.one ⟨2, u5, W5, hex5⟩))))


/-! ## 11.  Five lights then rem `3`: drop at `W' ≥ 3`, grow at `W' = 2` -/

theorem compose_five_three_W_three {n e5 e6 : Nat}
    (h32768 : 32768 * e5 = 59049 * n + 131405)
    (h32 : 32 * e6 ≤ 9 * e5 + 5) :
    1048576 * e6 ≤ 531441 * n + 1346485 := by
  have h := compose_mul_bound h32768 h32
  have hL : (32768 : Nat) * 32 = 1048576 := by decide
  have hR : (9 : Nat) * 59049 = 531441 := by decide
  have hc : (9 : Nat) * 131405 + 5 * 32768 = 1346485 := by decide
  rw [hL, hR, hc] at h
  exact h

/-- **Five lights then rem `3` with `W' ≥ 3` drop.**  The threshold is
one extra halving past the `W' = 2` bound, whose product exceeds `1`. -/
theorem lemmaX_of_five_light_then_three_heavy
    {n u e u2 e2 u3 e3 u4 e4 u5 e5 u6 W6 e6 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (h5 : IsExcursion e4 2 u5 1 e5) (_hrem : Val2 (e5 + 5) 3)
    (h6 : IsExcursion e5 2 u6 W6 e6) (hW : 3 ≤ W6) : e6 < n := by
  have h32 := landing_upper_of_v_two_W_ge_three h6 hW
  have h32768 := five_light_clock h1 h2 h3 h4 h5
  have h1048576 := compose_five_three_W_three h32768 h32
  have hn11 := eleven_le_of_light h1
  have hcoeff := drop_coeff_five_three hn11
  have : 1048576 * e6 < 1048576 * n := Nat.lt_of_le_of_lt h1048576 hcoeff
  exact Nat.lt_of_mul_lt_mul_left this

/-- Packaged Lemma X, assuming the next `v = 2` excursion has `W' ≥ 3`. -/
theorem lemmaX_of_five_light_then_three
    {n u e u2 e2 u3 e3 u4 e4 u5 e5 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (h5 : IsExcursion e4 2 u5 1 e5) (hrem : Val2 (e5 + 5) 3) (_hn : 1 < n)
    (hheavy : ∀ u6 W6 e6 : Nat, IsExcursion e5 2 u6 W6 e6 → 3 ≤ W6) :
    ∃ e6 : Nat, ExChain n e6 ∧ e6 < n := by
  have he16 := e_three_mod_sixteen hrem
  have he5odd : e5 % 2 = 1 := h5.2.2.1
  obtain ⟨v6, u6, W6, e6, hex6⟩ := exists_excursion he5odd
  have ⟨hv6, _hW6⟩ := (v_two_W_ge_two_iff hex6).mpr he16
  have hv6' : v6 = 2 := hv6
  subst hv6'
  have hW : 3 ≤ W6 := hheavy u6 W6 e6 hex6
  have hlt :=
    lemmaX_of_five_light_then_three_heavy h1 h2 h3 h4 h5 hrem hex6 hW
  refine ⟨e6, ?_, hlt⟩
  exact ExChain.cons ⟨2, u, 1, h1⟩
    (ExChain.cons ⟨2, u2, 1, h2⟩
      (ExChain.cons ⟨2, u3, 1, h3⟩
        (ExChain.cons ⟨2, u4, 1, h4⟩
          (ExChain.cons ⟨2, u5, 1, h5⟩ (ExChain.one ⟨2, u6, W6, hex6⟩)))))

/-- Exact `W' = 2` identity after five lights:
`524288 e₆ = 531441 n + 1346485`. -/
theorem compose_five_three_W_two_eq {n e5 e6 : Nat}
    (h32768 : 32768 * e5 = 59049 * n + 131405)
    (h16 : 16 * e6 = 9 * e5 + 5) :
    524288 * e6 = 531441 * n + 1346485 := by
  have h := compose_mul_eq h32768 h16
  have hL : (32768 : Nat) * 16 = 524288 := by decide
  have hR : (9 : Nat) * 59049 = 531441 := by decide
  have hc : (9 : Nat) * 131405 + 5 * 32768 = 1346485 := by decide
  rw [hL, hR, hc] at h
  exact h

/-- `(9/8)⁵ · (9/16) = 531441/524288 > 1`, as an integer comparison. -/
private theorem grow_coeff_five_three (n : Nat) :
    524288 * n < 531441 * n + 1346485 := by
  have hle : (524288 : Nat) ≤ 531441 := by decide
  have hmul : 524288 * n ≤ 531441 * n := Nat.mul_le_mul_right n hle
  have hpos : 0 < (1346485 : Nat) := by decide
  have hlt : 531441 * n < 531441 * n + 1346485 := Nat.lt_add_of_pos_right hpos
  exact Nat.lt_of_le_of_lt hmul hlt

/-- **Growth law.**  Five lights then rem `3` with `W' = 2` satisfies
`n < e₆`.  The product `(9/8)⁵ · (9/16) = 531441/524288 > 1` is an
identity. -/
theorem grows_of_five_light_then_three_W_two
    {n u e u2 e2 u3 e3 u4 e4 u5 e5 u6 e6 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (h5 : IsExcursion e4 2 u5 1 e5) (_hrem : Val2 (e5 + 5) 3)
    (h6 : IsExcursion e5 2 u6 2 e6) : n < e6 := by
  have heq := landing_eq_of_v_two_W_two h6
  have h32768 := five_light_clock h1 h2 h3 h4 h5
  have h524288 := compose_five_three_W_two_eq h32768 heq
  have : 524288 * n < 524288 * e6 := h524288 ▸ grow_coeff_five_three n
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy.**  After five `(2, 1)` steps with remainder `3`, the next
`v = 2` excursion either drops (`W' ≥ 3`) or grows (`W' = 2`). -/
theorem dichotomy_five_light_then_three
    {n u e u2 e2 u3 e3 u4 e4 u5 e5 u6 W6 e6 : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (h3 : IsExcursion e2 2 u3 1 e3) (h4 : IsExcursion e3 2 u4 1 e4)
    (h5 : IsExcursion e4 2 u5 1 e5) (hrem : Val2 (e5 + 5) 3)
    (h6 : IsExcursion e5 2 u6 W6 e6) :
    (3 ≤ W6 ∧ e6 < n) ∨ (W6 = 2 ∧ n < e6) := by
  have he16 := e_three_mod_sixteen hrem
  have ⟨_, hW2⟩ := (v_two_W_ge_two_iff h6).mpr he16
  rcases Nat.eq_or_lt_of_le hW2 with hW | hW
  · subst hW
    exact Or.inr ⟨rfl, grows_of_five_light_then_three_W_two h1 h2 h3 h4 h5 hrem h6⟩
  · have hW3 : 3 ≤ W6 := by omega
    exact Or.inl ⟨hW3,
      lemmaX_of_five_light_then_three_heavy h1 h2 h3 h4 h5 hrem h6 hW3⟩


/-! ## 12.  Witnesses -/

set_option maxHeartbeats 800000

/-- `W' = 1` still drops after two lights: `379 → 427 → 481 → 361`.
Fuel: `v₂(379 + 5) = 7`. -/
theorem three_seventy_nine_two_light_then_one :
    IsExcursion 379 2 95 1 427 ∧
    IsExcursion 427 2 107 1 481 ∧
    Val2 (481 + 5) 1 ∧
    IsExcursion 481 1 241 1 361 ∧
    361 < 379 ∧
    Val2 (379 + 5) 7 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨243, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨3, rfl, rfl⟩⟩

/-- `W' = 1` grows after three lights: `3067 → 3451 → 3883 → 4369 → 3277`.
Fuel: `v₂(3067 + 5) = 10`. -/
theorem three_thousand_sixty_seven_three_light_then_one_grows :
    IsExcursion 3067 2 767 1 3451 ∧
    IsExcursion 3451 2 863 1 3883 ∧
    IsExcursion 3883 2 971 1 4369 ∧
    Val2 (4369 + 5) 1 ∧
    IsExcursion 4369 1 2185 1 3277 ∧
    3067 < 3277 ∧
    Val2 (3067 + 5) 10 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨2187, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨3, rfl, rfl⟩⟩

/-- `W' = 2` drops after three lights, rem `1`:
`1019 → 1147 → 1291 → 1453 → 545`. -/
theorem one_thousand_nineteen_three_light_then_one_drops :
    IsExcursion 1019 2 255 1 1147 ∧
    IsExcursion 1147 2 287 1 1291 ∧
    IsExcursion 1291 2 323 1 1453 ∧
    Val2 (1453 + 5) 1 ∧
    IsExcursion 1453 1 727 2 545 ∧
    545 < 1019 ∧
    Val2 (1019 + 5) 10 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨729, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨1, rfl, rfl⟩⟩

/-- `W' = 2` bound attained and still drops after three lights, rem `3`:
`12283 → 13819 → 15547 → 17491 → 9839`.  Fuel: `v₂(12283 + 5) = 12`. -/
theorem twelve_thousand_two_eighty_three_three_light_then_three :
    IsExcursion 12283 2 3071 1 13819 ∧
    IsExcursion 13819 2 3455 1 15547 ∧
    IsExcursion 15547 2 3887 1 17491 ∧
    Val2 (17491 + 5) 3 ∧
    IsExcursion 17491 2 4373 2 9839 ∧
    9839 < 12283 ∧
    Val2 (12283 + 5) 12 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨2187, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨3, rfl, rfl⟩⟩

/-- `W' = 2` bound attained and still drops after four lights, rem `3`:
`98299 → … → 157459 → 88571`.  Fuel: `v₂(98299 + 5) = 15`. -/
theorem ninety_eight_two_ninety_nine_four_light_then_three :
    IsExcursion 98299 2 24575 1 110587 ∧
    IsExcursion 110587 2 27647 1 124411 ∧
    IsExcursion 124411 2 31103 1 139963 ∧
    IsExcursion 139963 2 34991 1 157459 ∧
    Val2 (157459 + 5) 3 ∧
    IsExcursion 157459 2 39365 2 88571 ∧
    88571 < 98299 ∧
    Val2 (98299 + 5) 15 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨19683, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨3, rfl, rfl⟩⟩

/-- `W' = 2` grows after five lights, rem `3`:
`786427 → … → 1417171 → 797159`.  Fuel: `v₂(786427 + 5) = 18`. -/
theorem seven_eighty_six_four_twenty_seven_five_light_then_three_grows :
    IsExcursion 786427 2 196607 1 884731 ∧
    IsExcursion 884731 2 221183 1 995323 ∧
    IsExcursion 995323 2 248831 1 1119739 ∧
    IsExcursion 1119739 2 279935 1 1259707 ∧
    IsExcursion 1259707 2 314927 1 1417171 ∧
    Val2 (1417171 + 5) 3 ∧
    IsExcursion 1417171 2 354293 2 797159 ∧
    786427 < 797159 ∧
    Val2 (786427 + 5) 18 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨177147, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨3, rfl, rfl⟩⟩

/-- `W' = 3` drops after five lights, rem `3`:
`262139 → … → 472387 → 132859`.  Fuel: `v₂(262139 + 5) = 18`. -/
theorem two_sixty_two_one_thirty_nine_five_light_then_three_drops :
    IsExcursion 262139 2 65535 1 294907 ∧
    IsExcursion 294907 2 73727 1 331771 ∧
    IsExcursion 331771 2 82943 1 373243 ∧
    IsExcursion 373243 2 93311 1 419899 ∧
    IsExcursion 419899 2 104975 1 472387 ∧
    Val2 (472387 + 5) 3 ∧
    IsExcursion 472387 2 118097 3 132859 ∧
    132859 < 262139 ∧
    Val2 (262139 + 5) 18 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨59049, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega,
    ⟨1, rfl, rfl⟩⟩

end ExcursionLightK
end Collatz

section AxiomAudit
open Collatz.ExcursionLightK
#print axioms two_light_then_one_fuel
#print axioms three_light_then_one_fuel
#print axioms three_light_then_three_fuel
#print axioms four_light_then_three_fuel
#print axioms five_light_then_three_fuel
#print axioms one_light_clock
#print axioms two_light_clock
#print axioms three_light_clock
#print axioms four_light_clock
#print axioms five_light_clock
#print axioms lemmaX_of_two_light_then_one
#print axioms lemmaX_of_three_light_then_one_heavy
#print axioms grows_of_three_light_then_one_W_one
#print axioms dichotomy_three_light_then_one
#print axioms lemmaX_of_three_light_then_three
#print axioms lemmaX_of_four_light_then_three
#print axioms lemmaX_of_five_light_then_three_heavy
#print axioms grows_of_five_light_then_three_W_two
#print axioms dichotomy_five_light_then_three
end AxiomAudit
