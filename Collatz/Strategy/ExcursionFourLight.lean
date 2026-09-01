import Collatz.Strategy.ExcursionLTE

/-!
# The even-`v` light family, especially `(v, W) = (4, 1)`

`ExcursionLTE` names the leftover plus-five class `v₂ = 2`: `n ≡ 7 (mod 8)`,
opening run `v ≥ 3`.  That class includes every odd leftover *and* the even
light blocks `(4, 1), (5, 1), (6, 1), …`.  For even `v` the ultrametric
comparison with LTE (`v₂(3^v − 1) = v₂(v) + 2 ≥ 3`) reads `W = 1` off
`v₂(u − 1) = 1`, i.e. `u ≡ 3 (mod 4)`.

At `v = 4` this is `n ≡ 47 (mod 64)`: `n = 16u − 1` and

    `e = (81u − 1) / 2 = (81n + 65) / 32`.

The affine map `n ↦ (81n + 65)/32` has rational fixed point `−65/49`.  There
is therefore **no** `Nat` `c` with `32(e + c) = 81(n + c)` (obstruction
`49c = 65`).  The unique 2-adic clock, written without denominators, is

  `32(49e + 65) = 81(49n + 65)`.

Each `(4, 1)` step spends exactly five factors of two:

  `v₂(49n + 65) ≥ 6`,     `v₂(49e + 65) = v₂(49n + 65) − 5`.

The fuel is finite, so a single integer cannot take infinitely many `(4, 1)`
steps.  After one step the remainder `r − 5` reads the landing:

* `r = 6` → remainder `1` → `e ≡ 1 (mod 4)` → next `v = 1`
  (`W' ≥ 2` drops below the start; `W' = 1` grows: `47 → 121 → 91`);
* `r = 7` → remainder `2` → `e ≡ 3 (mod 8)` → next `v = 2`;
* `r = 8` → remainder `3` → `e ≡ 7 (mod 16)` → next `v = 3`;
* `r = 9` → remainder `4` → `e ≡ 31 (mod 32)` → next `v ≥ 5`;
* `r ≥ 11` is the only room for a second `(4, 1)` step.

The same fixed-point construction gives a clock for every even `v ≥ 2` with
`W = 1`: `A = 3^v − 2^{v+1}`, `B = 3^v − 2^v`, and

  `2^{v+1}(A e + B) = 3^v (A n + B)`.

At `v = 2` one has `A = 1`, `B = 5`, recovering the integer plus-five clock.
For even `v ≥ 4`, `A` does not divide `B` in `Nat`.

This does **not** prove Lemma X on the whole `(4, 1)` family, and does not
claim Collatz.
-/

namespace Collatz
namespace ExcursionFourLight

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap Collatz.ExcursionLTE


/-! ## 1.  Unpacking a single `(4, 1)` excursion -/

/-- The defining equations at `(v, W) = (4, 1)`. -/
theorem eqs_of_v_four_W_one {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    n + 1 = 16 * u ∧ 81 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 4 = 16 by decide] at hnu
  rw [show (3 : Nat) ^ 4 = 81 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

/-- **Start in cofactor coordinates.**  `v = 4` is `n = 16u − 1`. -/
theorem n_eq_of_v_four_W_one {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    n = 16 * u - 1 := by
  have ⟨hnu, _⟩ := eqs_of_v_four_W_one h
  omega

/-- `W = 1` with even `v = 4` forces `u ≡ 3 (mod 4)`. -/
theorem u_three_mod_four_of_v_four_W_one {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) : u % 4 = 3 := by
  have ⟨_, hpeak⟩ := eqs_of_v_four_W_one h
  have he : e % 2 = 1 := h.2.2.1
  have : (81 * u) % 4 = 3 := by omega
  have : (81 : Nat) % 4 = 1 := by decide
  have hmul : (81 * u) % 4 = (1 * (u % 4)) % 4 := by
    rw [Nat.mul_mod, this]
  omega

/-- A single `(4, 1)` step is strictly expanding. -/
theorem v_four_W_one_grows {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    n < e := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_four_W_one h
  omega


/-! ## 2.  Exact one-step landing -/

/-- **The one-step light map in the cofactor.**  For `n = 16u − 1` with
`(v, W) = (4, 1)`, the landing is `(81u − 1) / 2`. -/
theorem landing_u_of_v_four_W_one {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    e = (81 * u - 1) / 2 := by
  have ⟨_, hpeak⟩ := eqs_of_v_four_W_one h
  have hsub : 81 * u - 1 = 2 * e := by omega
  rw [hsub]
  exact (Nat.mul_div_cancel_left e (by omega : 0 < 2)).symm

/-- **The one-step light map in `n`.**  Affine form `(81/32) n + 65/32`. -/
theorem landing_n_of_v_four_W_one {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    e = (81 * n + 65) / 32 := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_four_W_one h
  have h32 : 32 * e = 81 * n + 65 := by omega
  have : 81 * n + 65 = 32 * e := h32.symm
  rw [this]
  exact (Nat.mul_div_cancel_left e (by omega : 0 < 32)).symm


/-! ## 3.  No integer clock; the unique 2-adic clock, written integrally -/

/-- Any putative integer clock `32(e + c) = 81(n + c)` forces `49c = 65`. -/
theorem clock_forces_forty_nine_c {n u e c : Nat} (h : IsExcursion n 4 u 1 e)
    (heq : 32 * (e + c) = 81 * (n + c)) : 49 * c = 65 := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_four_W_one h
  omega

/-- **Negative theorem.**  There is no `Nat` `c > 0` with
`32(e + c) = 81(n + c)` on a `(4, 1)` excursion.  The obstruction is
`49c = 65` (which also rules out `c = 0`). -/
theorem no_nat_clock {n u e c : Nat} (h : IsExcursion n 4 u 1 e)
    (_hc : 0 < c) : 32 * (e + c) ≠ 81 * (n + c) := by
  intro heq
  have := clock_forces_forty_nine_c h heq
  omega

/-- `47 ↦ 121` is a `(4, 1)` excursion. -/
theorem forty_seven_is_v_four_W_one : IsExcursion 47 4 3 1 121 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

/-- The same obstruction at the seed `47 ↦ 121`. -/
theorem forty_seven_no_clock {c : Nat} (hc : 0 < c) :
    32 * (121 + c) ≠ 81 * (47 + c) :=
  no_nat_clock forty_seven_is_v_four_W_one hc

/-- **The unique rational / 2-adic clock**, cleared of the denominator `49`.
This is `32(e + 65/49) = 81(n + 65/49)`, not an integer-`c` identity. -/
theorem two_adic_clock {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    32 * (49 * e + 65) = 81 * (49 * n + 65) := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_four_W_one h
  omega


/-! ## 4.  Cofactor form, and the residue `n ≡ 47 (mod 64)` -/

/-- Every `(4, 1)` cofactor is `u = 4k + 3`. -/
theorem exists_k_of_v_four_W_one {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    ∃ k : Nat, u = 4 * k + 3 := by
  have hu4 := u_three_mod_four_of_v_four_W_one h
  exact ⟨u / 4, (Nat.div_add_mod u 4).symm.trans (by rw [hu4])⟩

/-- **Exact next residue.**  On `u = 4k + 3` the landing is `162k + 121`. -/
theorem landing_of_u_three_mod_four {n k e : Nat}
    (h : IsExcursion n 4 (4 * k + 3) 1 e) : e = 162 * k + 121 := by
  have ⟨_, hpeak⟩ := eqs_of_v_four_W_one h
  omega

/-- The start is `n ≡ 47 (mod 64)`. -/
theorem n_forty_seven_mod_sixty_four {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) : n % 64 = 47 := by
  obtain ⟨k, hk⟩ := exists_k_of_v_four_W_one h
  have hn : n = 16 * u - 1 := n_eq_of_v_four_W_one h
  subst hk
  omega


/-! ## 5.  Scaling lemmas for the clock -/

/-- Scaling by `81` does not change the valuation. -/
private theorem val2_eighty_one_mul {x r : Nat} (h : Val2 x r) :
    Val2 (81 * x) r := by
  have h81 : Val2 (81 : Nat) 0 := Val2.of_odd (by decide)
  have := Val2.mul h81 h
  simpa using this

/-- The odd factor `81` can be cancelled. -/
private theorem val2_of_eighty_one_mul {x r : Nat}
    (hx : 0 < x) (h : Val2 (81 * x) r) : Val2 x r := by
  obtain ⟨s, hs⟩ := Val2.exists_of_pos hx
  exact (Val2.unique (val2_eighty_one_mul hs) h) ▸ hs

/-- Scaling by `32 = 2 ^ 5` raises the valuation by exactly five. -/
private theorem val2_thirty_two_mul {x r : Nat} (h : Val2 x r) :
    Val2 (32 * x) (r + 5) := by
  have h32 : (32 : Nat) = 2 ^ 5 := by decide
  rw [h32]
  have := Val2.two_pow_mul h 5
  simpa [Nat.add_comm] using this


/-! ## 6.  Fuel lower bound, and the countdown -/

/-- Every `(4, 1)` start has `64 ∣ 49n + 65`. -/
theorem sixty_four_dvd {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    64 ∣ 49 * n + 65 := by
  obtain ⟨k, hk⟩ := exists_k_of_v_four_W_one h
  have hn : n = 16 * u - 1 := n_eq_of_v_four_W_one h
  subst hk
  -- `49(16(4k+3) − 1) + 65 = 64(49k + 37)`
  omega

/-- **Fuel ≥ 6.**  Every `(4, 1)` excursion has `v₂(49n + 65) ≥ 6`.
Remainder `5` is impossible: `49e + 65` is always even for odd `e`, so
the countdown never lands on valuation `0`, and a start of fuel `5`
would. -/
theorem val2_ge_six {n u e r : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) r) : 6 ≤ r := by
  have hdvd := sixty_four_dvd h
  have hpow : (2 : Nat) ^ 6 = 64 := by decide
  exact (Val2.dvd_iff_le hr).mp (hpow ▸ hdvd)

/-- **Fuel identity.**  The clock shifts the valuation of `49· + 65` by `−5`. -/
theorem val2_forty_nine_shift {n u e r : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * e + 65) r) :
    Val2 (49 * n + 65) (r + 5) := by
  have hclock := two_adic_clock h
  have h32 := val2_thirty_two_mul hr
  have hpos : 0 < 49 * n + 65 := by
    have : 0 < 32 * (49 * e + 65) := Val2.pos h32
    omega
  have h81 : Val2 (81 * (49 * n + 65)) (r + 5) := hclock ▸ h32
  exact val2_of_eighty_one_mul hpos h81

/-- **Countdown.**  One `(4, 1)` step spends exactly five factors of two. -/
theorem val2_landing {n u e r : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) r) :
    Val2 (49 * e + 65) (r - 5) := by
  have hge := val2_ge_six h hr
  obtain ⟨s, hs⟩ := Val2.exists_of_pos (by omega : 0 < 49 * e + 65)
  have hr' := val2_forty_nine_shift h hs
  have heq : s + 5 = r := Val2.unique hr' hr
  have : s = r - 5 := by omega
  rwa [this] at hs

/-- The fuel strictly decreases. -/
theorem fuel_lt {n u e r : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) r) :
    r - 5 < r := by
  have := val2_ge_six h hr
  omega


/-! ## 7.  A second `(4, 1)` step needs fuel `≥ 11` -/

/-- If `v₂(49n + 65) < 11`, the landing is not another `(4, 1)` excursion. -/
theorem not_second_light {n u e r u2 e2 : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) r) (hlt : r < 11) :
    ¬ IsExcursion e 4 u2 1 e2 := by
  intro h2
  have hs := val2_landing h hr
  have h6 := val2_ge_six h2 hs
  omega

/-- Two consecutive `(4, 1)` steps force `v₂(49n + 65) ≥ 11`.  Fuel drops
by `5` at each step from a finite start, so only finitely many consecutive
`(4, 1)` iterates are possible. -/
theorem two_light_fuel {n u e u2 e2 r : Nat}
    (h1 : IsExcursion n 4 u 1 e) (h2 : IsExcursion e 4 u2 1 e2)
    (hr : Val2 (49 * n + 65) r) : 11 ≤ r := by
  have hs := val2_landing h1 hr
  have := val2_ge_six h2 hs
  omega


/-! ## 8.  Exit letters after one leftover step -/

/-- Remainder `1`: `v₂(49n + 65) = 6` lands on `e ≡ 1 (mod 4)`. -/
theorem exit_one_mod_four {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 6) :
    e % 4 = 1 := by
  have hs : Val2 (49 * e + 65) 1 := by
    have := val2_landing h hr
    simpa using this
  have : (49 * e + 65) % 4 = 2 := Val2.one_iff.mp hs
  omega

/-- That remainder-`1` landing is next run `v = 1`. -/
theorem exit_one_is_v_one {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 6)
    (h' : IsExcursion e v' u' W' e') : v' = 1 :=
  (v_eq_one_iff h').mpr (exit_one_mod_four h hr)

/-- Remainder `2`: `v₂(49n + 65) = 7` lands on `e ≡ 3 (mod 8)`. -/
theorem exit_three_mod_eight {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 7) :
    e % 8 = 3 := by
  have hs : Val2 (49 * e + 65) 2 := by
    have := val2_landing h hr
    simpa using this
  have : (49 * e + 65) % 8 = 4 := Val2.two_iff.mp hs
  omega

/-- That remainder-`2` landing is next run `v = 2`. -/
theorem exit_two_is_v_two {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 7)
    (h' : IsExcursion e v' u' W' e') : v' = 2 :=
  (v_eq_two_iff h').mpr (exit_three_mod_eight h hr)

/-- Remainder `3`: `v₂(49n + 65) = 8` lands on `e ≡ 7 (mod 16)`. -/
theorem exit_seven_mod_sixteen {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 8) :
    e % 16 = 7 := by
  have hs : Val2 (49 * e + 65) 3 := by
    have := val2_landing h hr
    simpa using this
  have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
  have : (49 * e + 65) % 16 = 8 := by
    have := Val2.mod hs
    rwa [hpow] at this
  omega

/-- That remainder-`3` landing is next run `v = 3`. -/
theorem exit_three_is_v_three {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 8)
    (h' : IsExcursion e v' u' W' e') : v' = 3 := by
  have h16 := exit_seven_mod_sixteen h hr
  have hval := val2_succ_of h'
  have hmod : (e + 1) % 16 = 8 := by omega
  have h3 : Val2 (e + 1) 3 := by
    refine Val2.of_mod ?_
    have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
    rwa [hpow]
  exact Val2.unique hval h3

/-- `17` is its own inverse modulo `32`. -/
private theorem seventeen_inv_mod_thirty_two {e : Nat}
    (h : (17 * e + 1) % 32 = 16) : e % 32 = 31 := by
  have h15 : (17 * e) % 32 = 15 := by omega
  have hL : (17 * (17 * e)) % 32 = e % 32 := by
    have h289 : (17 : Nat) * 17 = 289 := by decide
    have : 17 * (17 * e) = 289 * e := by rw [← Nat.mul_assoc, h289]
    rw [this, Nat.mul_mod]
    have : (289 : Nat) % 32 = 1 := by decide
    rw [this, Nat.one_mul, Nat.mod_mod]
  have hR : (17 * (17 * e)) % 32 = (17 * 15) % 32 := by
    rw [Nat.mul_mod]
    have : (17 : Nat) % 32 = 17 := by decide
    rw [this, h15]
  have : (17 * 15 : Nat) % 32 = 31 := by decide
  omega

/-- Remainder `4`: `v₂(49n + 65) = 9` lands on `e ≡ 31 (mod 32)`. -/
theorem exit_thirty_one_mod_thirty_two {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 9) :
    e % 32 = 31 := by
  have hs : Val2 (49 * e + 65) 4 := by
    have := val2_landing h hr
    simpa using this
  have hpow : (2 : Nat) ^ (4 + 1) = 32 := by decide
  have h32 : (49 * e + 65) % 32 = 16 := by
    have := Val2.mod hs
    rwa [hpow] at this
  have : (17 * e + 1) % 32 = 16 := by
    have h49 : (49 : Nat) % 32 = 17 := by decide
    have h65 : (65 : Nat) % 32 = 1 := by decide
    have hL : (49 * e + 65) % 32 =
        ((49 % 32 * (e % 32)) % 32 + 65 % 32) % 32 := by
      rw [Nat.add_mod, Nat.mul_mod]
    have hR : (17 * e + 1) % 32 =
        ((17 % 32 * (e % 32)) % 32 + 1 % 32) % 32 := by
      rw [Nat.add_mod, Nat.mul_mod]
    have : (17 : Nat) % 32 = 17 := by decide
    have : (1 : Nat) % 32 = 1 := by decide
    omega
  exact seventeen_inv_mod_thirty_two this

/-- That remainder-`4` landing has next run `v ≥ 5`. -/
theorem exit_four_v_ge_five {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 9)
    (h' : IsExcursion e v' u' W' e') : 5 ≤ v' := by
  have h32 := exit_thirty_one_mod_thirty_two h hr
  have hval := val2_succ_of h'
  have hdvd : 32 ∣ e + 1 := by omega
  have hpow : (2 : Nat) ^ 5 = 32 := by decide
  exact (Val2.dvd_iff_le hval).mp (hpow ▸ hdvd)


/-! ## 9.  Two-step drop: `(4, 1)` then `v = 1` with heavy `W'` -/

/-- Bridge: `4 u' = 81 u + 1` when the landing has `v' = 1`. -/
theorem four_u'_of_v_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (h' : IsExcursion e 1 u' W' e') :
    4 * u' = 81 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_four_W_one h
  have hnu' : e + 1 = 2 * u' := by
    have := h'.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  omega

/-- Crude bound: `W ≥ 2` on a `v = 1` excursion gives `4 e' ≤ 3 u' − 1`. -/
theorem four_e'_le_v_one {e u' W' e' : Nat}
    (h' : IsExcursion e 1 u' W' e') (hW : 2 ≤ W') :
    4 * e' ≤ 3 * u' - 1 := by
  have hpeak : 3 * u' = 2 ^ W' * e' + 1 := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one] at this
    exact this
  have hsub : 3 * u' - 1 = 2 ^ W' * e' := by omega
  have h4 : 4 ≤ 2 ^ W' := by
    have : (2 : Nat) ^ 2 ≤ 2 ^ W' := two_pow_le_two_pow hW
    simpa using this
  have : 4 * e' ≤ 2 ^ W' * e' := Nat.mul_le_mul_right e' h4
  omega

/-- **The integer comparison.**  `3 u' − 1 < 4 (16 u − 1)` when
`4 u' = 81 u + 1` and `u ≥ 3`. -/
private theorem second_lt_aux {u u' : Nat}
    (hu : 3 ≤ u) (hrel : 4 * u' = 81 * u + 1) :
    3 * u' - 1 < 4 * (16 * u - 1) := by
  have h12 : 12 * u' = 243 * u + 3 := by
    have : 12 * u' = 3 * (4 * u') := by
      have h : (12 : Nat) = 3 * 4 := by decide
      rw [h, Nat.mul_assoc]
    rw [this, hrel]
    omega
  have hL : 4 * (3 * u' - 1) = 12 * u' - 4 := by omega
  have hR : 4 * (4 * (16 * u - 1)) = 256 * u - 16 := by omega
  have hcmp : 12 * u' - 4 < 256 * u - 16 := by
    rw [h12]
    have : 243 * u + 3 - 4 = 243 * u - 1 := by omega
    have : 15 < 13 * u := by
      have : 13 * 3 ≤ 13 * u := Nat.mul_le_mul_left 13 hu
      omega
    omega
  have : 4 * (3 * u' - 1) < 4 * (4 * (16 * u - 1)) := by
    rw [hL, hR]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Lemma X on `(4, 1)` landings of clock-valuation `6` with `W' ≥ 2`.**
The second excursion is `v = 1` with at least two extra halvings, and lands
below the original start. -/
theorem lemmaX_of_v_four_land_one_heavy {n u e u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e)
    (h' : IsExcursion e 1 u' W' e') (hW : 2 ≤ W') (_hn : 1 < n) :
    e' < n := by
  have hu : 3 ≤ u := by
    have hu4 := u_three_mod_four_of_v_four_W_one h
    omega
  have hrel : 4 * u' = 81 * u + 1 := four_u'_of_v_one h h'
  have hbound := four_e'_le_v_one h' hW
  have hlt : 3 * u' - 1 < 4 * (16 * u - 1) := second_lt_aux hu hrel
  have hn_eq : n = 16 * u - 1 := n_eq_of_v_four_W_one h
  have hmid : 3 * u' - 1 < 4 * n := by
    rwa [hn_eq]
  have : 4 * e' < 4 * n := Nat.lt_of_le_of_lt hbound hmid
  exact Nat.lt_of_mul_lt_mul_left this

/-- Packaged as a Lemma X witness, from remainder-`1` fuel and a heavy
next extra-halving count. -/
theorem lemmaX_of_v_four_land_one {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) (hr : Val2 (49 * n + 65) 6) (hn : 1 < n)
    (hheavy : ∀ u' W' e' : Nat, IsExcursion e 1 u' W' e' → 2 ≤ W') :
    ∃ e' : Nat, ExChain n e' ∧ e' < n := by
  have he4 := exit_one_mod_four h hr
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have hv' : v' = 1 := (v_eq_one_iff h').mpr he4
  have h'1 : IsExcursion e 1 u' W' e' := hv' ▸ h'
  have hW : 2 ≤ W' := hheavy u' W' e' h'1
  have hlt := lemmaX_of_v_four_land_one_heavy h h'1 hW hn
  exact ⟨e', ExChain.cons ⟨4, u, 1, h⟩ (ExChain.one ⟨v', u', W', h'⟩), hlt⟩


/-! ## 10.  `W' = 1` always grows past the original start -/

/-- When `W' = 1`, the landing is `(3 u' − 1)/2`. -/
theorem landing_of_W_one {e u' e' : Nat}
    (h' : IsExcursion e 1 u' 1 e') : 2 * e' + 1 = 3 * u' := by
  have := h'.2.2.2.2.2.2
  rw [Nat.pow_one, Nat.pow_one] at this
  exact this.symm

/-- **Negative law.**  `(4, 1)` then remainder `1` with `W' = 1` satisfies
`n < e'`.  The second landing is `(243 u − 1)/8`, strictly above `16 u − 1`. -/
theorem grows_of_v_four_land_one_light {n u e u' e' : Nat}
    (h : IsExcursion n 4 u 1 e)
    (h' : IsExcursion e 1 u' 1 e') : n < e' := by
  have hrel : 4 * u' = 81 * u + 1 := four_u'_of_v_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := landing_of_W_one h'
  have hn_eq : n = 16 * u - 1 := n_eq_of_v_four_W_one h
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hsum : 8 * e' + 4 = 12 * u' := by omega
  have h12 : 12 * u' = 3 * (4 * u') := by
    have : (12 : Nat) = 3 * 4 := by decide
    rw [this, Nat.mul_assoc]
  have h3 : 8 * e' + 4 = 3 * (81 * u + 1) := by
    rw [hsum, h12, hrel]
  have h243 : 3 * (81 * u + 1) = 243 * u + 3 := by
    have hc : (3 : Nat) * 81 = 243 := by decide
    rw [Nat.mul_add, ← Nat.mul_assoc, hc]
  have heq : 8 * e' + 4 = 243 * u + 3 := h3.trans h243
  have h8e : 8 * e' = 243 * u - 1 := by
    have hpos : 1 ≤ 243 * u := Nat.mul_le_mul (by omega : 1 ≤ 243) hu
    have hR : 243 * u - 1 + 4 = 243 * u + 3 := by omega
    have : 8 * e' + 4 = 243 * u - 1 + 4 := heq.trans hR.symm
    exact Nat.add_right_cancel this
  have hn8 : 8 * n = 128 * u - 8 := by
    rw [hn_eq]
    have hpos : 1 ≤ 16 * u := Nat.mul_le_mul (by omega : 1 ≤ 16) hu
    have h128 : (8 : Nat) * 16 = 128 := by decide
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.mul_assoc, h128]
  have hcmp : 128 * u - 8 < 243 * u - 1 := by
    have hposL : 8 ≤ 128 * u := Nat.mul_le_mul (by omega : 8 ≤ 128) hu
    have hposR : 1 ≤ 243 * u := Nat.mul_le_mul (by omega : 1 ≤ 243) hu
    omega
  have : 8 * n < 8 * e' := by
    rw [hn8, h8e]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy.**  After `(4, 1)` with remainder `1`, the next `v = 1`
excursion either drops below the start (`W' ≥ 2`) or grows past it
(`W' = 1`). -/
theorem dichotomy_land_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (_hr : Val2 (49 * n + 65) 6)
    (h' : IsExcursion e 1 u' W' e') (hn : 1 < n) :
    (2 ≤ W' ∧ e' < n) ∨ (W' = 1 ∧ n < e') := by
  have hW1 : 1 ≤ W' := IsExcursion.one_le_W h'
  rcases Nat.eq_or_lt_of_le hW1 with hW | hW
  · subst hW
    exact Or.inr ⟨rfl, grows_of_v_four_land_one_light h h'⟩
  · have h2 : 2 ≤ W' := by omega
    exact Or.inl ⟨h2, lemmaX_of_v_four_land_one_heavy h h' h2 hn⟩


/-! ## 11.  Witnesses -/

/-- Fuel `6`, remainder `1`, `W' = 1` grows: `47 → 121 → 91`. -/
theorem forty_seven_fuel_grows :
    IsExcursion 47 4 3 1 121 ∧
    Val2 (49 * 47 + 65) 6 ∧
    IsExcursion 121 1 61 1 91 ∧
    47 < 91 :=
  ⟨forty_seven_is_v_four_W_one, ⟨37, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Fuel `6`, remainder `1`, `W' ≥ 2` drops: `175 → 445 → 167`. -/
theorem one_seventy_five_fuel_drops :
    IsExcursion 175 4 11 1 445 ∧
    Val2 (49 * 175 + 65) 6 ∧
    IsExcursion 445 1 223 2 167 ∧
    167 < 175 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨135, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Fuel `7`, remainder `2`: `111 → 283 ≡ 3 (mod 8)`. -/
theorem one_eleven_fuel :
    IsExcursion 111 4 7 1 283 ∧ Val2 (49 * 111 + 65) 7 ∧ 283 % 8 = 3 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨43, rfl, rfl⟩, rfl⟩

/-- Fuel `8`, remainder `3`: `495 → 1255 ≡ 7 (mod 16)`. -/
theorem four_ninety_five_fuel :
    IsExcursion 495 4 31 1 1255 ∧ Val2 (49 * 495 + 65) 8 ∧ 1255 % 16 = 7 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨95, rfl, rfl⟩, rfl⟩

/-- Fuel `9`, remainder `4`: `239 → 607 ≡ 31 (mod 32)`. -/
theorem two_thirty_nine_fuel :
    IsExcursion 239 4 15 1 607 ∧ Val2 (49 * 239 + 65) 9 ∧ 607 % 32 = 31 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨23, rfl, rfl⟩, rfl⟩

/-- Fuel `12` permits a second `(4, 1)`: `751 → 1903`. -/
theorem seven_fifty_one_two_light :
    IsExcursion 751 4 47 1 1903 ∧
    IsExcursion 1903 4 119 1 4819 ∧
    Val2 (49 * 751 + 65) 12 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨9, rfl, rfl⟩⟩

/-- Sanity: the closed form on the two seed witnesses. -/
theorem landing_closed_form_on_witnesses :
    (81 * 47 + 65) / 32 = 121 ∧ (81 * 175 + 65) / 32 = 445 := by
  decide


/-! ## 12.  General even `v`, `W = 1`: the same fixed-point clock -/

private theorem three_pow_odd (k : Nat) : (3 : Nat) ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

private theorem two_pow_even {k : Nat} (hk : 1 ≤ k) : (2 : Nat) ^ k % 2 = 0 := by
  have : k = (k - 1) + 1 := by omega
  rw [this, two_pow_succ]
  omega

/-- Clock numerator: `A = 3^v − 2^{v+1}`, the denominator of the fixed point. -/
def clockA (v : Nat) : Nat := 3 ^ v - 2 ^ (v + 1)

/-- Clock translation: `B = 3^v − 2^v`. -/
def clockB (v : Nat) : Nat := 3 ^ v - 2 ^ v

/-- At `v = 2` this is the plus-five clock: `A = 1`, `B = 5`. -/
theorem clockAB_two : clockA 2 = 1 ∧ clockB 2 = 5 := by decide

/-- At `v = 4` this is the `(4, 1)` clock: `A = 49`, `B = 65`. -/
theorem clockAB_four : clockA 4 = 49 ∧ clockB 4 = 65 := by decide

/-- `2^{v+1} < 3^v` for `v ≥ 2`: the even power of two cannot equal the odd
power of three. -/
theorem two_pow_succ_lt_three_pow {v : Nat} (hv : 2 ≤ v) :
    2 ^ (v + 1) < 3 ^ v := by
  have hle := two_pow_succ_le_three_pow hv
  have hne : 2 ^ (v + 1) ≠ 3 ^ v := by
    intro heq
    have heven : 2 ^ (v + 1) % 2 = 0 := two_pow_even (by omega)
    have hodd : 3 ^ v % 2 = 1 := three_pow_odd v
    omega
  omega

/-- The affine identity `2^{v+1} e = 3^v n + (3^v − 2^v)` on even-`v` light. -/
theorem landing_n_of_even_v_W_one {n v u e : Nat}
    (h : IsExcursion n v u 1 e) (_hv : 2 ≤ v) :
    2 ^ (v + 1) * e = 3 ^ v * n + (3 ^ v - 2 ^ v) := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [Nat.pow_one] at hpeak
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hsv : 1 ≤ 2 ^ v := one_le_two_pow v
  have hn : n = 2 ^ v * u - 1 := by
    have : n + 1 = 2 ^ v * u := hnu
    omega
  have he : 2 * e = 3 ^ v * u - 1 := by omega
  have hB : 2 ^ v ≤ 3 ^ v := two_pow_le_three_pow v
  have hL : 2 ^ (v + 1) * e = 2 ^ v * (3 ^ v * u - 1) := by
    have h2 : 2 ^ (v + 1) = 2 * 2 ^ v := two_pow_succ v
    rw [h2, Nat.mul_assoc, Nat.mul_left_comm, he]
  have hL2 : 2 ^ v * (3 ^ v * u - 1) = 2 ^ v * 3 ^ v * u - 2 ^ v := by
    have hle : 2 ^ v ≤ 2 ^ v * (3 ^ v * u) :=
      Nat.le_mul_of_pos_right _ (by omega)
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_assoc]
  have hR : 3 ^ v * n + (3 ^ v - 2 ^ v) =
      3 ^ v * (2 ^ v * u - 1) + (3 ^ v - 2 ^ v) := by rw [hn]
  have hR2 : 3 ^ v * (2 ^ v * u - 1) + (3 ^ v - 2 ^ v) =
      3 ^ v * 2 ^ v * u - 2 ^ v := by
    have hsub : 3 ^ v * (2 ^ v * u - 1) = 3 ^ v * 2 ^ v * u - 3 ^ v := by
      have hle : 3 ^ v ≤ 3 ^ v * (2 ^ v * u) :=
        Nat.le_mul_of_pos_right _ (by
          have : 1 ≤ 2 ^ v * u := Nat.mul_le_mul hsv hu
          omega)
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_assoc]
    have h3le : 3 ^ v ≤ 3 ^ v * 2 ^ v * u := by
      have : 1 ≤ 2 ^ v * u := Nat.mul_le_mul hsv hu
      have := Nat.le_mul_of_pos_right (3 ^ v) this
      simpa [Nat.mul_assoc] using this
    have hcancel : 3 ^ v * 2 ^ v * u - 3 ^ v + (3 ^ v - 2 ^ v) =
        3 ^ v * 2 ^ v * u - 2 ^ v := by
      omega
    rw [hsub, hcancel]
  have hcomm : 2 ^ v * 3 ^ v * u = 3 ^ v * 2 ^ v * u := by
    rw [Nat.mul_comm (2 ^ v), Nat.mul_assoc]
  rw [hL, hL2, hR, hR2, hcomm]

/-- **The general even-`v` light clock.**  Fixed point `−B/A`, cleared of
the (odd) denominator `A`. -/
theorem two_adic_clock_even_v {n v u e : Nat}
    (h : IsExcursion n v u 1 e) (hv : 2 ≤ v) :
    2 ^ (v + 1) * (clockA v * e + clockB v) =
      3 ^ v * (clockA v * n + clockB v) := by
  have hland := landing_n_of_even_v_W_one h hv
  have hA : 2 ^ (v + 1) ≤ 3 ^ v := two_pow_succ_le_three_pow hv
  have hsum : clockA v + 2 ^ (v + 1) = 3 ^ v := Nat.sub_add_cancel hA
  have hdist :
      2 ^ (v + 1) * (clockA v * e + clockB v) =
        clockA v * (2 ^ (v + 1) * e) + 2 ^ (v + 1) * clockB v := by
    rw [Nat.mul_add, Nat.mul_left_comm (2 ^ (v + 1)) (clockA v)]
  rw [hdist, hland, Nat.mul_add]
  have hBdef : 3 ^ v - 2 ^ v = clockB v := rfl
  rw [hBdef]
  have h1 : clockA v * (3 ^ v * n) = 3 ^ v * (clockA v * n) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (clockA v), Nat.mul_assoc]
  have h2 : clockA v * clockB v + 2 ^ (v + 1) * clockB v =
      3 ^ v * clockB v := by
    have : clockA v * clockB v + 2 ^ (v + 1) * clockB v =
        (clockA v + 2 ^ (v + 1)) * clockB v := (Nat.add_mul _ _ _).symm
    rw [this, hsum]
  rw [h1, Nat.add_assoc, h2, ← Nat.mul_add]

/-- A putative integer clock `2^{v+1}(e + c) = 3^v(n + c)` forces `A c = B`. -/
theorem clock_forces_A_c {n v u e c : Nat}
    (h : IsExcursion n v u 1 e) (hv : 2 ≤ v)
    (heq : 2 ^ (v + 1) * (e + c) = 3 ^ v * (n + c)) :
    clockA v * c = clockB v := by
  have hland := landing_n_of_even_v_W_one h hv
  have hA : 2 ^ (v + 1) ≤ 3 ^ v := two_pow_succ_le_three_pow hv
  have hL : 2 ^ (v + 1) * e + 2 ^ (v + 1) * c = 3 ^ v * n + 3 ^ v * c := by
    rw [Nat.mul_add, Nat.mul_add] at heq
    exact heq
  have hsum : 3 ^ v * n + (3 ^ v - 2 ^ v) + 2 ^ (v + 1) * c =
      3 ^ v * n + 3 ^ v * c := by
    rw [hland.symm]
    exact hL
  have hBc : clockB v + 2 ^ (v + 1) * c = 3 ^ v * c := by
    simp only [clockB] at *
    omega
  have hle : 2 ^ (v + 1) * c ≤ 3 ^ v * c := Nat.mul_le_mul_right c hA
  simp only [clockA, clockB]
  rw [Nat.mul_sub_right_distrib]
  omega

/-- `2^v < 3^{v−1}` for `v ≥ 4`. -/
private theorem two_pow_lt_three_pow_pred {v : Nat} (hv : 4 ≤ v) :
    2 ^ v < 3 ^ (v - 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hv
  subst hk
  clear hv
  induction k with
  | zero => decide
  | succ k ih =>
    have h2 : 2 ^ (4 + (k + 1)) = 2 * 2 ^ (4 + k) := by
      rw [show 4 + (k + 1) = (4 + k) + 1 by omega, two_pow_succ]
    have h3 : 3 ^ (4 + (k + 1) - 1) = 3 * 3 ^ (4 + k - 1) := by
      have : 4 + (k + 1) - 1 = (4 + k - 1) + 1 := by omega
      rw [this, three_pow_succ]
    rw [h2, h3]
    have hlt : 2 * 2 ^ (4 + k) < 2 * 3 ^ (4 + k - 1) :=
      Nat.mul_lt_mul_of_pos_left ih (by omega)
    have hlt2 : 2 * 3 ^ (4 + k - 1) < 3 * 3 ^ (4 + k - 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega : (2 : Nat) < 3) (three_pow_pos _)
    exact Nat.lt_trans hlt hlt2

/-- For even `v ≥ 4` one has `2A > B`, so `A c = B` is impossible in `Nat`. -/
private theorem two_clockA_gt_clockB {v : Nat} (hv : 4 ≤ v) :
    clockB v < 2 * clockA v := by
  have hA : 2 ^ (v + 1) ≤ 3 ^ v :=
    two_pow_succ_le_three_pow (by omega : 2 ≤ v)
  have hB : 2 ^ v ≤ 3 ^ v := two_pow_le_three_pow v
  have hpred := two_pow_lt_three_pow_pred hv
  simp only [clockA, clockB]
  have h2A : 2 * (3 ^ v - 2 ^ (v + 1)) = 2 * 3 ^ v - 2 ^ (v + 2) := by
    have hpow : 2 * 2 ^ (v + 1) = 2 ^ (v + 2) := by
      have hadd : v + 2 = (v + 1) + 1 := by omega
      have hsucc : 2 ^ ((v + 1) + 1) = 2 * 2 ^ (v + 1) := two_pow_succ (v + 1)
      rw [hadd, hsucc]
    rw [Nat.mul_sub_left_distrib, hpow]
  rw [h2A]
  have h3v : 3 ^ v = 3 * 3 ^ (v - 1) := by
    have hsucc : 3 ^ (v - 1 + 1) = 3 * 3 ^ (v - 1) := three_pow_succ (v - 1)
    have heq : v - 1 + 1 = v := by omega
    rwa [heq] at hsucc
  have h3 : 3 * 2 ^ v < 3 ^ v := by
    rw [h3v]
    exact Nat.mul_lt_mul_of_pos_left hpred (by omega)
  have hR : 2 ^ (v + 2) = 4 * 2 ^ v := by
    have : v + 2 = 2 + v := by omega
    rw [this, Nat.pow_add, show (2 : Nat) ^ 2 = 4 by decide]
  have hleR : 2 ^ (v + 2) ≤ 2 * 3 ^ v := by
    rw [hR]
    have : 2 * 2 ^ v < 3 ^ v := by
      have : 2 * 2 ^ v = 2 ^ (v + 1) := (two_pow_succ v).symm
      rw [this]
      exact two_pow_succ_lt_three_pow (by omega)
    omega
  omega

/-- **Negative theorem, general even `v ≥ 4`.**  There is no `Nat` `c > 0`
with `2^{v+1}(e + c) = 3^v(n + c)`.  At `v = 2` the same identity *is*
the integer clock `c = 5`. -/
theorem no_nat_clock_even_v {n v u e c : Nat}
    (h : IsExcursion n v u 1 e) (hv : 4 ≤ v) (hc : 0 < c)
    (_heven : v % 2 = 0) :
    2 ^ (v + 1) * (e + c) ≠ 3 ^ v * (n + c) := by
  intro heq
  have hAc := clock_forces_A_c h (by omega : 2 ≤ v) heq
  have hgt := two_clockA_gt_clockB hv
  have hApos : 0 < clockA v := by
    simp only [clockA]
    exact Nat.sub_pos_of_lt (two_pow_succ_lt_three_pow (by omega))
  have hltAB : clockA v < clockB v := by
    simp only [clockA, clockB]
    have hA : 2 ^ (v + 1) ≤ 3 ^ v :=
      two_pow_succ_le_three_pow (by omega : 2 ≤ v)
    have hB : 2 ^ v ≤ 3 ^ v := two_pow_le_three_pow v
    have : 2 ^ v < 2 ^ (v + 1) := two_pow_lt_two_pow (by omega)
    omega
  rcases Nat.eq_or_lt_of_le hc with h1 | h2
  · subst h1
    have : clockA v = clockB v := by simpa using hAc
    omega
  · have hc2 : 2 ≤ c := by omega
    have hle : 2 * clockA v ≤ clockA v * c := by
      have : clockA v * 2 ≤ clockA v * c := Nat.mul_le_mul_left _ hc2
      rwa [Nat.mul_comm (clockA v) 2] at this
    omega

/-- Even `v ≥ 2` and `u ≡ 3 (mod 4)` force `W = 1`.  Dual of
`W_eq_one_of_odd_v_u_one_mod_four`. -/
theorem W_eq_one_of_even_v_u_three_mod_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (heven : v % 2 = 0) (hv : 2 ≤ v)
    (hu4 : u % 4 = 3) : W = 1 := by
  obtain ⟨t, ht1, -, hL⟩ := val2_three_pow_sub_one_even (by omega) heven
  have hu : 1 < u := by omega
  have ht : Val2 (u - 1) 1 := Val2.one_iff.mpr (by omega)
  have hlt : 1 < t + 2 := by omega
  exact W_eq_of_u_pred_lt h hu ht hL hlt

end ExcursionFourLight
end Collatz

section AxiomAudit
open Collatz.ExcursionFourLight
#print axioms landing_u_of_v_four_W_one
#print axioms landing_n_of_v_four_W_one
#print axioms no_nat_clock
#print axioms two_adic_clock
#print axioms val2_ge_six
#print axioms val2_landing
#print axioms not_second_light
#print axioms two_light_fuel
#print axioms exit_one_mod_four
#print axioms exit_one_is_v_one
#print axioms exit_three_mod_eight
#print axioms exit_two_is_v_two
#print axioms exit_seven_mod_sixteen
#print axioms exit_three_is_v_three
#print axioms exit_thirty_one_mod_thirty_two
#print axioms lemmaX_of_v_four_land_one_heavy
#print axioms grows_of_v_four_land_one_light
#print axioms two_adic_clock_even_v
#print axioms no_nat_clock_even_v
#print axioms W_eq_one_of_even_v_u_three_mod_four
end AxiomAudit
