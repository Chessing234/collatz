import Collatz.Strategy.ExcursionOddLight

/-!
# The 2-adic fuel of a `(3, 1)` leftover

There is no integer clock `16(e + c) = 27(n + c)` (`no_nat_clock`).  The
unique 2-adic clock

  `16(11e + 19) = 27(11n + 19)`

makes `11n + 19` a Lyapunov quantity on the class: each `(3, 1)` step
spends exactly four factors of two.

  `v₂(11n + 19) ≥ 5`,     `v₂(11e + 19) = v₂(11n + 19) − 4`.

The fuel is finite, so a single integer cannot take infinitely many
`(3, 1)` steps.  After one step the remainder `r − 4` reads the landing:

* `r = 5` → remainder `1` → `e ≡ 1 (mod 4)` → next `v = 1`
  (the LandOne dichotomy: `W' ≥ 2` drops, `W' = 1` grows);
* `r = 6` → remainder `2` → `e ≡ 3 (mod 8)` → next `v = 2`
  (either `3 (mod 16)` drops, or `(2, 1)` light);
* `r = 7` → remainder `3` → `e ≡ 15 (mod 16)` → next `v ≥ 4`;
* `r = 8` → remainder `4` → `e ≡ 23 (mod 32)` → next `v = 3`, not
  another `(3, 1)` (fuel `< 5`), so `W' ≥ 2`;
* `r ≥ 9` is the only room for a second `(3, 1)` step.

This is the plus-five / Clock device, written for the leftover odd run
instead of the even light block.  It does **not** prove Lemma X: the
`r = 5`, `W' = 1` family `71 → 121 → 91` still grows, as a law.
-/

namespace Collatz
namespace ExcursionEleven

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionOddLight


/-! ## 1.  Scaling lemmas for the clock -/

/-- Scaling by `27` does not change the valuation. -/
private theorem val2_twenty_seven_mul {x r : Nat} (h : Val2 x r) :
    Val2 (27 * x) r := by
  have h27 : Val2 (27 : Nat) 0 := Val2.of_odd (by decide)
  have := Val2.mul h27 h
  simpa using this

/-- The odd factor `27` can be cancelled. -/
private theorem val2_of_twenty_seven_mul {x r : Nat}
    (hx : 0 < x) (h : Val2 (27 * x) r) : Val2 x r := by
  obtain ⟨s, hs⟩ := Val2.exists_of_pos hx
  exact (Val2.unique (val2_twenty_seven_mul hs) h) ▸ hs

/-- Scaling by `16 = 2 ^ 4` raises the valuation by exactly four. -/
private theorem val2_sixteen_mul {x r : Nat} (h : Val2 x r) :
    Val2 (16 * x) (r + 4) := by
  have h16 : (16 : Nat) = 2 ^ 4 := by decide
  rw [h16]
  have := Val2.two_pow_mul h 4
  simpa [Nat.add_comm] using this


/-! ## 2.  Fuel lower bound, and the countdown -/

/-- Every `(3, 1)` start has `32 ∣ 11n + 19`. -/
theorem thirty_two_dvd {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    32 ∣ 11 * n + 19 := by
  obtain ⟨k, hk⟩ := exists_k_of_v_three_W_one h
  have hn : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  subst hk
  -- `11(8(4k+1) − 1) + 19 = 32(11k + 3)`
  omega

/-- **Fuel ≥ 5.**  Every `(3, 1)` excursion has `v₂(11n + 19) ≥ 5`.
Remainder `4` is impossible: `11e + 19` is always even for odd `e`, so
the countdown never lands on valuation `0`, and a start of fuel `4`
would. -/
theorem val2_ge_five {n u e r : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) r) : 5 ≤ r := by
  have hdvd := thirty_two_dvd h
  have hpow : (2 : Nat) ^ 5 = 32 := by decide
  exact (Val2.dvd_iff_le hr).mp (hpow ▸ hdvd)

/-- **Fuel identity.**  The clock shifts the valuation of `11· + 19` by `−4`. -/
theorem val2_eleven_shift {n u e r : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * e + 19) r) :
    Val2 (11 * n + 19) (r + 4) := by
  have hclock := two_adic_clock h
  have h16 := val2_sixteen_mul hr
  have hpos : 0 < 11 * n + 19 := by
    have : 0 < 16 * (11 * e + 19) := Val2.pos h16
    omega
  have h27 : Val2 (27 * (11 * n + 19)) (r + 4) := hclock ▸ h16
  exact val2_of_twenty_seven_mul hpos h27

/-- **Countdown.**  One `(3, 1)` step spends exactly four factors of two. -/
theorem val2_landing {n u e r : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) r) :
    Val2 (11 * e + 19) (r - 4) := by
  have hge := val2_ge_five h hr
  obtain ⟨s, hs⟩ := Val2.exists_of_pos (by omega : 0 < 11 * e + 19)
  have hr' := val2_eleven_shift h hs
  have heq : s + 4 = r := Val2.unique hr' hr
  have : s = r - 4 := by omega
  rwa [this] at hs

/-- The fuel strictly decreases. -/
theorem fuel_lt {n u e r : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) r) :
    r - 4 < r := by
  have := val2_ge_five h hr
  omega


/-! ## 3.  A second `(3, 1)` step needs fuel `≥ 9` -/

/-- If `v₂(11n + 19) < 9`, the landing is not another `(3, 1)` excursion. -/
theorem not_second_light {n u e r u2 e2 : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) r) (hlt : r < 9) :
    ¬ IsExcursion e 3 u2 1 e2 := by
  intro h2
  have hs := val2_landing h hr
  have h5 := val2_ge_five h2 hs
  omega

/-- Two consecutive `(3, 1)` steps force `v₂(11n + 19) ≥ 9`. -/
theorem two_light_fuel {n u e u2 e2 r : Nat}
    (h1 : IsExcursion n 3 u 1 e) (h2 : IsExcursion e 3 u2 1 e2)
    (hr : Val2 (11 * n + 19) r) : 9 ≤ r := by
  have hs := val2_landing h1 hr
  have := val2_ge_five h2 hs
  omega


/-! ## 4.  Exit letters after one leftover step -/

/-- Remainder `1`: `v₂(11n + 19) = 5` lands on `e ≡ 1 (mod 4)`. -/
theorem exit_one_mod_four {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 5) :
    e % 4 = 1 := by
  have hs : Val2 (11 * e + 19) 1 := by
    have := val2_landing h hr
    simpa using this
  have : (11 * e + 19) % 4 = 2 := Val2.one_iff.mp hs
  omega

/-- That remainder-`1` landing is next run `v = 1`. -/
theorem exit_one_is_v_one {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 5)
    (h' : IsExcursion e v' u' W' e') : v' = 1 :=
  (v_eq_one_iff h').mpr (exit_one_mod_four h hr)

/-- Remainder `2`: `v₂(11n + 19) = 6` lands on `e ≡ 3 (mod 8)`. -/
theorem exit_three_mod_eight {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 6) :
    e % 8 = 3 := by
  have hs : Val2 (11 * e + 19) 2 := by
    have := val2_landing h hr
    simpa using this
  have : (11 * e + 19) % 8 = 4 := Val2.two_iff.mp hs
  omega

/-- That remainder-`2` landing is next run `v = 2`. -/
theorem exit_two_is_v_two {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 6)
    (h' : IsExcursion e v' u' W' e') : v' = 2 :=
  (v_eq_two_iff h').mpr (exit_three_mod_eight h hr)

/-- Remainder `3`: `v₂(11n + 19) = 7` lands on `e ≡ 15 (mod 16)`. -/
theorem exit_fifteen_mod_sixteen {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 7) :
    e % 16 = 15 := by
  have hs : Val2 (11 * e + 19) 3 := by
    have := val2_landing h hr
    simpa using this
  have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
  have : (11 * e + 19) % 16 = 8 := by
    have := Val2.mod hs
    rwa [hpow] at this
  omega

/-- That remainder-`3` landing has next run `v ≥ 4`. -/
theorem exit_three_v_ge_four {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 7)
    (h' : IsExcursion e v' u' W' e') : 4 ≤ v' := by
  have h16 := exit_fifteen_mod_sixteen h hr
  have hval := val2_succ_of h'
  have hdvd : 16 ∣ e + 1 := by omega
  have hpow : (2 : Nat) ^ 4 = 16 := by decide
  exact (Val2.dvd_iff_le hval).mp (hpow ▸ hdvd)

/-- Remainder `4`: `v₂(11n + 19) = 8` lands on `e ≡ 23 (mod 32)`. -/
theorem exit_twenty_three_mod_thirty_two {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 8) :
    e % 32 = 23 := by
  have hs : Val2 (11 * e + 19) 4 := by
    have := val2_landing h hr
    simpa using this
  have hpow : (2 : Nat) ^ (4 + 1) = 32 := by decide
  have : (11 * e + 19) % 32 = 16 := by
    have := Val2.mod hs
    rwa [hpow] at this
  omega

/-- That remainder-`4` landing is `≡ 7 (mod 16)`, hence next run `v = 3`,
and is not another `(3, 1)` step. -/
theorem exit_four_mod_sixteen {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 8) :
    e % 16 = 7 := by
  have := exit_twenty_three_mod_thirty_two h hr
  omega


/-! ## 5.  Witnesses -/

/-- Fuel `5`, remainder `1`: `7 → 13 ≡ 1 (mod 4)`. -/
theorem seven_fuel :
    IsExcursion 7 3 1 1 13 ∧ Val2 (11 * 7 + 19) 5 ∧ 13 % 4 = 1 :=
  ⟨seven_is_v_three_W_one, ⟨3, rfl, rfl⟩, rfl⟩

/-- Fuel `6`, remainder `2`: `39 → 67 ≡ 3 (mod 8)`. -/
theorem thirty_nine_fuel :
    IsExcursion 39 3 5 1 67 ∧ Val2 (11 * 39 + 19) 6 ∧ 67 % 8 = 3 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨7, rfl, rfl⟩, rfl⟩

/-- Fuel `7`, remainder `3`: `103 → 175 ≡ 15 (mod 16)`. -/
theorem one_oh_three_fuel :
    IsExcursion 103 3 13 1 175 ∧ Val2 (11 * 103 + 19) 7 ∧ 175 % 16 = 15 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨9, rfl, rfl⟩, rfl⟩

/-- Fuel `8`, remainder `4`: `487 → 823 ≡ 23 (mod 32)`. -/
theorem four_eighty_seven_fuel :
    IsExcursion 487 3 61 1 823 ∧ Val2 (11 * 487 + 19) 8 ∧ 823 % 32 = 23 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨21, rfl, rfl⟩, rfl⟩

/-- Fuel `9` permits a second `(3, 1)`: `231 → 391`. -/
theorem two_thirty_one_two_light :
    IsExcursion 231 3 29 1 391 ∧
    IsExcursion 391 3 49 1 661 ∧
    Val2 (11 * 231 + 19) 9 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨5, rfl, rfl⟩⟩

/-- The `r = 5`, `W' = 1` obstruction is unchanged: `71 → 121 → 91`. -/
theorem seventy_one_fuel_grows :
    IsExcursion 71 3 9 1 121 ∧
    Val2 (11 * 71 + 19) 5 ∧
    IsExcursion 121 1 61 1 91 ∧
    71 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨25, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

end ExcursionEleven
end Collatz

section AxiomAudit
open Collatz.ExcursionEleven
#print axioms thirty_two_dvd
#print axioms val2_ge_five
#print axioms val2_eleven_shift
#print axioms val2_landing
#print axioms not_second_light
#print axioms two_light_fuel
#print axioms exit_one_mod_four
#print axioms exit_one_is_v_one
#print axioms exit_three_mod_eight
#print axioms exit_two_is_v_two
#print axioms exit_fifteen_mod_sixteen
#print axioms exit_three_v_ge_four
#print axioms exit_twenty_three_mod_thirty_two
end AxiomAudit
