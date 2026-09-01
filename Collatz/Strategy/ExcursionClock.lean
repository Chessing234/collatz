import Collatz.Strategy.ExcursionExit

/-!
# The 2-adic fuel of a `(2, 1)` light block

A `(v, W) = (2, 1)` excursion is the class `n ≡ 11 (mod 16)`.  The integer
clock `8(e + 5) = 9(n + 5)` (`ExcursionExit.eight_clock`) makes `n + 5` a
Lyapunov quantity on that class: each light step spends exactly three
factors of two.

  `v₂(n + 5) ≥ 4`,     `v₂(e + 5) = v₂(n + 5) − 3`.

The fuel is finite, so a single integer cannot take infinitely many
`(2, 1)` steps.  After the last one the remainder is `1`, `2`, or `3`:

* remainder `1` (`r = 4` after one step): `e ≡ 1 (mod 4)`, then
  `drop_of_v_one` on the landing (the class `11 (mod 32)`, already closed);
* remainder `3` (`r = 6` after one step): `e ≡ 3 (mod 16)`, then
  `drop_of_three_mod_sixteen` on the landing (the class `59 (mod 128)`);
* remainder `2` (`r = 5`): `e ≡ 7 (mod 8)`, odd `v ≥ 3`, not a drop
  (`ExcursionExit.next_not_force_drop`, witness `27 → 31 → 121`).

Two consecutive `(2, 1)` steps need fuel `≥ 7`.  The device does not claim
that the landing's own drop goes below the original start, except on the
one-step remainder-`1` class already proved as `lemmaX_of_eleven_mod_thirtytwo`.
-/

namespace Collatz
namespace ExcursionClock

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionBlock Collatz.ExcursionExit


/-! ## 1.  Fuel lower bound, and the countdown -/

/-- A `(2, 1)` start is `n ≡ 11 (mod 16)`, equivalently `16 ∣ n + 5`. -/
theorem light_iff_dvd {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 2 ∧ W = 1 ↔ 16 ∣ n + 5 := by
  constructor
  · intro hvW
    have hmod : n % 16 = 11 := (v_two_W_one_iff h).mp hvW
    omega
  · intro hdvd
    have hmod : n % 16 = 11 := by omega
    exact (v_two_W_one_iff h).mpr hmod

/-- **Fuel ≥ 4.**  Every `(2, 1)` excursion has `v₂(n + 5) ≥ 4`. -/
theorem val2_ge_four {n u e r : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) r) : 4 ≤ r := by
  have hdvd : 16 ∣ n + 5 := (light_iff_dvd h).mp ⟨rfl, rfl⟩
  have hpow : (2 : Nat) ^ 4 = 16 := by decide
  exact (Val2.dvd_iff_le hr).mp (hpow ▸ hdvd)

/-- **Countdown.**  One `(2, 1)` step spends exactly three factors of two. -/
theorem val2_landing {n u e r : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) r) :
    Val2 (e + 5) (r - 3) := by
  have hge := val2_ge_four h hr
  obtain ⟨s, hs⟩ := Val2.exists_of_pos (by omega : 0 < e + 5)
  have hr' := val2_plus_five_shift h hs
  have heq : s + 3 = r := Val2.unique hr' hr
  have : s = r - 3 := by omega
  rwa [this] at hs

/-- The fuel strictly decreases. -/
theorem fuel_lt {n u e r : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) r) :
    r - 3 < r := by
  have := val2_ge_four h hr
  omega


/-! ## 2.  A second `(2, 1)` step needs fuel `≥ 7` -/

/-- If `v₂(n + 5) < 7`, the landing is not another `(2, 1)` excursion. -/
theorem not_second_light {n u e r u2 e2 : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) r) (hlt : r < 7) :
    ¬ IsExcursion e 2 u2 1 e2 := by
  intro h2
  have hs := val2_landing h hr
  have h4 := val2_ge_four h2 hs
  omega

/-- Two consecutive `(2, 1)` steps force `v₂(n + 5) ≥ 7`. -/
theorem two_light_fuel {n u e u2 e2 r : Nat}
    (h1 : IsExcursion n 2 u 1 e) (h2 : IsExcursion e 2 u2 1 e2)
    (hr : Val2 (n + 5) r) : 7 ≤ r := by
  have hs := val2_landing h1 hr
  have := val2_ge_four h2 hs
  omega


/-! ## 3.  Exit letters after one light step -/

/-- Remainder `1`: `v₂(n + 5) = 4` lands on `e ≡ 1 (mod 4)`. -/
theorem exit_one_mod_four {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 4) :
    e % 4 = 1 := by
  have hs : Val2 (e + 5) 1 := by
    have := val2_landing h hr
    simpa using this
  have : (e + 5) % 4 = 2 := Val2.one_iff.mp hs
  omega

/-- `v₂(x) = 3` is the class `x ≡ 8 (mod 16)`. -/
private theorem val2_three_iff {x : Nat} : Val2 x 3 ↔ x % 16 = 8 := by
  simpa using (@Val2.iff_mod x 3)

/-- Remainder `3`: `v₂(n + 5) = 6` lands on `e ≡ 3 (mod 16)`. -/
theorem exit_three_mod_sixteen {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 6) :
    e % 16 = 3 := by
  have hs : Val2 (e + 5) 3 := by
    have := val2_landing h hr
    simpa using this
  have : (e + 5) % 16 = 8 := val2_three_iff.mp hs
  omega

/-- Remainder `2`: `v₂(n + 5) = 5` lands on `e ≡ 7 (mod 8)`. -/
theorem exit_seven_mod_eight {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 5) :
    e % 8 = 7 := by
  have hs : Val2 (e + 5) 2 := by
    have := val2_landing h hr
    simpa using this
  exact e_seven_mod_eight h hs

/-- The remainder-`1` landing (`r = 4`) is itself `v = 1`, so it drops
below *itself*.  That is not a drop below the original start; the two-step
comparison with the start is `lemmaX_of_eleven_mod_thirtytwo`. -/
theorem exit_one_drops_landing {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 4) (he : 1 < e) :
    ∃ e' : Nat, NextOdd e e' ∧ e' < e := by
  have h4 := exit_one_mod_four h hr
  have hodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v, u', W, e', h'⟩ := exists_excursion hodd
  have hv : v = 1 := (v_eq_one_iff h').mpr h4
  exact ⟨e', ⟨v, u', W, h'⟩, drop_of_v_one h' hv he⟩

/-- The remainder-`3` landing (`r = 6`) is `3 (mod 16)`, so it drops below
*itself*.  Not automatically below the original start. -/
theorem exit_three_drops_landing {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 6) (he : 1 < e) :
    ∃ e' : Nat, NextOdd e e' ∧ e' < e := by
  have h16 := exit_three_mod_sixteen h hr
  have hodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v, u', W, e', h'⟩ := exists_excursion hodd
  exact ⟨e', ⟨v, u', W, h'⟩, drop_of_three_mod_sixteen h' h16 he⟩


/-! ## 4.  Witnesses for the three remainders after one step -/

/-- Remainder `1`: `11 + 5` has valuation `4`, landing `13 ≡ 1 (mod 4)`. -/
theorem eleven_fuel :
    IsExcursion 11 2 3 1 13 ∧ Val2 (11 + 5) 4 ∧ 13 % 4 = 1 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨1, rfl, rfl⟩, rfl⟩

/-- Remainder `2`: `27 + 5` has valuation `5`, landing `31 ≡ 7 (mod 8)`. -/
theorem twenty_seven_fuel :
    IsExcursion 27 2 7 1 31 ∧ Val2 (27 + 5) 5 ∧ 31 % 8 = 7 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨1, rfl, rfl⟩, rfl⟩

/-- Remainder `3`: `59 + 5` has valuation `6`, landing `67 ≡ 3 (mod 16)`. -/
theorem fifty_nine_fuel :
    IsExcursion 59 2 15 1 67 ∧ Val2 (59 + 5) 6 ∧ 67 % 16 = 3 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨1, rfl, rfl⟩, rfl⟩

end ExcursionClock
end Collatz

section AxiomAudit
open Collatz.ExcursionClock
#print axioms light_iff_dvd
#print axioms val2_ge_four
#print axioms val2_landing
#print axioms not_second_light
#print axioms two_light_fuel
#print axioms exit_one_mod_four
#print axioms exit_three_mod_sixteen
#print axioms exit_seven_mod_eight
#print axioms exit_one_drops_landing
#print axioms exit_three_drops_landing
end AxiomAudit
