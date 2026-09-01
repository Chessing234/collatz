import Collatz.Strategy.ExcursionEleven
import Collatz.Strategy.ExcursionLandOne
import Collatz.Strategy.ExcursionLandVal2
import Collatz.Strategy.ExcursionLandTwo
import Collatz.Strategy.ExcursionRemTwoLeft
import Collatz.Strategy.ExcursionTelescope

/-!
# Chaining Lemma X: one named remainder, strictly inside plus-five

`ExcursionPlusFive.collatz_of_lemmaX_plus_five` reduces Collatz to Lemma X on
the leftover `{ v₂(n+5) = 2 } ∪ { v₂(n+5) ≥ 4 }`.  This file **does not redo**
those drops.  It consumes the existing lemmaX theorems on that leftover,
case-splitting the first excursion and the two clocks, and leaves a single
named predicate `OpenRemainder` for the families those theorems do not close:

* the 71 family: `(3, 1)` fuel 5 then `v' = 1`, `W' = 1`;
* `(2, 1)` remainder 2 with next `v' ≥ 7` or light `W'`;
* `(2, 1)` rem 2 with `v' = 6` and `W' ≤ 3`;
* `(3, 1)` fuel 6 then another `(2, 1)`;
* `(3, 1)` fuel 7 with next `v' = 4`, `W' ≤ 3`, or `v' ≥ 5`;
* `(3, 1)` fuel 8 with next `W' = 2`;
* longer leftover chains (fuel `≥ 9`);
* longer `(2, 1)` chains (fuel `7`, `8`, or `≥ 10`);
* first-excursion `v ≥ 4` (including `(4, 1)` light).

This is not a proof of Collatz.  It is a smaller Lemma X input.
-/

namespace Collatz
namespace ExcursionChain

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionPlusFive Collatz.ExcursionClock
open Collatz.ExcursionEleven Collatz.ExcursionLandOne Collatz.ExcursionLand
open Collatz.ExcursionLandVal2 Collatz.ExcursionLandTwo
open Collatz.ExcursionRemTwo Collatz.ExcursionRemTwoLeft
open Collatz.ExcursionLTE Collatz.ExcursionExit Collatz.ExcursionOddLight
open Collatz.ExcursionTelescope


/-! ## 1.  The remaining predicate, named honestly -/

/-- Next letter after a `(2, 1)` remainder-`2` landing that existing lemmaX
theorems do not drop. -/
def OpenRemTwoNext (v' W' : Nat) : Prop :=
  (v' = 3 ∧ W' = 1) ∨
  (v' = 4 ∧ W' ≤ 2) ∨
  (v' = 5 ∧ W' ≤ 3) ∨
  (v' = 6 ∧ W' ≤ 3) ∨
  7 ≤ v'

/-- `(2, 1)` clock remainders not closed by chaining.  Fuel `4` is
`lemmaX_of_eleven_mod_thirtytwo`; fuel `6` is one light then remainder `3`;
fuel `9` is `lemmaX_of_two_light_then_three`. -/
def OpenClock (n _u e : Nat) : Prop :=
  ∃ r : Nat, Val2 (n + 5) r ∧
    ((r = 5 ∧ ∃ v' u' W' e' : Nat,
        IsExcursion e v' u' W' e' ∧ OpenRemTwoNext v' W') ∨
     r = 7 ∨ r = 8 ∨ 10 ≤ r)

/-- `(3, 1)` 11-clock remainders not closed by chaining.  Fuel `5` with
`W' ≥ 2` is LandOne; fuel `6` with next `W' ≥ 2` is Land; fuel `7`/`8`
heavy slices are LandVal2. -/
def OpenLeftover (n _u e : Nat) : Prop :=
  ∃ r : Nat, Val2 (11 * n + 19) r ∧
    ((r = 5 ∧ ∃ u' e' : Nat, IsExcursion e 1 u' 1 e') ∨
     (r = 6 ∧ ∃ u' e' : Nat, IsExcursion e 2 u' 1 e') ∨
     (r = 7 ∧ ∃ v' u' W' e' : Nat,
        IsExcursion e v' u' W' e' ∧ (v' = 4 ∧ W' ≤ 3 ∨ 5 ≤ v')) ∨
     (r = 8 ∧ ∃ u' e' : Nat, IsExcursion e 3 u' 2 e') ∨
     9 ≤ r)

/-- **The remaining Lemma X input.**  `n` is here only when the first
excursion / fuel analysis does not fire an existing lemmaX theorem. -/
def OpenRemainder (n : Nat) : Prop :=
  ∃ v u W e : Nat, IsExcursion n v u W e ∧
    ((v = 2 ∧ W = 1 ∧ OpenClock n u e) ∨
     (v = 3 ∧ W = 1 ∧ OpenLeftover n u e) ∨
     4 ≤ v)


/-! ## 2.  Constructors, so the case-split inhabits the predicate cleanly -/

theorem open_of_clock {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hc : OpenClock n u e) : OpenRemainder n :=
  ⟨2, u, 1, e, h, Or.inl ⟨rfl, rfl, hc⟩⟩

theorem open_of_leftover {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hl : OpenLeftover n u e) : OpenRemainder n :=
  ⟨3, u, 1, e, h, Or.inr (Or.inl ⟨rfl, rfl, hl⟩)⟩

theorem open_of_v_ge_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : 4 ≤ v) : OpenRemainder n :=
  ⟨v, u, W, e, h, Or.inr (Or.inr hv)⟩

theorem open_clock_rem_two {n u e v' u' W' e' : Nat}
    (hr : Val2 (n + 5) 5) (h' : IsExcursion e v' u' W' e')
    (hnxt : OpenRemTwoNext v' W') : OpenClock n u e :=
  ⟨5, hr, Or.inl ⟨rfl, v', u', W', e', h', hnxt⟩⟩

theorem open_clock_fuel_seven {n u e : Nat} (hr : Val2 (n + 5) 7) :
    OpenClock n u e :=
  ⟨7, hr, Or.inr (Or.inl rfl)⟩

theorem open_clock_fuel_eight {n u e : Nat} (hr : Val2 (n + 5) 8) :
    OpenClock n u e :=
  ⟨8, hr, Or.inr (Or.inr (Or.inl rfl))⟩

theorem open_clock_fuel_long {n u e r : Nat}
    (hr : Val2 (n + 5) r) (h10 : 10 ≤ r) : OpenClock n u e :=
  ⟨r, hr, Or.inr (Or.inr (Or.inr h10))⟩

theorem open_leftover_seventy_one {n u e u' e' : Nat}
    (hr : Val2 (11 * n + 19) 5) (h' : IsExcursion e 1 u' 1 e') :
    OpenLeftover n u e :=
  ⟨5, hr, Or.inl ⟨rfl, u', e', h'⟩⟩

theorem open_leftover_then_light {n u e u' e' : Nat}
    (hr : Val2 (11 * n + 19) 6) (h' : IsExcursion e 2 u' 1 e') :
    OpenLeftover n u e :=
  ⟨6, hr, Or.inr (Or.inl ⟨rfl, u', e', h'⟩)⟩

theorem open_leftover_fuel_seven {n u e v' u' W' e' : Nat}
    (hr : Val2 (11 * n + 19) 7) (h' : IsExcursion e v' u' W' e')
    (hnxt : v' = 4 ∧ W' ≤ 3 ∨ 5 ≤ v') : OpenLeftover n u e :=
  ⟨7, hr, Or.inr (Or.inr (Or.inl ⟨rfl, v', u', W', e', h', hnxt⟩))⟩

theorem open_leftover_fuel_eight_W_two {n u e u' e' : Nat}
    (hr : Val2 (11 * n + 19) 8) (h' : IsExcursion e 3 u' 2 e') :
    OpenLeftover n u e :=
  ⟨8, hr, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, u', e', h'⟩)))⟩

theorem open_leftover_fuel_long {n u e r : Nat}
    (hr : Val2 (11 * n + 19) r) (h9 : 9 ≤ r) : OpenLeftover n u e :=
  ⟨r, hr, Or.inr (Or.inr (Or.inr (Or.inr h9)))⟩

theorem pack_two {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (hlt : e' < n) : ∃ eout : Nat, ExChain n eout ∧ eout < n :=
  ⟨e', ExChain.cons ⟨v, u, W, h⟩ (ExChain.one ⟨v', u', W', h'⟩), hlt⟩


/-! ## 3.  Glue lemmas that chain existing theorem statements -/

/-- Fuel `4` of a `(2, 1)` start is `n ≡ 11 (mod 32)`. -/
theorem mod_thirtytwo_of_fuel_four {n u e : Nat}
    (_h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 4) : n % 32 = 11 := by
  have hpow : (2 : Nat) ^ (4 + 1) = 32 := by decide
  have hmod : (n + 5) % 32 = 16 := by
    have := Val2.mod hr
    rwa [hpow] at this
  omega

/-- **Glue:** `Eleven.exit_one_is_v_one` into `LandOne.lemmaX_of_v_three_land_one`. -/
theorem lemmaX_of_eleven_fuel_five_heavy {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 5) (hn : 1 < n)
    (hheavy : ∀ u' W' e' : Nat, IsExcursion e 1 u' W' e' → 2 ≤ W') :
    ∃ e' : Nat, ExChain n e' ∧ e' < n := by
  have he4 := exit_one_mod_four h hr
  have hr1 : Val2 (e + 5) 1 := Val2.one_iff.mpr (by omega)
  exact lemmaX_of_v_three_land_one h hr1 hn hheavy

/-- One `(2, 1)` step then remainder `3` drops below the start.
`(9/8) · (9/16) = 81/128 < 1`; the `W = 2` upper bound is already enough. -/
private theorem one_light_drop_coeff {n : Nat} (h : 11 ≤ n) :
    81 * n + 85 < 128 * n := by
  have h47 : 85 < 47 * n := by
    have hmin : 47 * 11 ≤ 47 * n := Nat.mul_le_mul_left 47 h
    have hnum : (85 : Nat) < 47 * 11 := by decide
    omega
  omega

theorem lemmaX_of_one_light_then_three {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 3) (_hn : 1 < n) :
    ∃ e' : Nat, ExChain n e' ∧ e' < n := by
  have he16 := land_three_mod_sixteen hrem
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have ⟨hv', hW'⟩ := (v_two_W_ge_two_iff h').mpr he16
  have h'2 : IsExcursion e 2 u' W' e' := hv' ▸ h'
  have h16 := landing_upper_of_v_two_W_ge_two h'2 hW'
  have hclock := eight_clock h
  have h8e : 8 * e = 9 * n + 5 := by omega
  have hn11 := eleven_le_of_v_two_W_one h
  have h128 : 128 * e' ≤ 81 * n + 85 := by
    have hL : 8 * (16 * e') = 128 * e' := by omega
    have hmul : 8 * (16 * e') ≤ 8 * (9 * e + 5) := Nat.mul_le_mul_left 8 h16
    have hrhs : 8 * (9 * e + 5) = 81 * n + 85 := by
      have : 8 * (9 * e + 5) = 9 * (8 * e) + 40 := by omega
      rw [this, h8e]
      omega
    omega
  have hcoeff := one_light_drop_coeff hn11
  have hdrop : e' < n := by
    have : 128 * e' < 128 * n := Nat.lt_of_le_of_lt h128 hcoeff
    exact Nat.lt_of_mul_lt_mul_left this
  exact pack_two h h' hdrop

/-- Fuel `4` of the even clock. -/
theorem lemmaX_of_clock_fuel_four {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 4) (hn : 1 < n) :
    ∃ e' : Nat, ExChain n e' ∧ e' < n :=
  lemmaX_of_eleven_mod_thirtytwo hn (mod_thirtytwo_of_fuel_four h hr)

/-- Fuel `6` of the even clock is remainder `3`. -/
theorem lemmaX_of_clock_fuel_six {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 6) (hn : 1 < n) :
    ∃ e' : Nat, ExChain n e' ∧ e' < n := by
  have hrem : Val2 (e + 5) 3 := by
    have := val2_landing h hr
    simpa using this
  exact lemmaX_of_one_light_then_three h hrem hn

/-- Fuel `9`: two lights then remainder `3`. -/
theorem lemmaX_of_clock_fuel_nine {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 9) (hn : 1 < n) :
    ∃ e' : Nat, ExChain n e' ∧ e' < n := by
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v2, u2, W2, e2, h2⟩ := exists_excursion heodd
  have hmid : Val2 (e + 5) 6 := by
    have := val2_landing h hr
    simpa using this
  have ⟨hv2, hW2⟩ := (val2_ge_four_iff h2).mp ⟨6, by omega, hmid⟩
  have h2' : IsExcursion e 2 u2 1 e2 := hv2 ▸ hW2 ▸ h2
  have hrem : Val2 (e2 + 5) 3 := by
    have := val2_landing h2' hmid
    simpa using this
  exact lemmaX_of_two_light_then_three h h2' hrem hn


/-! ## 4.  `(2, 1)` clock: drop or `OpenRemainder` -/

theorem drop_or_open_rem_two {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (n + 5) 5)
    (hrem : Val2 (e + 5) 2) (h' : IsExcursion e v' u' W' e')
    (hn : 1 < n)
    (hX : OpenRemainder n → ∃ eout : Nat, ExChain n eout ∧ eout < n) :
    ∃ eout : Nat, ExChain n eout ∧ eout < n := by
  have hvge := next_v_ge_three h hrem h'
  rcases Nat.eq_or_lt_of_le hvge with hv3 | hgt3
  · subst hv3
    rcases dichotomy_rem_two_v_three h hrem h' hn with ⟨hW, hlt⟩ | ⟨hW1, _⟩
    · exact pack_two h h' hlt
    · exact hX (open_of_clock h (open_clock_rem_two hr h' (Or.inl ⟨rfl, hW1⟩)))
  · have h4 : 4 ≤ v' := by omega
    rcases Nat.eq_or_lt_of_le h4 with hv4 | hgt4
    · subst hv4
      rcases Nat.lt_or_ge W' 3 with hWlt | hWge
      · have hW2 : W' ≤ 2 := by omega
        exact hX (open_of_clock h
          (open_clock_rem_two hr h' (Or.inr (Or.inl ⟨rfl, hW2⟩))))
      · have hlt := lemmaX_of_rem_two_v_four h hrem h' hWge hn
        exact pack_two h h' hlt
    · have h5le : 5 ≤ v' := by omega
      rcases Nat.eq_or_lt_of_le h5le with hv5 | hv6
      · subst hv5
        rcases dichotomy_rem_two_v_five h hrem h' hn with ⟨hW, hlt⟩ | ⟨hW3, _⟩
        · exact pack_two h h' hlt
        · exact hX (open_of_clock h
            (open_clock_rem_two hr h' (Or.inr (Or.inr (Or.inl ⟨rfl, hW3⟩)))))
      · have h6le : 6 ≤ v' := by omega
        rcases Nat.eq_or_lt_of_le h6le with hv6eq | hv7
        · subst hv6eq
          rcases Nat.lt_or_ge W' 4 with hWlt | hWge
          · have hW3 : W' ≤ 3 := by omega
            exact hX (open_of_clock h
              (open_clock_rem_two hr h'
                (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hW3⟩))))))
          · have hlt := lemmaX_of_two_one_then_v_six h h' hWge
            exact pack_two h h' hlt
        · exact hX (open_of_clock h
            (open_clock_rem_two hr h' (Or.inr (Or.inr (Or.inr (Or.inr hv7))))))

theorem drop_or_open_clock {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hn : 1 < n)
    (hX : OpenRemainder n → ∃ eout : Nat, ExChain n eout ∧ eout < n) :
    ∃ eout : Nat, ExChain n eout ∧ eout < n := by
  obtain ⟨r, hr⟩ := Val2.exists_of_pos (by omega : 0 < n + 5)
  have hge := val2_ge_four h hr
  rcases Nat.eq_or_lt_of_le hge with hr4 | hgt4
  · subst hr4
    exact lemmaX_of_clock_fuel_four h hr hn
  · have h5 : 5 ≤ r := by omega
    rcases Nat.eq_or_lt_of_le h5 with hr5 | hgt5
    · subst hr5
      have hrem : Val2 (e + 5) 2 := by
        have := val2_landing h hr
        simpa using this
      have heodd : e % 2 = 1 := h.2.2.1
      obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
      exact drop_or_open_rem_two h hr hrem h' hn hX
    · have h6 : 6 ≤ r := by omega
      rcases Nat.eq_or_lt_of_le h6 with hr6 | hgt6
      · subst hr6
        exact lemmaX_of_clock_fuel_six h hr hn
      · have h7 : 7 ≤ r := by omega
        rcases Nat.eq_or_lt_of_le h7 with hr7 | hgt7
        · subst hr7
          exact hX (open_of_clock h (open_clock_fuel_seven hr))
        · have h8 : 8 ≤ r := by omega
          rcases Nat.eq_or_lt_of_le h8 with hr8 | hgt8
          · subst hr8
            exact hX (open_of_clock h (open_clock_fuel_eight hr))
          · have h9 : 9 ≤ r := by omega
            rcases Nat.eq_or_lt_of_le h9 with hr9 | hgt9
            · subst hr9
              exact lemmaX_of_clock_fuel_nine h hr hn
            · exact hX (open_of_clock h (open_clock_fuel_long hr hgt9))


/-! ## 5.  `(3, 1)` leftover: drop or `OpenRemainder` -/

theorem drop_or_open_leftover_five {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 5) (hn : 1 < n)
    (hX : OpenRemainder n → ∃ eout : Nat, ExChain n eout ∧ eout < n) :
    ∃ eout : Nat, ExChain n eout ∧ eout < n := by
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have hv' := exit_one_is_v_one h hr h'
  have h'1 : IsExcursion e 1 u' W' e' := hv' ▸ h'
  have he4 := exit_one_mod_four h hr
  have hr1 : Val2 (e + 5) 1 := Val2.one_iff.mpr (by omega)
  rcases dichotomy_land_one h hr1 h'1 hn with ⟨_, hlt⟩ | ⟨hW1, _⟩
  · exact pack_two h h' hlt
  · have h'W : IsExcursion e 1 u' 1 e' := hW1 ▸ h'1
    exact hX (open_of_leftover h (open_leftover_seventy_one hr h'W))

theorem drop_or_open_leftover_six {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 6) (hn : 1 < n)
    (hX : OpenRemainder n → ∃ eout : Nat, ExChain n eout ∧ eout < n) :
    ∃ eout : Nat, ExChain n eout ∧ eout < n := by
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have hv' := exit_two_is_v_two h hr h'
  have h'2 : IsExcursion e 2 u' W' e' := hv' ▸ h'
  have hW1 : 1 ≤ W' := IsExcursion.one_le_W h'2
  rcases Nat.eq_or_lt_of_le hW1 with heq | hgt
  · have h'W : IsExcursion e 2 u' 1 e' := heq ▸ h'2
    exact hX (open_of_leftover h (open_leftover_then_light hr h'W))
  · have h2 : 2 ≤ W' := by omega
    have hr3 : Val2 (e + 5) 3 := (val2_eq_three_iff h'2).mpr ⟨rfl, h2⟩
    exact lemmaX_of_v_three_land_three h hr3 hn

theorem drop_or_open_leftover_seven {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 7) (hn : 1 < n)
    (hX : OpenRemainder n → ∃ eout : Nat, ExChain n eout ∧ eout < n) :
    ∃ eout : Nat, ExChain n eout ∧ eout < n := by
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have hvge := exit_three_v_ge_four h hr h'
  have hr2 : Val2 (e + 5) 2 := val2_of_v_ge_three h' (Nat.le_trans (by omega : 3 ≤ 4) hvge)
  rcases Nat.eq_or_lt_of_le hvge with hv4 | hv5
  · subst hv4
    rcases Nat.lt_or_ge W' 4 with hWlt | hWge
    · have hW3 : W' ≤ 3 := by omega
      exact hX (open_of_leftover h
        (open_leftover_fuel_seven hr h' (Or.inl ⟨rfl, hW3⟩)))
    · have hlt := lemmaX_of_land_two_v_four h hr2 h' hWge hn
      exact pack_two h h' hlt
  · exact hX (open_of_leftover h (open_leftover_fuel_seven hr h' (Or.inr hv5)))

theorem v_eq_three_of_fifteen_mod_sixteen {e v' u' W' e' : Nat}
    (h' : IsExcursion e v' u' W' e') (h16 : e % 16 = 7) : v' = 3 := by
  have hval : Val2 (e + 1) 3 := by
    refine Val2.of_mod ?_
    have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
    rw [hpow]
    omega
  exact Val2.unique (val2_succ_of h') hval

theorem drop_or_open_leftover_eight {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 8) (hn : 1 < n)
    (hX : OpenRemainder n → ∃ eout : Nat, ExChain n eout ∧ eout < n) :
    ∃ eout : Nat, ExChain n eout ∧ eout < n := by
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have he16 := exit_four_mod_sixteen h hr
  have hv' := v_eq_three_of_fifteen_mod_sixteen h' he16
  have h'3 : IsExcursion e 3 u' W' e' := hv' ▸ h'
  have hr2 : Val2 (e + 5) 2 := Val2.two_iff.mpr (by omega)
  have hWne : W' ≠ 1 := by
    intro h1
    have h'1 : IsExcursion e 3 u' 1 e' := h1 ▸ h'3
    exact not_second_light h hr (by omega : 8 < 9) h'1
  have hW2le : 2 ≤ W' := by
    have := IsExcursion.one_le_W h'3
    omega
  rcases Nat.eq_or_lt_of_le hW2le with hW2 | hW3
  · have h'W : IsExcursion e 3 u' 2 e' := hW2 ▸ h'3
    exact hX (open_of_leftover h (open_leftover_fuel_eight_W_two hr h'W))
  · have h3 : 3 ≤ W' := by omega
    have hlt := lemmaX_of_land_two_v_three h hr2 h'3 h3 hn
    exact pack_two h h' hlt

theorem drop_or_open_leftover {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hn : 1 < n)
    (hX : OpenRemainder n → ∃ eout : Nat, ExChain n eout ∧ eout < n) :
    ∃ eout : Nat, ExChain n eout ∧ eout < n := by
  obtain ⟨r, hr⟩ := Val2.exists_of_pos (by omega : 0 < 11 * n + 19)
  have hge := val2_ge_five h hr
  rcases Nat.eq_or_lt_of_le hge with hr5 | hgt5
  · subst hr5
    exact drop_or_open_leftover_five h hr hn hX
  · have h6 : 6 ≤ r := by omega
    rcases Nat.eq_or_lt_of_le h6 with hr6 | hgt6
    · subst hr6
      exact drop_or_open_leftover_six h hr hn hX
    · have h7 : 7 ≤ r := by omega
      rcases Nat.eq_or_lt_of_le h7 with hr7 | hgt7
      · subst hr7
        exact drop_or_open_leftover_seven h hr hn hX
      · have h8 : 8 ≤ r := by omega
        rcases Nat.eq_or_lt_of_le h8 with hr8 | hgt8
        · subst hr8
          exact drop_or_open_leftover_eight h hr hn hX
        · exact hX (open_of_leftover h (open_leftover_fuel_long hr hgt8))


/-! ## 6.  First-excursion split, and the reduction -/

theorem u_three_mod_four_of_v_three_heavy {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 3) (hW : 2 ≤ W) : u % 4 = 3 := by
  subst hv
  have hu : u % 2 = 1 := h.2.1
  have hne : u % 4 ≠ 1 := by
    intro hu1
    have hW1 := W_eq_one_of_odd_v_u_one_mod_four h (by decide : (3 : Nat) % 2 = 1) hu1
    omega
  omega

/-- Lemma X on every odd `n > 1` that is not `OpenRemainder`. -/
theorem lemmaX_of_not_open {n : Nat} (hn : 1 < n) (hodd : n % 2 = 1)
    (hX : OpenRemainder n → ∃ e : Nat, ExChain n e ∧ e < n) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  rcases Nat.lt_trichotomy v 2 with hlt | heq | hgt
  · have hv : v = 1 := by
      have : 0 < v := h.2.2.2.1
      omega
    exact lemmaX_of_val2_one hn hodd (val2_of_v_one h hv)
  · subst heq
    rcases Nat.lt_or_ge W 2 with hWlt | hWge
    · have hW1 : W = 1 := by
        have := IsExcursion.one_le_W h
        omega
      subst hW1
      exact drop_or_open_clock h hn hX
    · exact lemmaX_of_val2_three hn hodd ((val2_eq_three_iff h).mpr ⟨rfl, hWge⟩)
  · have h3 : 3 ≤ v := by omega
    rcases Nat.eq_or_lt_of_le h3 with hv3 | hv4
    · subst hv3
      rcases Nat.lt_or_ge W 2 with hWlt | hWge
      · have hW1 : W = 1 := by
          have := IsExcursion.one_le_W h
          omega
        subst hW1
        exact drop_or_open_leftover h hn hX
      · have hu4 := u_three_mod_four_of_v_three_heavy h rfl hWge
        have ⟨hchain, hlt⟩ := lemmaX_of_excursion_v_three h rfl hu4 hn
        exact ⟨e, hchain, hlt⟩
    · exact hX (open_of_v_ge_four h hv4)

/-- **Collatz follows from Lemma X on `OpenRemainder`.**  The plus-five
leftover `{ v₂ = 2 } ∪ { v₂ ≥ 4 }` is split by the first excursion and the
two clocks; every closed letter is an existing lemmaX theorem. -/
theorem collatz_of_open_remainder
    (hX : ∀ n : Nat, 1 < n → n % 2 = 1 → OpenRemainder n →
      ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  collatz_of_lemmaX fun n hodd hn => lemmaX_of_not_open hn hodd (hX n hn hodd)


/-! ## 7.  Strictly inside the plus-five leftover -/

/-- Every `OpenRemainder` start still has plus-five valuation `2` or `≥ 4`. -/
theorem open_remainder_in_plus_five {n : Nat}
    (_hodd : n % 2 = 1) (hopen : OpenRemainder n) :
    ∃ r : Nat, Val2 (n + 5) r ∧ (r = 2 ∨ 4 ≤ r) := by
  obtain ⟨v, u, W, e, h, hcases⟩ := hopen
  rcases hcases with ⟨hv, hW, _⟩ | ⟨hv, hW, _⟩ | hv4
  · obtain ⟨r, hr⟩ := Val2.exists_of_pos (by omega : 0 < n + 5)
    refine ⟨r, hr, Or.inr ?_⟩
    have h21 : IsExcursion n 2 u 1 e := hv ▸ hW ▸ h
    exact val2_ge_four h21 hr
  · have h31 : IsExcursion n 3 u 1 e := hv ▸ hW ▸ h
    exact ⟨2, val2_of_v_ge_three h31 (by omega), Or.inl rfl⟩
  · have : 3 ≤ v := by omega
    exact ⟨2, val2_of_v_ge_three h this, Or.inl rfl⟩

/-- The closed seed `11` (clock fuel `4`) is leftover but not open. -/
theorem eleven_not_open : ¬ OpenRemainder 11 := by
  intro hopen
  obtain ⟨v, u, W, e, h, hcases⟩ := hopen
  have hvuniq := excursion_v_unique h eleven_val2.2
  rcases hcases with ⟨hv2, hW, hc⟩ | ⟨hv3, _, _⟩ | hv4
  · subst hv2
    subst hW
    obtain ⟨r, hr, hfuel⟩ := hc
    have : r = 4 := Val2.unique hr eleven_val2.1
    subst this
    rcases hfuel with ⟨h5, _⟩ | h7 | h8 | h10
    · omega
    · omega
    · omega
    · omega
  · omega
  · omega

end ExcursionChain
end Collatz

section AxiomAudit
open Collatz.ExcursionChain
#print axioms OpenRemainder
#print axioms lemmaX_of_eleven_fuel_five_heavy
#print axioms lemmaX_of_one_light_then_three
#print axioms collatz_of_open_remainder
#print axioms open_remainder_in_plus_five
#print axioms eleven_not_open
end AxiomAudit
