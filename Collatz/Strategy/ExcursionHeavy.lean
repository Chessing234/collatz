import Collatz.Strategy.ExcursionMap

/-!
# One-step drop when the extra halvings beat every cofactor

For an excursion `n + 1 = 2^v u` with odd cofactor `u` and landing
`3^v u = 2^W e + 1`, the exact test `e < n` is

  `3^v u + 2^W ≤ 2^{v+W} u`.

The right-hand side grows with `u`, and the ratio tends to `3^v / 2^{v+W}`.
Clearing the cofactor gives a threshold with no `u` left in it:

  `3^v ≤ 2^W (2^v - 1)`.

This inequality is necessary and sufficient for the drop test to hold for
every positive cofactor. Sufficiency is the new closure: every such
excursion lands strictly below its start, with no lower bound on `n` and no
restriction to a single residue class. Necessity is the cofactor `u = 1`,
so replacing `2^v - 1` by any smaller constant would fail for that cofactor.

Concrete heavy pairs include `(v, W) = (4, 3)` and `(5, 3)`. The bound does
not fire for `W = 1` once `v ≥ 2`: those runs are light, and the
Mersenne-type obstruction is unchanged.

For `v ≥ 2` the two strict inequalities `2^W (2^v − 1) < 3^v < 2^{v+W}`
can hold for at most one `W`, namely `W = ⌈log₂(3^v)⌉ − v`. Every shorter
halving count is absolutely light, and every longer one is heavy. `W ≥ v ≥ 2`
is always on the heavy side. So is every `W ≥ v − ⌊127v/306⌋`, for every
`v ≥ 2`. The single boundary count is classified for every even pair
`(v, W)`, and for every run length from `2` through `128`. It is also
heavy whenever `gcd(v, ⌈log₂(3^v)⌉) ≥ 2`, including odd lengths such as
`9`. It is also heavy when the ceiling grows by two from length `v − 1`
to length `v`, which covers lengths that share no factor with the ceiling,
such as `4`. From one length to the next the ceiling grows by one or by
two, and a growth of one is isolated: the previous and the next growth are
two. The one-step boundary stays open only for that isolated growth when
the ceiling is also coprime to the length, as with length `5`; through
length `128` even those are heavy. The case
`v = 1`, `W = 1` is the known exception the bound does not cover.

This is not a proof of Collatz. Light runs, including every `(v, 1)` with
`v ≥ 2`, stay in the remaining input. The boundary check stops at `128`.
Past that length the boundary can sit strictly below `v − ⌊127v/306⌋`.
-/

namespace Collatz
namespace ExcursionHeavy

open Collatz.Arith Collatz.ExcursionMap


/-! ## 1.  The cofactor-free threshold -/

/-- The drop test at cofactor one is the threshold `3^v ≤ 2^W (2^v - 1)`. -/
theorem threshold_of_one {v W : Nat} (hv : 1 ≤ v)
    (hle : 3 ^ v + 2 ^ W ≤ 2 ^ (v + W)) :
    3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  have _hv := hv
  have hrestore : 2 ^ v = (2 ^ v - 1) + 1 := (Nat.sub_add_cancel (one_le_two_pow v)).symm
  have hsplit : 2 ^ (v + W) = 2 ^ W * (2 ^ v - 1) + 2 ^ W := by
    calc
      2 ^ (v + W) = 2 ^ W * 2 ^ v := by rw [Nat.add_comm, Nat.pow_add]
      _ = 2 ^ W * ((2 ^ v - 1) + 1) := congrArg (fun t => 2 ^ W * t) hrestore
      _ = 2 ^ W * (2 ^ v - 1) + 2 ^ W * 1 := by rw [Nat.mul_add]
      _ = 2 ^ W * (2 ^ v - 1) + 2 ^ W := by rw [Nat.mul_one]
  rw [hsplit] at hle
  exact Nat.le_of_add_le_add_right hle

/-- Every positive cofactor drops if and only if `u = 1` does. -/
theorem all_u_drop_iff {v W : Nat} (hv : 1 ≤ v) (hW : 1 ≤ W) :
    (∀ u : Nat, 1 ≤ u → 3 ^ v * u + 2 ^ W ≤ 2 ^ (v + W) * u) ↔
      3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  have _hW := hW
  constructor
  · intro h
    have h1 := h 1 (by omega)
    exact threshold_of_one hv (by simpa [Nat.mul_one] using h1)
  · intro hb u hu
    have hden : (2 ^ v - 1) * u ≤ 2 ^ v * u - 1 := by
      have hsub : (2 ^ v - 1) * u = 2 ^ v * u - u := by
        simpa [Nat.one_mul] using (Nat.sub_mul (2 ^ v) 1 u)
      rw [hsub]
      exact Nat.sub_le_sub_left hu _
    have hscale : 3 ^ v * u ≤ 2 ^ W * ((2 ^ v - 1) * u) := by
      calc
        3 ^ v * u ≤ (2 ^ W * (2 ^ v - 1)) * u := Nat.mul_le_mul_right u hb
        _ = 2 ^ W * ((2 ^ v - 1) * u) := by ac_rfl
    have hpush : 2 ^ W * ((2 ^ v - 1) * u) ≤ 2 ^ W * (2 ^ v * u - 1) :=
      Nat.mul_le_mul_left _ hden
    have hmain : 3 ^ v * u ≤ 2 ^ W * (2 ^ v * u - 1) := Nat.le_trans hscale hpush
    have hfactor : 2 ^ W * (2 ^ v * u - 1) + 2 ^ W = 2 ^ (v + W) * u := by
      have hpos : 1 ≤ 2 ^ v * u := by
        have h2 : 1 ≤ 2 ^ v := one_le_two_pow v
        exact Nat.mul_le_mul h2 hu
      have hsucc : (2 ^ v * u - 1) + 1 = 2 ^ v * u := Nat.sub_add_cancel hpos
      calc
        2 ^ W * (2 ^ v * u - 1) + 2 ^ W
            = 2 ^ W * (2 ^ v * u - 1) + 2 ^ W * 1 := by rw [Nat.mul_one]
        _ = 2 ^ W * ((2 ^ v * u - 1) + 1) := by rw [← Nat.mul_add]
        _ = 2 ^ W * (2 ^ v * u) := by rw [hsucc]
        _ = (2 ^ W * 2 ^ v) * u := by rw [Nat.mul_assoc]
        _ = 2 ^ (W + v) * u := by rw [← Nat.pow_add]
        _ = 2 ^ (v + W) * u := by rw [Nat.add_comm]
    exact Nat.le_trans (Nat.add_le_add_right hmain _) (Nat.le_of_eq hfactor)


/-! ## 2.  Every heavy excursion drops -/

/-- **Uniform one-step drop.**  If the extra halvings beat `2^v - 1` in the
sense above, the landing is strictly below the start. -/
theorem drop_of_heavy {n v u W e : Nat} (h : IsExcursion n v u W e)
    (hb : 3 ^ v ≤ 2 ^ W * (2 ^ v - 1)) : e < n := by
  have hv : 1 ≤ v := h.2.2.2.1
  have hW : 1 ≤ W := IsExcursion.one_le_W h
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  exact (drop_iff h).mpr ((all_u_drop_iff hv hW).mpr hb u hu)

/-- The threshold is sharp at cofactor one: if it fails, `u = 1` fails the
drop test. -/
theorem not_all_u_of_light {v W : Nat} (hv : 1 ≤ v) (_hW : 1 ≤ W)
    (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v) :
    ¬ 3 ^ v * 1 + 2 ^ W ≤ 2 ^ (v + W) * 1 := by
  intro hle
  have hb := threshold_of_one hv (by simpa [Nat.mul_one] using hle)
  omega


/-! ## 3.  Witnesses: the split is realized -/

/-- `15 = 2^4 - 1` is heavy: four odd steps and four halvings, landing at `5`. -/
theorem fifteen_excursion : IsExcursion 15 4 1 4 5 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem fifteen_heavy : 3 ^ 4 ≤ 2 ^ 4 * (2 ^ 4 - 1) := by decide

theorem fifteen_drops : (5 : Nat) < 15 :=
  drop_of_heavy fifteen_excursion fifteen_heavy

/-- `(v, W) = (4, 3)` is heavy, and `(4, 2)` is not. -/
theorem four_three_heavy : 3 ^ 4 ≤ 2 ^ 3 * (2 ^ 4 - 1) := by decide

theorem four_two_light : 2 ^ 2 * (2 ^ 4 - 1) < 3 ^ 4 := by decide

/-- `47` is the light `(4, 1)` seed: the first landing `121` does not drop. -/
theorem forty_seven_excursion : IsExcursion 47 4 3 1 121 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

theorem forty_seven_light : 2 ^ 1 * (2 ^ 4 - 1) < 3 ^ 4 := by decide

theorem forty_seven_no_first_drop : ¬ acceleratedOrbit (4 + 1) 47 < 47 := by
  have h := forty_seven_excursion
  have hlight : 2 ^ (4 + 1) ≤ 3 ^ 4 := by decide
  have hge := no_drop_of_light h hlight
  intro hlt
  have hland := landing_eq h
  omega

/-- The classical one-step class `v = 1`, `W = 1` is exactly the gap the
threshold does not cover: `u = 1` fails, while every `u ≥ 3` still drops.
That positive statement is `lemmaX_of_one_mod_four`, not this bound. -/
theorem v_one_W_one_not_uniform : ¬ 3 ^ 1 ≤ 2 ^ 1 * (2 ^ 1 - 1) := by decide


/-! ## 4.  At least as many halvings as odd steps -/

/-- `3^v + 2^v ≤ 4^v` for `v ≥ 2`, written as a power of two. -/
theorem three_add_two_le_sq {v : Nat} (hv : 2 ≤ v) :
    3 ^ v + 2 ^ v ≤ 2 ^ (2 * v) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
  clear hv
  induction k with
  | zero => decide
  | succ k ih =>
    have h3sum : 3 * 3 ^ (2 + k) + 3 * 2 ^ (2 + k) ≤ 3 * 2 ^ (2 * (2 + k)) := by
      have hmul : 3 * (3 ^ (2 + k) + 2 ^ (2 + k)) ≤ 3 * 2 ^ (2 * (2 + k)) :=
        Nat.mul_le_mul_left 3 ih
      simpa [Nat.mul_add] using hmul
    have htwo : 2 * 2 ^ (2 + k) + 2 ^ (2 + k) = 3 * 2 ^ (2 + k) := by
      calc
        2 * 2 ^ (2 + k) + 2 ^ (2 + k) = 2 * 2 ^ (2 + k) + 1 * 2 ^ (2 + k) := by
          rw [Nat.one_mul]
        _ = (2 + 1) * 2 ^ (2 + k) := by rw [Nat.add_mul]
        _ = 3 * 2 ^ (2 + k) := by rw [show (2 + 1 : Nat) = 3 by decide]
    have hadd : 3 * 3 ^ (2 + k) + 2 * 2 ^ (2 + k) + 2 ^ (2 + k) =
        3 * 3 ^ (2 + k) + 3 * 2 ^ (2 + k) := by
      calc
        3 * 3 ^ (2 + k) + 2 * 2 ^ (2 + k) + 2 ^ (2 + k)
            = 3 * 3 ^ (2 + k) + (2 * 2 ^ (2 + k) + 2 ^ (2 + k)) := by
              rw [Nat.add_assoc]
        _ = 3 * 3 ^ (2 + k) + 3 * 2 ^ (2 + k) := by rw [htwo]
    have hle : 3 * 3 ^ (2 + k) + 2 * 2 ^ (2 + k) + 2 ^ (2 + k) ≤
        3 * 2 ^ (2 * (2 + k)) := by
      rw [hadd]
      exact h3sum
    have hsub : 3 * 3 ^ (2 + k) + 2 * 2 ^ (2 + k) ≤
        3 * 2 ^ (2 * (2 + k)) - 2 ^ (2 + k) :=
      Nat.le_sub_of_add_le hle
    have h3le4 : 3 * 2 ^ (2 * (2 + k)) ≤ 4 * 2 ^ (2 * (2 + k)) :=
      Nat.mul_le_mul_right _ (by decide : (3 : Nat) ≤ 4)
    have hdrop : 3 * 2 ^ (2 * (2 + k)) - 2 ^ (2 + k) ≤ 4 * 2 ^ (2 * (2 + k)) :=
      Nat.le_trans (Nat.sub_le _ _) h3le4
    have hstep : 3 * 3 ^ (2 + k) + 2 * 2 ^ (2 + k) ≤ 4 * 2 ^ (2 * (2 + k)) :=
      Nat.le_trans hsub hdrop
    have hexp3 : 2 + (k + 1) = (2 + k) + 1 := by omega
    have hexp2 : 2 + 2 * (2 + k) = 2 * (2 + (k + 1)) := by omega
    calc
      3 ^ (2 + (k + 1)) + 2 ^ (2 + (k + 1))
          = 3 * 3 ^ (2 + k) + 2 * 2 ^ (2 + k) := by
            rw [hexp3, three_pow_succ, two_pow_succ]
      _ ≤ 4 * 2 ^ (2 * (2 + k)) := hstep
      _ = 2 ^ 2 * 2 ^ (2 * (2 + k)) := by rw [show (4 : Nat) = 2 ^ 2 by decide]
      _ = 2 ^ (2 + 2 * (2 + k)) := by rw [← Nat.pow_add]
      _ = 2 ^ (2 * (2 + (k + 1))) := by rw [hexp2]

/-- **Long halvings are heavy.**  `W ≥ v ≥ 2` puts every positive cofactor
strictly below the start. -/
theorem heavy_of_W_ge_v {v W : Nat} (hv : 2 ≤ v) (hW : v ≤ W) :
    3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  have hsum := three_add_two_le_sq hv
  have htwo : 2 ^ v ≤ 2 ^ (2 * v) := two_pow_le_two_pow (by omega : v ≤ 2 * v)
  have hle : 3 ^ v ≤ 2 ^ (2 * v) - 2 ^ v := Nat.le_sub_of_add_le hsum
  have hid : 2 ^ v * (2 ^ v - 1) = 2 ^ (2 * v) - 2 ^ v := by
    have h1 : 1 ≤ 2 ^ v := one_le_two_pow v
    calc
      2 ^ v * (2 ^ v - 1) = 2 ^ v * 2 ^ v - 2 ^ v := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ (v + v) - 2 ^ v := by rw [← Nat.pow_add]
      _ = 2 ^ (2 * v) - 2 ^ v := by rw [← Nat.two_mul]
  have hbase : 3 ^ v ≤ 2 ^ v * (2 ^ v - 1) := by
    rw [hid]
    exact hle
  exact Nat.le_trans hbase (Nat.mul_le_mul_right _ (two_pow_le_two_pow hW))

theorem drop_of_W_ge_v {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : 2 ≤ v) (hW : v ≤ W) : e < n :=
  drop_of_heavy h (heavy_of_W_ge_v hv hW)


/-! ## 4b.  A third of the halving margin, for every run length -/

/-- Same margin survives one longer run. -/
theorem margin_same {v c : Nat} (hc : c ≤ v)
    (h : 3 ^ v ≤ 2 ^ (v - c) * (2 ^ v - 1)) :
    3 ^ (v + 1) ≤ 2 ^ (v + 1 - c) * (2 ^ (v + 1) - 1) := by
  have hshift : v + 1 - c = (v - c) + 1 := by omega
  have hthree : 3 * (2 ^ v - 1) ≤ 2 * (2 ^ (v + 1) - 1) := by
    have hL : 3 * (2 ^ v - 1) + 3 = 3 * 2 ^ v := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      exact Nat.sub_add_cancel (Nat.mul_le_mul_left 3 (one_le_two_pow v))
    have hR : 2 * (2 ^ (v + 1) - 1) + 2 = 4 * 2 ^ v := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [Nat.sub_add_cancel (Nat.mul_le_mul_left 2 (one_le_two_pow (v + 1)))]
      rw [two_pow_succ, show (4 : Nat) = 2 * 2 by decide]
      ac_rfl
    have h3le4 : 3 * 2 ^ v ≤ 4 * 2 ^ v :=
      Nat.mul_le_mul_right _ (by decide : (3 : Nat) ≤ 4)
    have hsum : 3 * (2 ^ v - 1) + 3 ≤ 2 * (2 ^ (v + 1) - 1) + 3 := by
      have h12 : 3 * (2 ^ v - 1) + 3 ≤ 2 * (2 ^ (v + 1) - 1) + 2 := by
        rw [hL, hR]
        exact h3le4
      exact Nat.le_trans h12 (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _)
    exact Nat.le_of_add_le_add_right hsum
  have hexp : 2 ^ (v + 1 - c) = 2 * 2 ^ (v - c) := by
    rw [hshift, two_pow_succ]
  have hleft : 3 * (2 ^ (v - c) * (2 ^ v - 1)) =
      2 ^ (v - c) * (3 * (2 ^ v - 1)) := by ac_rfl
  have hright : 2 * 2 ^ (v - c) * (2 ^ (v + 1) - 1) =
      2 ^ (v - c) * (2 * (2 ^ (v + 1) - 1)) := by ac_rfl
  have hscale : 3 * 3 ^ v ≤ 3 * (2 ^ (v - c) * (2 ^ v - 1)) :=
    Nat.mul_le_mul_left 3 h
  have hcmp : 3 * (2 ^ (v - c) * (2 ^ v - 1)) ≤
      2 * 2 ^ (v - c) * (2 ^ (v + 1) - 1) := by
    rw [hleft, hright]
    exact Nat.mul_le_mul_left _ hthree
  rw [three_pow_succ, hexp]
  exact Nat.le_trans hscale hcmp

/-- Three more odd steps pay for one more unit of margin. -/
theorem margin_block {m : Nat} (_hm : 1 ≤ m)
    (h : 3 ^ (3 * m) ≤ 2 ^ (2 * m) * (2 ^ (3 * m) - 1)) :
    3 ^ (3 * (m + 1)) ≤ 2 ^ (2 * (m + 1)) * (2 ^ (3 * (m + 1)) - 1) := by
  have hmul : 27 * 3 ^ (3 * m) ≤ 27 * (2 ^ (2 * m) * (2 ^ (3 * m) - 1)) :=
    Nat.mul_le_mul_left 27 h
  have hpow : 3 ^ (3 * (m + 1)) = 27 * 3 ^ (3 * m) := by
    have hexp : 3 * (m + 1) = 3 + 3 * m := by omega
    rw [hexp, three_pow_add]
  have hcore : 27 * (2 ^ (3 * m) - 1) ≤ 4 * (2 ^ (3 * m + 3) - 1) := by
    have hL : 27 * (2 ^ (3 * m) - 1) + 27 = 27 * 2 ^ (3 * m) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      exact Nat.sub_add_cancel (Nat.mul_le_mul_left 27 (one_le_two_pow (3 * m)))
    have hR : 4 * (2 ^ (3 * m + 3) - 1) + 4 = 32 * 2 ^ (3 * m) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [Nat.sub_add_cancel (Nat.mul_le_mul_left 4 (one_le_two_pow (3 * m + 3)))]
      have hexp : 3 * m + 3 = 3 + 3 * m := by omega
      rw [hexp, Nat.pow_add]
      have h8 : (2 : Nat) ^ 3 = 8 := by decide
      rw [h8, ← Nat.mul_assoc]
    have hcoeff : 27 * 2 ^ (3 * m) ≤ 32 * 2 ^ (3 * m) :=
      Nat.mul_le_mul_right _ (by decide : (27 : Nat) ≤ 32)
    have hsum : 27 * (2 ^ (3 * m) - 1) + 27 ≤
        4 * (2 ^ (3 * m + 3) - 1) + 27 := by
      rw [hL]
      have hrest : 27 * 2 ^ (3 * m) ≤ 4 * (2 ^ (3 * m + 3) - 1) + 4 := by
        rw [← hR] at hcoeff
        exact hcoeff
      exact Nat.le_trans hrest (Nat.add_le_add_left (by decide : (4 : Nat) ≤ 27) _)
    exact Nat.le_of_add_le_add_right hsum
  have hleft : 27 * (2 ^ (2 * m) * (2 ^ (3 * m) - 1)) =
      2 ^ (2 * m) * (27 * (2 ^ (3 * m) - 1)) := by ac_rfl
  have hright : 2 ^ (2 * (m + 1)) * (2 ^ (3 * (m + 1)) - 1) =
      2 ^ (2 * m) * (4 * (2 ^ (3 * m + 3) - 1)) := by
    have h2 : 2 * (m + 1) = 2 * m + 2 := by omega
    have h3 : 3 * (m + 1) = 3 * m + 3 := by omega
    rw [h2, h3, Nat.pow_add]
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    rw [h4]
    ac_rfl
  have hcmp : 27 * (2 ^ (2 * m) * (2 ^ (3 * m) - 1)) ≤
      2 ^ (2 * (m + 1)) * (2 ^ (3 * (m + 1)) - 1) := by
    rw [hleft, hright]
    exact Nat.mul_le_mul_left _ hcore
  rw [hpow]
  exact Nat.le_trans hmul hcmp

theorem margin_multiple (m : Nat) (hm : 1 ≤ m) :
    3 ^ (3 * m) ≤ 2 ^ (2 * m) * (2 ^ (3 * m) - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => decide
  | succ k ih =>
    have h := margin_block (by omega : 1 ≤ 1 + k) ih
    simpa [show (1 + k) + 1 = 1 + (k + 1) by omega,
      Nat.mul_add, Nat.add_assoc, Nat.mul_one] using h

/-- **One third of the halvings may be missing.**  For every `v ≥ 3`,
`3^v ≤ 2^{v − ⌊v/3⌋} (2^v − 1)`. -/
theorem heavy_margin_third {v : Nat} (hv : 3 ≤ v) :
    3 ^ v ≤ 2 ^ (v - v / 3) * (2 ^ v - 1) := by
  have hq : 1 ≤ v / 3 := by omega
  have hbase := margin_multiple (v / 3) hq
  have hbase' : 3 ^ (3 * (v / 3)) ≤
      2 ^ (3 * (v / 3) - v / 3) * (2 ^ (3 * (v / 3)) - 1) := by
    rw [show 3 * (v / 3) - v / 3 = 2 * (v / 3) by omega]
    exact hbase
  have hr : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
  rcases hr with _h0 | _h1 | _h2
  · have hv0 : 3 * (v / 3) = v := by omega
    have hexp : (3 * (v / 3)) - (3 * (v / 3)) / 3 = 2 * (v / 3) := by omega
    rw [← hv0, hexp]
    exact hbase
  · have hs := margin_same (by omega : v / 3 ≤ 3 * (v / 3)) hbase'
    calc
      3 ^ v = 3 ^ (3 * (v / 3) + 1) := by
        exact congrArg (fun t => 3 ^ t) (by omega : v = 3 * (v / 3) + 1)
      _ ≤ 2 ^ ((3 * (v / 3) + 1) - v / 3) * (2 ^ (3 * (v / 3) + 1) - 1) := hs
      _ = 2 ^ (v - v / 3) * (2 ^ v - 1) := by
        rw [show 3 * (v / 3) + 1 = v by omega]
  · have hs1 := margin_same (by omega : v / 3 ≤ 3 * (v / 3)) hbase'
    have hs2 := margin_same (by omega : v / 3 ≤ 3 * (v / 3) + 1) hs1
    calc
      3 ^ v = 3 ^ ((3 * (v / 3) + 1) + 1) := by
        exact congrArg (fun t => 3 ^ t) (by omega : v = (3 * (v / 3) + 1) + 1)
      _ ≤ 2 ^ (((3 * (v / 3) + 1) + 1) - v / 3) *
          (2 ^ ((3 * (v / 3) + 1) + 1) - 1) := hs2
      _ = 2 ^ (v - v / 3) * (2 ^ v - 1) := by
        rw [show (3 * (v / 3) + 1) + 1 = v by omega]

/-- Every cofactor drops once `W` reaches `v − ⌊v/3⌋`. -/
theorem heavy_of_margin_third {v W : Nat} (hv : 3 ≤ v) (hW : v - v / 3 ≤ W) :
    3 ^ v ≤ 2 ^ W * (2 ^ v - 1) :=
  Nat.le_trans (heavy_margin_third hv)
    (Nat.mul_le_mul_right _ (two_pow_le_two_pow hW))

theorem drop_of_margin_third {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : 3 ≤ v) (hW : v - v / 3 ≤ W) : e < n :=
  drop_of_heavy h (heavy_of_margin_third hv hW)


/-! ## 4c.  The convergent margin ⌊127v/306⌋ -/

/-- Stepping forward by 306 odd steps raises the halving budget by 127
and the surviving power of two by 179. -/
theorem margin_shift_306 (v : Nat) :
    (v + 306) - 127 * (v + 306) / 306 = v - 127 * v / 306 + 179 := by
  have hmul : 127 * (v + 306) = 306 * 127 + 127 * v := by
    calc
      127 * (v + 306) = 127 * v + 127 * 306 := by rw [Nat.mul_add]
      _ = 127 * v + 306 * 127 := by rw [Nat.mul_comm 127 306]
      _ = 306 * 127 + 127 * v := by rw [Nat.add_comm]
  rw [hmul, Nat.mul_add_div (by decide : 0 < 306) 127 (127 * v)]
  have hq : 127 * v / 306 ≤ v := by
    have hle : 127 * v ≤ 306 * v :=
      Nat.mul_le_mul_right v (by decide : (127 : Nat) ≤ 306)
    have hdiv : 127 * v / 306 ≤ 306 * v / 306 := Nat.div_le_div_right hle
    rwa [Nat.mul_div_cancel_left v (by decide : 0 < 306)] at hdiv
  rw [← Nat.sub_sub]
  rw [Nat.add_sub_assoc (by decide : (127 : Nat) ≤ 306)]
  rw [Nat.add_comm v (306 - 127), Nat.add_sub_assoc hq, Nat.add_comm]

/-- `3^306 ≤ 2^485` pays for one block, for every length. -/
theorem margin_core_306 (v : Nat) :
    3 ^ 306 * (2 ^ v - 1) ≤ 2 ^ 179 * (2 ^ (v + 306) - 1) := by
  have hL : 3 ^ 306 * (2 ^ v - 1) + 3 ^ 306 = 3 ^ 306 * 2 ^ v := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    exact Nat.sub_add_cancel <| by
      simpa [Nat.mul_one] using Nat.mul_le_mul_left (3 ^ 306) (one_le_two_pow v)
  have hR : 2 ^ 179 * (2 ^ (v + 306) - 1) + 2 ^ 179 = 2 ^ 485 * 2 ^ v := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [Nat.sub_add_cancel <| by
      simpa [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ 179) (one_le_two_pow (v + 306))]
    have hv306 : 2 ^ (v + 306) = 2 ^ v * 2 ^ 306 := Nat.pow_add 2 v 306
    rw [hv306, ← Nat.mul_assoc, Nat.mul_right_comm]
    have h485 : 2 ^ 179 * 2 ^ 306 = 2 ^ 485 := by
      have hsum : 179 + 306 = 485 := by decide
      rw [← Nat.pow_add, hsum]
    rw [h485]
  have hpow : (3 : Nat) ^ 306 ≤ 2 ^ 485 := by decide
  have hsmall : (2 : Nat) ^ 179 ≤ 3 ^ 306 := by decide
  have hcoeff : 3 ^ 306 * 2 ^ v ≤ 2 ^ 485 * 2 ^ v := Nat.mul_le_mul_right _ hpow
  have hrest : 3 ^ 306 * 2 ^ v ≤ 2 ^ 179 * (2 ^ (v + 306) - 1) + 2 ^ 179 := by
    rw [hR]
    exact hcoeff
  have hsum : 3 ^ 306 * (2 ^ v - 1) + 3 ^ 306 ≤
      2 ^ 179 * (2 ^ (v + 306) - 1) + 3 ^ 306 := by
    rw [hL]
    exact Nat.le_trans hrest (Nat.add_le_add_left hsmall _)
  exact Nat.le_of_add_le_add_right hsum

theorem margin_jump_306 {v : Nat}
    (h : 3 ^ v ≤ 2 ^ (v - 127 * v / 306) * (2 ^ v - 1)) :
    3 ^ (v + 306) ≤
      2 ^ ((v + 306) - 127 * (v + 306) / 306) * (2 ^ (v + 306) - 1) := by
  have hmul : 3 ^ 306 * 3 ^ v ≤
      3 ^ 306 * (2 ^ (v - 127 * v / 306) * (2 ^ v - 1)) :=
    Nat.mul_le_mul_left _ h
  have hpow : 3 ^ (v + 306) = 3 ^ 306 * 3 ^ v := by
    rw [Nat.add_comm v 306, three_pow_add]
  have hexp := margin_shift_306 v
  have hcore := margin_core_306 v
  rw [hpow, hexp]
  calc
    3 ^ 306 * 3 ^ v ≤ 3 ^ 306 * (2 ^ (v - 127 * v / 306) * (2 ^ v - 1)) := hmul
    _ = 2 ^ (v - 127 * v / 306) * (3 ^ 306 * (2 ^ v - 1)) := by
      rw [Nat.mul_left_comm]
    _ ≤ 2 ^ (v - 127 * v / 306) * (2 ^ 179 * (2 ^ (v + 306) - 1)) :=
      Nat.mul_le_mul_left _ hcore
    _ = 2 ^ (v - 127 * v / 306 + 179) * (2 ^ (v + 306) - 1) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add]

/-- The inequality at one run length. -/
def margin306Ok (v : Nat) : Bool :=
  decide (3 ^ v ≤ 2 ^ (v - 127 * v / 306) * (2 ^ v - 1))

/-- Run lengths `2` through `n`. -/
def margins306Ok : Nat → Bool
  | 0 => true
  | n + 1 => if n + 1 < 2 then true else margin306Ok (n + 1) && margins306Ok n

theorem margins306Ok_sound : ∀ n v, margins306Ok n = true → 2 ≤ v → v ≤ n →
    margin306Ok v = true := by
  intro n
  induction n with
  | zero =>
    intro v _ hv hvn
    omega
  | succ n ih =>
    intro v h hv hvn
    by_cases h2 : n + 1 < 2
    · omega
    · have hif : margins306Ok (n + 1) =
          (if n + 1 < 2 then true else margin306Ok (n + 1) && margins306Ok n) := rfl
      rw [hif, if_neg h2, Bool.and_eq_true] at h
      by_cases hlast : v = n + 1
      · rw [hlast]
        exact h.1
      · exact ih v h.2 hv (by omega)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem margins306_through_307 : margins306Ok 307 = true := by
  decide

/-- **The convergent margin.**  For every `v ≥ 2`,
`3^v ≤ 2^{v − ⌊127v/306⌋} (2^v − 1)`. -/
theorem heavy_margin_306 (v : Nat) (hv : 2 ≤ v) :
    3 ^ v ≤ 2 ^ (v - 127 * v / 306) * (2 ^ v - 1) := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hle : v ≤ 307
    · have hb := margins306Ok_sound 307 v margins306_through_307 hv hle
      simpa [margin306Ok, decide_eq_true_eq] using hb
    · have ih' := ih (v - 306) (by omega) (by omega : 2 ≤ v - 306)
      have hjump := margin_jump_306 ih'
      simpa [show v - 306 + 306 = v by omega] using hjump

/-- Every cofactor drops once `W` reaches `v − ⌊127v/306⌋`. -/
theorem heavy_of_margin_306 {v W : Nat} (hv : 2 ≤ v)
    (hW : v - 127 * v / 306 ≤ W) :
    3 ^ v ≤ 2 ^ W * (2 ^ v - 1) :=
  Nat.le_trans (heavy_margin_306 v hv)
    (Nat.mul_le_mul_right _ (two_pow_le_two_pow hW))

theorem drop_of_margin_306 {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : 2 ≤ v)
    (hW : v - 127 * v / 306 ≤ W) : e < n :=
  drop_of_heavy h (heavy_of_margin_306 hv hW)


/-! ## 5.  Off the binary length, the split is exact -/

/-- Least `k` with `n < 2^k`, for `n ≥ 1`.  Fuel `n` is enough. -/
def twoCeil (n : Nat) : Nat :=
  go n n
where
  go (fuel n : Nat) : Nat :=
    match fuel with
    | 0 => 1
    | fuel + 1 => if n ≤ 1 then 1 else go fuel (n / 2) + 1

theorem twoCeil.go_spec (fuel n : Nat) (hn : 1 ≤ n) (hf : n ≤ fuel + 1) :
    2 ^ (twoCeil.go fuel n - 1) ≤ n ∧ n < 2 ^ twoCeil.go fuel n := by
  induction fuel generalizing n with
  | zero =>
    have hn1 : n = 1 := by omega
    subst hn1
    simp [twoCeil.go]
  | succ fuel ih =>
    by_cases h1 : n ≤ 1
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [twoCeil.go]
    · have hpos : 1 ≤ n / 2 := by omega
      have hf' : n / 2 ≤ fuel + 1 := by omega
      have ih' := ih (n / 2) hpos hf'
      have hdef : twoCeil.go (fuel + 1) n = twoCeil.go fuel (n / 2) + 1 := by
        simp [twoCeil.go, h1]
      rw [hdef]
      have hc : 1 ≤ twoCeil.go fuel (n / 2) := by
        rcases Nat.eq_zero_or_pos (twoCeil.go fuel (n / 2)) with hz | hp
        · have hlt := ih'.2
          rw [hz, Nat.pow_zero] at hlt
          omega
        · omega
      constructor
      · have hexp : twoCeil.go fuel (n / 2) + 1 - 1 = twoCeil.go fuel (n / 2) := by
          omega
        rw [hexp]
        have hpow : 2 ^ twoCeil.go fuel (n / 2) =
            2 * 2 ^ (twoCeil.go fuel (n / 2) - 1) := by
          have hc1 : twoCeil.go fuel (n / 2) =
              (twoCeil.go fuel (n / 2) - 1) + 1 := by omega
          have hcong : 2 ^ twoCeil.go fuel (n / 2) =
              2 ^ ((twoCeil.go fuel (n / 2) - 1) + 1) :=
            congrArg (fun t => 2 ^ t) hc1
          rw [hcong, two_pow_succ]
        have hmul : 2 * 2 ^ (twoCeil.go fuel (n / 2) - 1) ≤ 2 * (n / 2) :=
          Nat.mul_le_mul_left 2 ih'.1
        have hhalf : 2 * (n / 2) ≤ n := by omega
        exact Nat.le_trans (Nat.le_trans (Nat.le_of_eq hpow) hmul) hhalf
      · have hlehalf : n / 2 ≤ 2 ^ twoCeil.go fuel (n / 2) - 1 := by
          have : 1 ≤ 2 ^ twoCeil.go fuel (n / 2) := one_le_two_pow _
          omega
        have hodd : n ≤ 2 * (n / 2) + 1 := by omega
        have hmul : 2 * (n / 2) + 1 ≤
            2 * (2 ^ twoCeil.go fuel (n / 2) - 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 2 hlehalf) 1
        have hid : 2 * (2 ^ twoCeil.go fuel (n / 2) - 1) + 1 =
            2 ^ (twoCeil.go fuel (n / 2) + 1) - 1 := by
          have hsub : 2 * (2 ^ twoCeil.go fuel (n / 2) - 1) =
              2 ^ (twoCeil.go fuel (n / 2) + 1) - 2 := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← two_pow_succ]
          rw [hsub]
          have h2 : 2 ≤ 2 ^ (twoCeil.go fuel (n / 2) + 1) := by
            have : (2 : Nat) ^ 1 ≤ 2 ^ (twoCeil.go fuel (n / 2) + 1) :=
              two_pow_le_two_pow (by omega)
            simpa using this
          omega
        have hle : n ≤ 2 ^ (twoCeil.go fuel (n / 2) + 1) - 1 :=
          Nat.le_trans (Nat.le_trans hodd hmul) (Nat.le_of_eq hid)
        have hposp : 1 ≤ 2 ^ (twoCeil.go fuel (n / 2) + 1) := one_le_two_pow _
        omega

theorem twoCeil_spec {n : Nat} (hn : 1 ≤ n) :
    2 ^ (twoCeil n - 1) ≤ n ∧ n < 2 ^ twoCeil n := by
  simpa [twoCeil] using twoCeil.go_spec n n hn (Nat.le_succ n)

/-- The binary ceiling is the only exponent with `2^{k−1} ≤ n < 2^k`. -/
theorem twoCeil_eq_of_bounds {n k : Nat} (hn : 1 ≤ n)
    (hlo : 2 ^ (k - 1) ≤ n) (hhi : n < 2 ^ k) : twoCeil n = k := by
  have spec := twoCeil_spec hn
  generalize hcdef : twoCeil n = c at spec
  have hkpos : 1 ≤ k := (Nat.one_le_iff_ne_zero).2 (by
    intro hz
    rw [hz, Nat.pow_zero] at hhi
    exact absurd hn (Nat.not_le_of_gt hhi))
  have hcpos : 1 ≤ c := (Nat.one_le_iff_ne_zero).2 (by
    intro hz
    rw [hz, Nat.pow_zero] at spec
    exact absurd hn (Nat.not_le_of_gt spec.2))
  have hkc : k ≤ c := by
    have hlt : 2 ^ (k - 1) < 2 ^ c := Nat.lt_of_le_of_lt hlo spec.2
    have hexp : k - 1 < c := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hlt
    have : k - 1 + 1 ≤ c := Nat.succ_le_of_lt hexp
    rwa [Nat.sub_add_cancel hkpos] at this
  have hck : c ≤ k := by
    have hlt : 2 ^ (c - 1) < 2 ^ k := Nat.lt_of_le_of_lt spec.1 hhi
    have hexp : c - 1 < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hlt
    have : c - 1 + 1 ≤ k := Nat.succ_le_of_lt hexp
    rwa [Nat.sub_add_cancel hcpos] at this
  exact Nat.le_antisymm hck hkc

/-- Fewer halvings than the binary length of `3^v` is an absolute light run:
`2^{v+W} ≤ 3^v`, so no positive cofactor drops in one step. -/
theorem light_below_ceil {v W : Nat} (h : v + W + 1 ≤ twoCeil (3 ^ v)) :
    2 ^ (v + W) ≤ 3 ^ v := by
  have h3 : 1 ≤ 3 ^ v := by
    have : 0 < 3 ^ v := three_pow_pos v
    omega
  have spec := twoCeil_spec h3
  have hk : v + W ≤ twoCeil (3 ^ v) - 1 := by omega
  exact Nat.le_trans (two_pow_le_two_pow hk) spec.1

/-- More halvings than the binary length is heavy. -/
theorem heavy_above_ceil {v W : Nat} (hv : 1 ≤ v)
    (hge : twoCeil (3 ^ v) + 1 ≤ v + W) :
    3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  have h3 : 1 ≤ 3 ^ v := by
    have : 0 < 3 ^ v := three_pow_pos v
    omega
  have spec := twoCeil_spec h3
  generalize hkdef : twoCeil (3 ^ v) = k at spec hge
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hz | hp
    · have hlt := spec.2
      rw [hz, Nat.pow_zero] at hlt
      omega
    · omega
  have hvk : v < k := by
    rcases Nat.lt_or_ge v k with h | h
    · exact h
    · have hle : 2 ^ k ≤ 2 ^ v := two_pow_le_two_pow h
      have h23 : 2 ^ v ≤ 3 ^ v := two_pow_le_three_pow v
      omega
  have hW0 : (k - v) + 1 ≤ W := by omega
  have hmono : 2 ^ ((k - v) + 1) * (2 ^ v - 1) ≤ 2 ^ W * (2 ^ v - 1) :=
    Nat.mul_le_mul_right _ (two_pow_le_two_pow hW0)
  have hsplit : 2 ^ ((k - v) + 1) * (2 ^ v - 1) =
      2 ^ (k + 1) - 2 ^ ((k - v) + 1) := by
    have hpow : 2 ^ ((k - v) + 1) * 2 ^ v = 2 ^ (k + 1) := by
      rw [← Nat.pow_add]
      have : (k - v) + 1 + v = k + 1 := by omega
      rw [this]
    calc
      2 ^ ((k - v) + 1) * (2 ^ v - 1)
          = 2 ^ ((k - v) + 1) * 2 ^ v - 2 ^ ((k - v) + 1) := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ (k + 1) - 2 ^ ((k - v) + 1) := by rw [hpow]
  have hthree : 3 ^ v ≤ 2 ^ k - 1 := by
    have : 1 ≤ 2 ^ k := one_le_two_pow k
    omega
  have hband : 2 ^ ((k - v) + 1) ≤ 2 ^ k :=
    two_pow_le_two_pow (by omega : (k - v) + 1 ≤ k)
  have hdiff : 2 ^ k ≤ 2 ^ (k + 1) - 2 ^ ((k - v) + 1) := by
    have hdup : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
      rw [two_pow_succ, ← Nat.two_mul]
    have hle : 2 ^ ((k - v) + 1) + 2 ^ k ≤ 2 ^ (k + 1) := by
      have hsum : 2 ^ ((k - v) + 1) + 2 ^ k ≤ 2 ^ k + 2 ^ k :=
        Nat.add_le_add_right hband _
      rwa [hdup] at hsum
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hle)
  have hmain : 3 ^ v ≤ 2 ^ ((k - v) + 1) * (2 ^ v - 1) := by
    rw [hsplit]
    exact Nat.le_trans (Nat.le_trans hthree (by
      have : 1 ≤ 2 ^ k := one_le_two_pow k
      omega)) hdiff
  exact Nat.le_trans hmain hmono


/-! ## 6.  Even run length and even extra halvings -/

private theorem diff_sq {x y : Nat} (hyx : y ≤ x) :
    (x - y) * (x + y) = x * x - y * y := by
  have hyy : y * y ≤ y * x := Nat.mul_le_mul_left y hyx
  have hyx2 : y * x ≤ x * x := Nat.mul_le_mul_right x hyx
  have hsum : (x * x - y * x) + (y * x - y * y) + y * y = x * x := by
    calc
      (x * x - y * x) + (y * x - y * y) + y * y
          = (x * x - y * x) + ((y * x - y * y) + y * y) := by rw [Nat.add_assoc]
      _ = (x * x - y * x) + y * x := by rw [Nat.sub_add_cancel hyy]
      _ = x * x := Nat.sub_add_cancel hyx2
  have hsplit : (x - y) * (x + y) =
      (x * x - y * x) + (y * x - y * y) := by
    calc
      (x - y) * (x + y) = (x - y) * x + (x - y) * y := Nat.mul_add _ _ _
      _ = (x * x - y * x) + (x * y - y * y) := by
        rw [Nat.sub_mul x y x, Nat.sub_mul x y y]
      _ = (x * x - y * x) + (y * x - y * y) := by rw [Nat.mul_comm x y]
  have hjoin : (x - y) * (x + y) + y * y = x * x := by
    rw [hsplit]
    exact hsum
  exact Nat.eq_sub_of_add_eq hjoin

/-- **No gap on even pairs.**  If `v ≥ 2` and `W ≥ 1` are both even, either
every positive cofactor drops in one step, or none does. -/
theorem no_gap_even {v W : Nat} (hv : 2 ≤ v) (_hW : 1 ≤ W)
    (hvEven : v % 2 = 0) (hWEven : W % 2 = 0) :
    2 ^ (v + W) ≤ 3 ^ v ∨ 3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  by_cases hlong : v ≤ W
  · exact Or.inr (heavy_of_W_ge_v hv hlong)
  · rcases Nat.lt_or_ge (3 ^ v) (2 ^ (v + W)) with hlt | hge
    · rcases Nat.lt_or_ge (2 ^ W * (2 ^ v - 1)) (3 ^ v) with hgap | hheavy
      · exfalso
        have hv_dvd : 2 ∣ v := (Nat.dvd_iff_mod_eq_zero).mpr hvEven
        have hW_dvd : 2 ∣ W := (Nat.dvd_iff_mod_eq_zero).mpr hWEven
        have hv_eq : v = 2 * (v / 2) := by
          rw [Nat.mul_comm]
          exact (Nat.div_mul_cancel hv_dvd).symm
        have hW_eq : W = 2 * (W / 2) := by
          rw [Nat.mul_comm]
          exact (Nat.div_mul_cancel hW_dvd).symm
        let t := v / 2
        let s := W / 2
        have hts : s + 1 ≤ t := by
          have : 2 * s < 2 * t := by
            rw [← hW_eq, ← hv_eq]
            omega
          omega
        have hy_lt : 3 ^ t < 2 ^ (t + s) := by
          rcases Nat.lt_or_ge (3 ^ t) (2 ^ (t + s)) with h | hle
          · exact h
          · have hsq := Nat.mul_le_mul hle hle
            have hpow2 : 2 ^ (t + s) * 2 ^ (t + s) = 2 ^ (v + W) := by
              rw [← Nat.pow_add]
              have : t + s + (t + s) = v + W := by
                have ht2 : t + t = v := by rw [← Nat.two_mul t, hv_eq]
                have hs2 : s + s = W := by rw [← Nat.two_mul s, hW_eq]
                omega
              rw [this]
            have hpow3 : 3 ^ t * 3 ^ t = 3 ^ v := by
              rw [← Nat.pow_add]
              have : t + t = v := by rw [← Nat.two_mul t, hv_eq]
              rw [this]
            rw [hpow2, hpow3] at hsq
            omega
        have hsplit : 2 ^ W * (2 ^ v - 1) = 2 ^ (v + W) - 2 ^ W := by
          have hpow : 2 ^ W * 2 ^ v = 2 ^ (v + W) := by
            rw [Nat.mul_comm, ← Nat.pow_add]
          calc
            2 ^ W * (2 ^ v - 1) = 2 ^ W * 2 ^ v - 2 ^ W := by
              rw [Nat.mul_sub_left_distrib, Nat.mul_one]
            _ = 2 ^ (v + W) - 2 ^ W := by rw [hpow]
        have hsub : 2 ^ (v + W) - 2 ^ W < 3 ^ v := by
          rw [← hsplit]
          exact hgap
        have hpowW : 2 ^ W ≤ 2 ^ (v + W) := two_pow_le_two_pow (Nat.le_add_left _ _)
        have hsum : 2 ^ (v + W) < 3 ^ v + 2 ^ W := by
          have : 2 ^ (v + W) - 2 ^ W + 2 ^ W < 3 ^ v + 2 ^ W :=
            Nat.add_lt_add_right hsub _
          rwa [Nat.sub_add_cancel hpowW] at this
        have h3le : 3 ^ v ≤ 2 ^ (v + W) := Nat.le_of_lt hlt
        have hdiff : 2 ^ (v + W) - 3 ^ v < 2 ^ W := by
          have : 2 ^ (v + W) - 3 ^ v + 3 ^ v < 2 ^ W + 3 ^ v := by
            rw [Nat.sub_add_cancel h3le]
            simpa [Nat.add_comm, Nat.add_left_comm] using hsum
          exact Nat.lt_of_add_lt_add_right this
        let x := 2 ^ (t + s)
        let y := 3 ^ t
        have hyx : y ≤ x := Nat.le_of_lt hy_lt
        have hprod : (x - y) * (x + y) = x * x - y * y := diff_sq hyx
        have hxx : x * x = 2 ^ (v + W) := by
          rw [show x * x = 2 ^ (t + s) * 2 ^ (t + s) by rfl, ← Nat.pow_add]
          have : t + s + (t + s) = v + W := by
            have ht2 : t + t = v := by rw [← Nat.two_mul t, hv_eq]
            have hs2 : s + s = W := by rw [← Nat.two_mul s, hW_eq]
            omega
          rw [this]
        have hyy : y * y = 3 ^ v := by
          rw [show y * y = 3 ^ t * 3 ^ t by rfl, ← Nat.pow_add]
          have : t + t = v := by rw [← Nat.two_mul t, hv_eq]
          rw [this]
        have hAB : (x - y) * (x + y) = 2 ^ (v + W) - 3 ^ v := by
          rw [hprod, hxx, hyy]
        have hA : 1 ≤ x - y := by omega
        have hy1 : 1 ≤ y := Nat.one_le_pow t 3 (by decide)
        have hgrow : x + 1 ≤ (x - y) * (x + y) := by
          have hB : x + 1 ≤ x + y := Nat.add_le_add_left hy1 x
          have hmul : x + y ≤ (x - y) * (x + y) := by
            have hone : 1 * (x + y) ≤ (x - y) * (x + y) :=
              Nat.mul_le_mul_right (x + y) hA
            simpa [Nat.one_mul] using hone
          exact Nat.le_trans hB hmul
        have hx : 2 ^ (2 * s + 1) ≤ x := by
          have : 2 * s + 1 ≤ t + s := by omega
          simpa [x] using two_pow_le_two_pow this
        have hbig : 2 ^ W < 2 ^ (2 * s + 1) := by
          have : W = 2 * s := hW_eq
          rw [this]
          exact two_pow_lt_two_pow (by omega)
        have hgt : 2 ^ W < (x - y) * (x + y) :=
          Nat.lt_of_lt_of_le
            (Nat.lt_trans (Nat.lt_of_lt_of_le hbig hx) (Nat.lt_succ_self x)) hgrow
        have hAB_lt : (x - y) * (x + y) < 2 ^ W := by
          rw [hAB]
          exact hdiff
        exact Nat.lt_irrefl _ (Nat.lt_trans hgt hAB_lt)
      · exact Or.inr hheavy
    · exact Or.inl hge


/-! ## 6b.  A shared factor forces the boundary to be heavy -/

private theorem three_pow_lt_four_pow (v : Nat) (hv : 1 ≤ v) : 3 ^ v < 4 ^ v := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hv
  clear hv
  induction t with
  | zero => decide
  | succ t ih =>
    have h3 : 3 * 3 ^ (1 + t) < 4 * 3 ^ (1 + t) :=
      Nat.mul_lt_mul_of_pos_right (by decide : (3 : Nat) < 4) (three_pow_pos (1 + t))
    have h4 : 4 * 3 ^ (1 + t) < 4 * 4 ^ (1 + t) :=
      Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 4)
    have hshift : 1 + (t + 1) = (1 + t) + 1 := by omega
    rw [hshift, three_pow_succ]
    have h4pow : 4 * 4 ^ (1 + t) = 4 ^ ((1 + t) + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [← h4pow]
    exact Nat.lt_trans h3 h4

private theorem twoCeil_three_le (v : Nat) (hv : 1 ≤ v) : twoCeil (3 ^ v) ≤ 2 * v := by
  have h3 : 1 ≤ 3 ^ v := by
    have : 0 < 3 ^ v := three_pow_pos v
    omega
  have spec := twoCeil_spec h3
  have hlt : 3 ^ v < 2 ^ (2 * v) := by
    have h4 : 4 ^ v = 2 ^ (2 * v) := by
      rw [show (4 : Nat) = 2 ^ 2 by decide, ← Nat.pow_mul]
    rw [← h4]
    exact three_pow_lt_four_pow v hv
  generalize hkdef : twoCeil (3 ^ v) = k at spec
  rcases Nat.lt_or_ge k (2 * v + 1) with hltk | hge
  · omega
  · have hexp : 2 * v ≤ k - 1 := by omega
    have hpow : 2 ^ (2 * v) ≤ 2 ^ (k - 1) := two_pow_le_two_pow hexp
    have hle : 2 ^ (k - 1) ≤ 3 ^ v := spec.1
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans hpow hle) hlt) (Nat.lt_irrefl _)

/-- `x^n − y^n` clears the leading power of `x`, with one left over. -/
private theorem pow_sub_succ {x y n : Nat} (hn : 2 ≤ n) (hy : 1 ≤ y) (hxy : y < x) :
    x ^ (n - 1) + 1 ≤ x ^ n - y ^ n := by
  have hn1 : n - 1 + 1 = n := by omega
  have hx : x ^ n = x ^ (n - 1) * x := by
    calc
      x ^ n = x ^ (n - 1 + 1) := congrArg (fun t => x ^ t) hn1.symm
      _ = x ^ (n - 1) * x := Nat.pow_succ _ _
  have hyx : y ≤ x := Nat.le_of_lt hxy
  have hyxn : y * x ^ (n - 1) ≤ x ^ n := by
    rw [hx, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hyx
  have hyn : y ^ n = y ^ (n - 1) * y := by
    calc
      y ^ n = y ^ (n - 1 + 1) := congrArg (fun t => y ^ t) hn1.symm
      _ = y ^ (n - 1) * y := Nat.pow_succ _ _
  have hyy : y ^ n ≤ y * x ^ (n - 1) := by
    rw [hyn, Nat.mul_comm (y ^ (n - 1)) y]
    exact Nat.mul_le_mul_left y (Nat.pow_le_pow_left hyx (n - 1))
  have hhead : x ^ n - y * x ^ (n - 1) = (x - y) * x ^ (n - 1) := by
    calc
      x ^ n - y * x ^ (n - 1) = x ^ (n - 1) * x - y * x ^ (n - 1) := by rw [hx]
      _ = x * x ^ (n - 1) - y * x ^ (n - 1) := by rw [Nat.mul_comm (x ^ (n - 1)) x]
      _ = (x - y) * x ^ (n - 1) := by rw [Nat.sub_mul]
  have htail : y * x ^ (n - 1) - y ^ n = y * (x ^ (n - 1) - y ^ (n - 1)) := by
    rw [hyn, Nat.mul_comm (y ^ (n - 1)) y, ← Nat.mul_sub_left_distrib]
  have hsplit : x ^ n - y ^ n =
      (x ^ n - y * x ^ (n - 1)) + (y * x ^ (n - 1) - y ^ n) := by
    have hsum : (x ^ n - y * x ^ (n - 1)) + (y * x ^ (n - 1) - y ^ n) + y ^ n = x ^ n := by
      calc
        (x ^ n - y * x ^ (n - 1)) + (y * x ^ (n - 1) - y ^ n) + y ^ n
            = (x ^ n - y * x ^ (n - 1)) + ((y * x ^ (n - 1) - y ^ n) + y ^ n) := by
              rw [Nat.add_assoc]
        _ = (x ^ n - y * x ^ (n - 1)) + y * x ^ (n - 1) := by rw [Nat.sub_add_cancel hyy]
        _ = x ^ n := Nat.sub_add_cancel hyxn
    exact (Nat.eq_sub_of_add_eq hsum).symm
  have hpowlt : y ^ (n - 1) < x ^ (n - 1) :=
    Nat.pow_lt_pow_left hxy (by omega : n - 1 ≠ 0)
  have hpos : 1 ≤ x ^ (n - 1) - y ^ (n - 1) := by omega
  have htail1 : 1 ≤ y * (x ^ (n - 1) - y ^ (n - 1)) := by
    have hone : 1 ≤ y * 1 := by simpa using hy
    exact Nat.le_trans hone (Nat.mul_le_mul_left y hpos)
  have hhead1 : x ^ (n - 1) ≤ (x - y) * x ^ (n - 1) := by
    have hxy1 : 1 ≤ x - y := by omega
    have : 1 * x ^ (n - 1) ≤ (x - y) * x ^ (n - 1) :=
      Nat.mul_le_mul_right _ hxy1
    simpa using this
  calc
    x ^ (n - 1) + 1 ≤ (x - y) * x ^ (n - 1) + y * (x ^ (n - 1) - y ^ (n - 1)) :=
      Nat.add_le_add hhead1 htail1
    _ = x ^ n - y ^ n := by rw [← hhead, ← htail, hsplit]

/-- **Shared factors close the boundary.**  If `v ≥ 2` and
`gcd(v, ⌈log₂(3^v)⌉) ≥ 2`, the single candidate halving count is heavy. -/
theorem heavy_boundary_of_common_factor {v : Nat} (hv : 2 ≤ v)
    (hfac : 2 ≤ Nat.gcd v (twoCeil (3 ^ v))) :
    3 ^ v ≤ 2 ^ (twoCeil (3 ^ v) - v) * (2 ^ v - 1) := by
  have h3 : 1 ≤ 3 ^ v := by
    have : 0 < 3 ^ v := three_pow_pos v
    omega
  have spec := twoCeil_spec h3
  generalize hkdef : twoCeil (3 ^ v) = k at spec hfac
  have hdv : Nat.gcd v k ∣ v := Nat.gcd_dvd_left v k
  have hdk : Nat.gcd v k ∣ k := Nat.gcd_dvd_right v k
  generalize hddef : Nat.gcd v k = d at hdv hdk hfac
  have hd2 : 2 ≤ d := hfac
  have hk2 : k ≤ 2 * v := by
    have hk := twoCeil_three_le v (by omega)
    rwa [hkdef] at hk
  have hkd : k ≤ d * v := Nat.le_trans hk2 (Nat.mul_le_mul_right v hd2)
  have hk1mul : d * (k / d) = k := Nat.mul_div_cancel' hdk
  have hv1mul : d * (v / d) = v := Nat.mul_div_cancel' hdv
  have hk1le0 : k / d ≤ v := Nat.div_le_of_le_mul (k := d) hkd
  generalize hk1def : k / d = k1 at hk1mul hk1le0
  generalize hv1def : v / d = v1 at hv1mul
  have ha : (2 ^ k1) ^ d = 2 ^ k := by
    rw [← Nat.pow_mul]
    have : k1 * d = k := by
      rw [Nat.mul_comm]
      exact hk1mul
    rw [this]
  have hb : (3 ^ v1) ^ d = 3 ^ v := by
    rw [← Nat.pow_mul]
    have : v1 * d = v := by
      rw [Nat.mul_comm]
      exact hv1mul
    rw [this]
  have hpow : (3 ^ v1) ^ d < (2 ^ k1) ^ d := by
    rw [ha, hb]
    exact spec.2
  have hba : 3 ^ v1 < 2 ^ k1 :=
    (Nat.pow_lt_pow_iff_left (by omega : d ≠ 0)).1 hpow
  have hv1pos : 1 ≤ v1 := by
    have hpos : 0 < v / d :=
      Nat.div_pos (Nat.le_of_dvd (by omega : 0 < v) hdv) (by omega : 0 < d)
    rwa [hv1def] at hpos
  have hb1 : 1 ≤ 3 ^ v1 := Nat.one_le_pow v1 3 (by decide)
  have hdiff : (2 ^ k1) ^ (d - 1) + 1 ≤ (2 ^ k1) ^ d - (3 ^ v1) ^ d :=
    pow_sub_succ hd2 hb1 hba
  have haexp : (2 ^ k1) ^ (d - 1) = 2 ^ (k - k1) := by
    rw [← Nat.pow_mul]
    have hmul : k1 * (d - 1) = k - k1 := by
      have hsum : k1 * (d - 1) + k1 = k := by
        calc
          k1 * (d - 1) + k1 = k1 * (d - 1) + k1 * 1 := by rw [Nat.mul_one]
          _ = k1 * (d - 1 + 1) := by rw [← Nat.mul_add]
          _ = k1 * d := by rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
          _ = k := by rw [Nat.mul_comm]; exact hk1mul
      exact Nat.eq_sub_of_add_eq hsum
    rw [hmul]
  have hgap : (2 ^ k1) ^ d - (3 ^ v1) ^ d = 2 ^ k - 3 ^ v := by rw [ha, hb]
  have hge : 2 ^ (k - v) ≤ (2 ^ k1) ^ d - (3 ^ v1) ^ d := by
    rcases Nat.lt_or_ge k1 v with hlt | hge
    · have hk1v : k1 ≤ v - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlt)
      have : k - v ≤ k - k1 := by omega
      have hpow : 2 ^ (k - v) ≤ 2 ^ (k - k1) := two_pow_le_two_pow this
      have : 2 ^ (k - v) ≤ (2 ^ k1) ^ (d - 1) := by rw [haexp]; exact hpow
      exact Nat.le_trans this (Nat.le_trans (Nat.le_add_right _ 1) hdiff)
    · have hk1eq : k1 = v := by omega
      have hexp : k - k1 = k - v := by rw [hk1eq]
      have : 2 ^ (k - v) + 1 ≤ (2 ^ k1) ^ d - (3 ^ v1) ^ d := by
        rw [← hexp, ← haexp]
        exact hdiff
      exact Nat.le_trans (Nat.le_add_right _ 1) this
  have hsub : 3 ^ v + 2 ^ (k - v) ≤ 2 ^ k := by
    have hle : 2 ^ (k - v) ≤ 2 ^ k - 3 ^ v := by
      rw [← hgap]
      exact hge
    have h3k : 3 ^ v ≤ 2 ^ k := Nat.le_of_lt spec.2
    have : 2 ^ (k - v) + 3 ^ v ≤ 2 ^ k := by
      have hsum : 2 ^ (k - v) + 3 ^ v ≤ (2 ^ k - 3 ^ v) + 3 ^ v :=
        Nat.add_le_add_right hle _
      rwa [Nat.sub_add_cancel h3k] at hsum
    rwa [Nat.add_comm]
  have hid : 2 ^ (k - v) * (2 ^ v - 1) = 2 ^ k - 2 ^ (k - v) := by
    calc
      2 ^ (k - v) * (2 ^ v - 1) = 2 ^ (k - v) * 2 ^ v - 2 ^ (k - v) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ k - 2 ^ (k - v) := by
        rw [← Nat.pow_add]
        have hvk : v ≤ k := by
          have h2 : 2 ^ v ≤ 3 ^ v := two_pow_le_three_pow v
          have hlt : 2 ^ v < 2 ^ k := Nat.lt_of_le_of_lt h2 spec.2
          have : v < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hlt
          omega
        have : k - v + v = k := by omega
        rw [this]
  have : 3 ^ v ≤ 2 ^ k - 2 ^ (k - v) := Nat.le_sub_of_add_le hsub
  rw [← hid] at this
  simpa [hkdef] using this

/-- Every halving count is light or heavy when the ceiling shares a factor
with the run length. -/
theorem dichotomy_of_common_factor {v W : Nat} (hv : 2 ≤ v) (hW : 1 ≤ W)
    (hfac : 2 ≤ Nat.gcd v (twoCeil (3 ^ v))) :
    2 ^ (v + W) ≤ 3 ^ v ∨ 3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  have h3 : 1 ≤ 3 ^ v := by
    have : 0 < 3 ^ v := three_pow_pos v
    omega
  have spec := twoCeil_spec h3
  have hbound := heavy_boundary_of_common_factor hv hfac
  generalize hkdef : twoCeil (3 ^ v) = k at spec hbound
  rcases Nat.lt_or_ge (v + W) k with hlt | hge
  · have hshort : v + W + 1 ≤ twoCeil (3 ^ v) := by
      rw [hkdef]
      omega
    exact Or.inl (light_below_ceil hshort)
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · have hWeq : W = k - v := by omega
      exact Or.inr (by rw [hWeq]; exact hbound)
    · have hlong : twoCeil (3 ^ v) + 1 ≤ v + W := by
        rw [hkdef]
        omega
      exact Or.inr (heavy_above_ceil (by omega : 1 ≤ v) hlong)

/-- Odd length `9` shares the factor `3` with its binary ceiling. -/
theorem nine_shares_factor : 2 ≤ Nat.gcd 9 (twoCeil (3 ^ 9)) := by
  decide

/-- **A ceiling jump of two closes the boundary.**  If `v ≥ 2` and the
binary ceiling grows by two from length `v − 1` to length `v`, the single
candidate halving count is heavy.  The defect is then larger than the
previous pure power of two, which is already enough. -/
theorem heavy_boundary_of_ceiling_jump {v : Nat} (hv : 2 ≤ v)
    (hjump : twoCeil (3 ^ (v - 1)) + 2 = twoCeil (3 ^ v)) :
    3 ^ v ≤ 2 ^ (twoCeil (3 ^ v) - v) * (2 ^ v - 1) := by
  have h3prev : 1 ≤ 3 ^ (v - 1) := three_pow_pos (v - 1)
  have h3 : 1 ≤ 3 ^ v := three_pow_pos v
  have spec0 := twoCeil_spec h3prev
  have spec := twoCeil_spec h3
  generalize hk0def : twoCeil (3 ^ (v - 1)) = k0 at spec0 hjump
  generalize hkdef : twoCeil (3 ^ v) = k at spec hjump
  have hpred : 3 ^ (v - 1) ≤ 2 ^ k0 - 1 :=
    Nat.le_sub_of_add_le (Nat.succ_le_of_lt spec0.2)
  have h3le : 3 ^ v ≤ 3 * (2 ^ k0 - 1) := by
    have hpow : 3 ^ v = 3 * 3 ^ (v - 1) := by
      have hv1 : 1 ≤ v := Nat.le_trans (by decide : (1 : Nat) ≤ 2) hv
      calc
        3 ^ v = 3 ^ ((v - 1) + 1) :=
          congrArg (fun t => 3 ^ t) (Nat.sub_add_cancel hv1).symm
        _ = 3 ^ (v - 1) * 3 := Nat.pow_succ _ _
        _ = 3 * 3 ^ (v - 1) := by rw [Nat.mul_comm]
    rw [hpow]
    exact Nat.mul_le_mul_left 3 hpred
  have hroom : 3 * (2 ^ k0 - 1) + 2 ^ k0 = 2 ^ (k0 + 2) - 3 := by
    have hmul : 3 * (2 ^ k0 - 1) = 3 * 2 ^ k0 - 3 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hthree : 3 ≤ 3 * 2 ^ k0 := Nat.mul_le_mul_left 3 (one_le_two_pow k0)
    have hgather : 3 * 2 ^ k0 + 2 ^ k0 = (3 + 1) * 2 ^ k0 := by
      simpa [Nat.one_mul] using (Nat.add_mul 3 1 (2 ^ k0)).symm
    calc
      3 * (2 ^ k0 - 1) + 2 ^ k0 = 3 * 2 ^ k0 - 3 + 2 ^ k0 := by rw [hmul]
      _ = 3 * 2 ^ k0 + 2 ^ k0 - 3 := (Nat.sub_add_comm hthree).symm
      _ = (3 + 1) * 2 ^ k0 - 3 := by rw [hgather]
      _ = 4 * 2 ^ k0 - 3 := by rw [show (3 : Nat) + 1 = 4 by rfl]
      _ = 2 ^ 2 * 2 ^ k0 - 3 := by rw [show (4 : Nat) = 2 ^ 2 by decide]
      _ = 2 ^ (2 + k0) - 3 := by rw [← Nat.pow_add]
      _ = 2 ^ (k0 + 2) - 3 := by rw [Nat.add_comm]
  have hexp : k - v ≤ k0 := by
    rw [← hjump]
    exact Nat.le_trans (Nat.sub_le_sub_left hv (k0 + 2)) (Nat.le_of_eq (Nat.add_sub_cancel k0 2))
  have h2le : 2 ^ (k - v) ≤ 2 ^ k0 := two_pow_le_two_pow hexp
  have hsum : 3 ^ v + 2 ^ (k - v) ≤ 2 ^ (k0 + 2) := by
    have hstep : 3 ^ v + 2 ^ (k - v) ≤ 3 * (2 ^ k0 - 1) + 2 ^ k0 :=
      Nat.le_trans (Nat.add_le_add_left h2le _) (Nat.add_le_add_right h3le _)
    have hslack : 3 ^ v + 2 ^ (k - v) ≤ 2 ^ (k0 + 2) - 3 := by
      rw [← hroom]
      exact hstep
    have hthree : 3 ≤ 2 ^ (k0 + 2) :=
      Nat.le_trans (by decide : (3 : Nat) ≤ 4)
        (by
          rw [show (4 : Nat) = 2 ^ 2 by decide]
          exact two_pow_le_two_pow (Nat.le_add_left 2 k0))
    have hplus : 3 ^ v + 2 ^ (k - v) + 3 ≤ 2 ^ (k0 + 2) :=
      Nat.add_le_of_le_sub (b := 3) hthree hslack
    exact Nat.le_trans (Nat.le_add_right _ 3) hplus
  have hsub : 3 ^ v + 2 ^ (k - v) ≤ 2 ^ k := by
    simpa [hjump] using hsum
  have hid : 2 ^ (k - v) * (2 ^ v - 1) = 2 ^ k - 2 ^ (k - v) := by
    calc
      2 ^ (k - v) * (2 ^ v - 1) = 2 ^ (k - v) * 2 ^ v - 2 ^ (k - v) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ k - 2 ^ (k - v) := by
        rw [← Nat.pow_add]
        have hvk : v ≤ k := by
          have h2 : 2 ^ v ≤ 3 ^ v := two_pow_le_three_pow v
          have hlt : 2 ^ v < 2 ^ k := Nat.lt_of_le_of_lt h2 spec.2
          exact Nat.le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hlt)
        rw [Nat.sub_add_cancel hvk]
  have : 3 ^ v ≤ 2 ^ k - 2 ^ (k - v) := Nat.le_sub_of_add_le hsub
  rw [← hid] at this
  simpa [hkdef] using this

/-- Every halving count is light or heavy when the ceiling grew by two. -/
theorem dichotomy_of_ceiling_jump {v W : Nat} (hv : 2 ≤ v) (hW : 1 ≤ W)
    (hjump : twoCeil (3 ^ (v - 1)) + 2 = twoCeil (3 ^ v)) :
    2 ^ (v + W) ≤ 3 ^ v ∨ 3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  have h3 : 1 ≤ 3 ^ v := three_pow_pos v
  have spec := twoCeil_spec h3
  have hbound := heavy_boundary_of_ceiling_jump hv hjump
  generalize hkdef : twoCeil (3 ^ v) = k at spec hbound
  rcases Nat.lt_or_ge (v + W) k with hlt | hge
  · have hshort : v + W + 1 ≤ twoCeil (3 ^ v) := by
      rw [hkdef]
      omega
    exact Or.inl (light_below_ceil hshort)
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · have hWeq : W = k - v := by omega
      exact Or.inr (by rw [hWeq]; exact hbound)
    · have hlong : twoCeil (3 ^ v) + 1 ≤ v + W := by
        rw [hkdef]
        omega
      exact Or.inr (heavy_above_ceil (by omega : 1 ≤ v) hlong)

/-- Length `4` is a ceiling jump of two, and it shares no factor with that ceiling. -/
theorem four_ceiling_jumps :
    twoCeil (3 ^ (4 - 1)) + 2 = twoCeil (3 ^ 4) ∧ Nat.gcd 4 (twoCeil (3 ^ 4)) = 1 := by
  decide

/-- From one run length to the next, the binary ceiling grows by one or by two. -/
theorem ceiling_step {v : Nat} (_hv : 1 ≤ v) :
    twoCeil (3 ^ (v + 1)) = twoCeil (3 ^ v) + 1 ∨
      twoCeil (3 ^ (v + 1)) = twoCeil (3 ^ v) + 2 := by
  have h3 : 1 ≤ 3 ^ v := three_pow_pos v
  have spec := twoCeil_spec h3
  generalize hkdef : twoCeil (3 ^ v) = k at spec
  have hkpos : 1 ≤ k := (Nat.one_le_iff_ne_zero).2 (by
    intro hz
    rw [hz, Nat.pow_zero] at spec
    exact absurd h3 (Nat.not_le_of_gt spec.2))
  have hkback : (k - 1) + 1 = k := Nat.sub_add_cancel hkpos
  have hmul : 3 ^ (v + 1) = 3 * 3 ^ v := three_pow_succ v
  have hlo3 : 3 * 2 ^ (k - 1) ≤ 3 ^ (v + 1) := by
    rw [hmul]
    exact Nat.mul_le_mul_left 3 spec.1
  have hhi3 : 3 ^ (v + 1) < 3 * 2 ^ k := by
    rw [hmul]
    exact Nat.mul_lt_mul_of_pos_left spec.2 (by decide : 0 < 3)
  have hsplit : 3 * 2 ^ (k - 1) = 2 ^ k + 2 ^ (k - 1) := by
    calc
      3 * 2 ^ (k - 1) = (2 + 1) * 2 ^ (k - 1) := by rw [show (3 : Nat) = 2 + 1 by rfl]
      _ = 2 * 2 ^ (k - 1) + 1 * 2 ^ (k - 1) := by rw [Nat.add_mul]
      _ = 2 ^ ((k - 1) + 1) + 2 ^ (k - 1) := by rw [Nat.one_mul, ← two_pow_succ]
      _ = 2 ^ k + 2 ^ (k - 1) := by rw [hkback]
  have hgt : 2 ^ k < 3 * 2 ^ (k - 1) := by
    rw [hsplit]
    exact Nat.lt_add_of_pos_right (one_le_two_pow (k - 1))
  have hge : 2 ^ k ≤ 3 ^ (v + 1) := Nat.le_of_lt (Nat.lt_of_lt_of_le hgt hlo3)
  have htop : 3 * 2 ^ k < 2 ^ (k + 2) := by
    have hfour : 2 ^ (k + 2) = 4 * 2 ^ k := by
      calc
        2 ^ (k + 2) = 2 ^ (k + 1 + 1) := by rw [Nat.add_assoc]
        _ = 2 * 2 ^ (k + 1) := two_pow_succ _
        _ = 2 * (2 * 2 ^ k) := by rw [two_pow_succ]
        _ = (2 * 2) * 2 ^ k := by rw [← Nat.mul_assoc]
        _ = 4 * 2 ^ k := by rw [show (2 * 2 : Nat) = 4 by rfl]
    rw [hfour]
    exact Nat.mul_lt_mul_of_pos_right (by decide : (3 : Nat) < 4) (one_le_two_pow k)
  have hhi : 3 ^ (v + 1) < 2 ^ (k + 2) := Nat.lt_trans hhi3 htop
  have h3' : 1 ≤ 3 ^ (v + 1) := three_pow_pos (v + 1)
  rcases Nat.lt_or_ge (3 ^ (v + 1)) (2 ^ (k + 1)) with hlt | hge2
  · refine Or.inl ?_
    have hlo : 2 ^ ((k + 1) - 1) ≤ 3 ^ (v + 1) := by
      simpa [Nat.add_sub_cancel] using hge
    have : twoCeil (3 ^ (v + 1)) = k + 1 := twoCeil_eq_of_bounds h3' hlo hlt
    simpa [hkdef] using this
  · refine Or.inr ?_
    have hlo : 2 ^ ((k + 2) - 1) ≤ 3 ^ (v + 1) := by
      simpa [Nat.add_sub_cancel] using hge2
    have : twoCeil (3 ^ (v + 1)) = k + 2 := twoCeil_eq_of_bounds h3' hlo hhi
    simpa [hkdef] using this

/-- A ceiling growth of one is immediately followed by a growth of two. -/
theorem one_jump_next {v : Nat} (hv : 2 ≤ v)
    (hone : twoCeil (3 ^ (v - 1)) + 1 = twoCeil (3 ^ v)) :
    twoCeil (3 ^ v) + 2 = twoCeil (3 ^ (v + 1)) := by
  have hstep := ceiling_step (Nat.le_trans (by decide : (1 : Nat) ≤ 2) hv)
  rcases hstep with hshort | hlong
  · exfalso
    have hprev : 1 ≤ 3 ^ (v - 1) := three_pow_pos (v - 1)
    have spec0 := twoCeil_spec hprev
    generalize hk0def : twoCeil (3 ^ (v - 1)) = k0 at spec0 hone
    have hkpos : 1 ≤ k0 := (Nat.one_le_iff_ne_zero).2 (by
      intro hz
      rw [hz, Nat.pow_zero] at spec0
      exact absurd hprev (Nat.not_le_of_gt spec0.2))
    have hv1 : 1 ≤ v := Nat.le_trans (by decide : (1 : Nat) ≤ 2) hv
    have hback : (v - 1) + 1 = v := Nat.sub_add_cancel hv1
    have hpow : 3 ^ v = 3 * 3 ^ (v - 1) := by
      calc
        3 ^ v = 3 ^ ((v - 1) + 1) := congrArg (fun t => 3 ^ t) hback.symm
        _ = 3 * 3 ^ (v - 1) := three_pow_succ _
    have hthree : 3 * 2 ^ (k0 - 1) ≤ 3 ^ v := by
      rw [hpow]
      exact Nat.mul_le_mul_left 3 spec0.1
    have hnine : 9 * 2 ^ (k0 - 1) ≤ 3 ^ (v + 1) := by
      rw [three_pow_succ, show (9 : Nat) = 3 * 3 by decide, Nat.mul_assoc]
      exact Nat.mul_le_mul_left 3 hthree
    have h8 : 8 * 2 ^ (k0 - 1) < 9 * 2 ^ (k0 - 1) :=
      Nat.mul_lt_mul_of_pos_right (by decide : (8 : Nat) < 9) (one_le_two_pow (k0 - 1))
    have hpow8 : 2 ^ (k0 + 2) = 8 * 2 ^ (k0 - 1) := by
      have hkback : (k0 - 1) + 1 = k0 := Nat.sub_add_cancel hkpos
      have hexp : k0 + 2 = (k0 - 1) + 3 := by
        calc
          k0 + 2 = (k0 - 1) + 1 + 2 := by rw [hkback]
          _ = (k0 - 1) + 3 := by rw [Nat.add_assoc, show (1 + 2 : Nat) = 3 by rfl]
      calc
        2 ^ (k0 + 2) = 2 ^ ((k0 - 1) + 3) := congrArg (fun t => 2 ^ t) hexp
        _ = 2 ^ 3 * 2 ^ (k0 - 1) := by rw [Nat.pow_add, Nat.mul_comm]
        _ = 8 * 2 ^ (k0 - 1) := by rw [show (2 : Nat) ^ 3 = 8 by decide]
    have hlt : 2 ^ (k0 + 2) < 3 ^ (v + 1) :=
      Nat.lt_of_lt_of_le (by rwa [← hpow8] at h8) hnine
    have hge : 2 ^ (twoCeil (3 ^ v) + 1) ≤ 3 ^ (v + 1) := by
      have : twoCeil (3 ^ v) + 1 = k0 + 2 := by
        rw [← hone]
      rw [this]
      exact Nat.le_of_lt hlt
    have h3' : 1 ≤ 3 ^ (v + 1) := three_pow_pos (v + 1)
    have spec := twoCeil_spec h3'
    rw [hshort] at spec
    exact absurd hge (Nat.not_le_of_gt spec.2)
  · exact hlong.symm

/-- For `v ≥ 3`, a ceiling growth of one is also preceded by a growth of two. -/
theorem one_jump_prev {v : Nat} (hv : 3 ≤ v)
    (hone : twoCeil (3 ^ (v - 1)) + 1 = twoCeil (3 ^ v)) :
    twoCeil (3 ^ (v - 2)) + 2 = twoCeil (3 ^ (v - 1)) := by
  have hv2 : 2 ≤ v := Nat.le_trans (by decide : (2 : Nat) ≤ 3) hv
  have hv1 : 1 ≤ v := Nat.le_trans (by decide : (1 : Nat) ≤ 2) hv2
  have hshift : (v - 2) + 1 = v - 1 := by
    have hsum : (v - 2) + 1 + 1 = (v - 1) + 1 := by
      calc
        (v - 2) + 1 + 1 = (v - 2) + 2 := by rw [Nat.add_assoc, show (1 + 1 : Nat) = 2 by rfl]
        _ = v := Nat.sub_add_cancel hv2
        _ = (v - 1) + 1 := (Nat.sub_add_cancel hv1).symm
    exact Nat.add_right_cancel hsum
  have hstep := ceiling_step (Nat.le_sub_of_add_le (by
    rw [show (1 + 2 : Nat) = 3 by decide]
    exact hv))
  rcases hstep with hshort | hlong
  · exfalso
    have hshort' : twoCeil (3 ^ (v - 1)) = twoCeil (3 ^ (v - 2)) + 1 := by
      rw [← hshift]
      exact hshort
    have hone_prev : twoCeil (3 ^ ((v - 1) - 1)) + 1 = twoCeil (3 ^ (v - 1)) := by
      have hsub : (v - 1) - 1 = v - 2 := by
        rw [Nat.sub_sub, show (1 + 1 : Nat) = 2 by rfl]
      rw [hsub]
      exact hshort'.symm
    have hbad := one_jump_next (Nat.le_sub_of_add_le (by
      rw [show (2 + 1 : Nat) = 3 by decide]
      exact hv)) hone_prev
    rw [Nat.sub_add_cancel hv1] at hbad
    have : twoCeil (3 ^ (v - 1)) + 2 = twoCeil (3 ^ (v - 1)) + 1 := by
      rw [hbad, hone]
    exact absurd (Nat.add_left_cancel this) (by decide : (2 : Nat) ≠ 1)
  · rw [hshift] at hlong
    exact hlong.symm

/-- The boundary is heavy unless the ceiling grew by one.  A shared factor
still closes that one-growth case. -/
theorem heavy_boundary_outside_one_jump {v : Nat} (hv : 2 ≤ v)
    (h : twoCeil (3 ^ (v - 1)) + 2 = twoCeil (3 ^ v) ∨
        2 ≤ Nat.gcd v (twoCeil (3 ^ v))) :
    3 ^ v ≤ 2 ^ (twoCeil (3 ^ v) - v) * (2 ^ v - 1) := by
  rcases h with hjump | hfac
  · exact heavy_boundary_of_ceiling_jump hv hjump
  · exact heavy_boundary_of_common_factor hv hfac

/-- Length `5` is an isolated ceiling growth of one, coprime to its ceiling.
This is the shape not closed by the jump or the shared factor. -/
theorem five_is_isolated_one_jump :
    twoCeil (3 ^ (5 - 1)) + 1 = twoCeil (3 ^ 5) ∧
      twoCeil (3 ^ (5 - 2)) + 2 = twoCeil (3 ^ (5 - 1)) ∧
      twoCeil (3 ^ 5) + 2 = twoCeil (3 ^ (5 + 1)) ∧
      Nat.gcd 5 (twoCeil (3 ^ 5)) = 1 := by
  decide


/-! ## 7.  The single boundary, checked through run length 128 -/

/-- The one candidate extra-halving count is heavy. -/
def boundaryOk (v : Nat) : Bool :=
  decide (3 ^ v ≤ 2 ^ (twoCeil (3 ^ v) - v) * (2 ^ v - 1))

/-- `boundariesOk n` checks run lengths `2` through `n`. -/
def boundariesOk : Nat → Bool
  | 0 => true
  | n + 1 => if n + 1 < 2 then true else boundaryOk (n + 1) && boundariesOk n

theorem boundariesOk_sound : ∀ n v, boundariesOk n = true → 2 ≤ v → v ≤ n →
    boundaryOk v = true := by
  intro n
  induction n with
  | zero =>
    intro v _ hv hvn
    omega
  | succ n ih =>
    intro v h hv hvn
    by_cases h2 : n + 1 < 2
    · omega
    · have hif : boundariesOk (n + 1) =
          (if n + 1 < 2 then true else boundaryOk (n + 1) && boundariesOk n) := rfl
      rw [hif, if_neg h2, Bool.and_eq_true] at h
      by_cases hlast : v = n + 1
      · rw [hlast]
        exact h.1
      · exact ih v h.2 hv (by omega)

/-- **One-step dichotomy up to a checked run length.**  For `2 ≤ v ≤ n`,
either `2^{v+W} ≤ 3^v` or the cofactor-free threshold holds.  The
certificate only has to look at `W = ⌈log₂(3^v)⌉ − v`. -/
theorem dichotomy_of_boundary {n v W : Nat} (hv : 2 ≤ v) (hW : 1 ≤ W)
    (hvn : v ≤ n) (hcert : boundariesOk n = true) :
    2 ^ (v + W) ≤ 3 ^ v ∨ 3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  have hb := boundariesOk_sound n v hcert hv hvn
  have hdec : decide (3 ^ v ≤ 2 ^ (twoCeil (3 ^ v) - v) * (2 ^ v - 1)) = true := by
    simpa [boundaryOk] using hb
  have hbound := of_decide_eq_true hdec
  have h3 : 1 ≤ 3 ^ v := by
    have : 0 < 3 ^ v := three_pow_pos v
    omega
  have spec := twoCeil_spec h3
  generalize hkdef : twoCeil (3 ^ v) = k at hbound spec
  rcases Nat.lt_or_ge (v + W) k with hlt | hge
  · have hshort : v + W + 1 ≤ twoCeil (3 ^ v) := by
      rw [hkdef]
      omega
    exact Or.inl (light_below_ceil hshort)
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · have hWeq : W = k - v := by omega
      have hbound' : 3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
        rw [hWeq]
        exact hbound
      exact Or.inr hbound'
    · have hlong : twoCeil (3 ^ v) + 1 ≤ v + W := by
        rw [hkdef]
        omega
      exact Or.inr (heavy_above_ceil (by omega : 1 ≤ v) hlong)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
theorem boundaries_through_128 : boundariesOk 128 = true := by
  decide

/-- Every run length from `2` through `128`, and every extra-halving count,
is either absolutely light or heavy. -/
theorem dichotomy_through_128 {v W : Nat} (hv : 2 ≤ v) (hW : 1 ≤ W)
    (hv128 : v ≤ 128) :
    2 ^ (v + W) ≤ 3 ^ v ∨ 3 ^ v ≤ 2 ^ W * (2 ^ v - 1) :=
  dichotomy_of_boundary hv hW hv128 boundaries_through_128

/-- **The one-step boundary, reduced.**  It is heavy for every length
through `128`, for every ceiling growth of two, and whenever the ceiling
shares a factor with the length.  What remains is an isolated growth of
one, at a ceiling coprime to the length, past `128`. -/
theorem heavy_boundary_reduced {v : Nat} (hv : 2 ≤ v)
    (h : v ≤ 128 ∨
        twoCeil (3 ^ (v - 1)) + 2 = twoCeil (3 ^ v) ∨
        2 ≤ Nat.gcd v (twoCeil (3 ^ v))) :
    3 ^ v ≤ 2 ^ (twoCeil (3 ^ v) - v) * (2 ^ v - 1) := by
  rcases h with h128 | hstruct
  · have hb := boundariesOk_sound 128 v boundaries_through_128 hv h128
    simpa [boundaryOk, decide_eq_true_eq] using hb
  · exact heavy_boundary_outside_one_jump hv hstruct

end ExcursionHeavy
end Collatz

section AxiomAudit
open Collatz.ExcursionHeavy
#print axioms all_u_drop_iff
#print axioms drop_of_heavy
#print axioms heavy_of_W_ge_v
#print axioms drop_of_W_ge_v
#print axioms heavy_margin_third
#print axioms drop_of_margin_third
#print axioms heavy_margin_306
#print axioms drop_of_margin_306
#print axioms no_gap_even
#print axioms heavy_boundary_of_common_factor
#print axioms dichotomy_of_common_factor
#print axioms nine_shares_factor
#print axioms heavy_boundary_of_ceiling_jump
#print axioms dichotomy_of_ceiling_jump
#print axioms four_ceiling_jumps
#print axioms ceiling_step
#print axioms one_jump_next
#print axioms one_jump_prev
#print axioms heavy_boundary_outside_one_jump
#print axioms five_is_isolated_one_jump
#print axioms heavy_boundary_reduced
#print axioms dichotomy_through_128
#print axioms fifteen_drops
#print axioms forty_seven_no_first_drop
end AxiomAudit
