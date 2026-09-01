import Collatz.Strategy.ExcursionLandOne
import Collatz.Strategy.ExcursionEleven
import Collatz.Strategy.ExcursionPlusFive
import Collatz.Strategy.ExcursionOddLight

/-!
# The third excursion after `(3, 1)` then `(1, 1)`

`ExcursionLandOne` closed the two-step: after a leftover `(3, 1)` step
with remainder `1`, the next run is `v' = 1`, and `W' ≥ 2` drops while
`W' = 1` **always grows**.  The landing is the affine law

  `8 e' = 81 u − 1`,     `e' = (81 u − 1) / 8`,

with start `n = 8 u − 1`.  The seed `71 → 121 → 91` is that growth
(`u = 9`).  This file takes the third excursion of `e'`.

The next run and extra-halving count of `e'` are not a residue of `n`.
They are the plus-five / LTE reading of the two-step landing:

  `2^{v'' + 3} u'' = 81 u + 7`,

so `v'' = v₂(81 u + 7) − 3`, and `W'' = v₂(3^{v''} u'' − 1)`.  Equivalently
`v₂(e' + 5)` is the PlusFive dictionary at `e'`: remainder `1` is
`v'' = 1`, remainder `3` is `v'' = 2` with `W'' ≥ 2`, remainder `≥ 4`
is the light block `(2, 1)`, remainder `2` is leftover odd `v'' ≥ 3`.

A three-step drop below the original start holds once the third
excursion has enough extra halvings; too few grow past `n`.  The
thresholds (leading term `81 · 3^{v''} / 2^{v'' + W'' + 6}` against `1`):

* next `v'' = 1`: **always** drops (`W'' ≥ 1` is free);
* next `v'' = 2` and `W'' ≥ 2` drops; `W'' = 1` **grows**
  (`71 → 121 → 91 → 103`);
* next `v'' = 3` and `W'' ≥ 3` drops; `W'' ≤ 2` **grows**.

`71` itself does **not** drop in three steps.  The 11-fuel of a `(3, 1)`
start is `≥ 5`; fuel exactly `5` is the remainder-`1` landing that
feeds this family (`ExcursionEleven.exit_one_is_v_one`).

`expStep` has no extra halvings, so the `W''` thresholds never appear.
-/

namespace Collatz
namespace ExcursionLandOneNext

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionOddLight Collatz.ExcursionLandOne
open Collatz.ExcursionPlusFive Collatz.ExcursionEleven


/-! ## 1.  Two-step landing, and the family `u ≡ 9 (mod 16)` -/

/-- **Exact two-step landing.**  `(3, 1)` then `(1, 1)` is
`e' = (81 u − 1) / 8`. -/
theorem eight_e'_of_two_light {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') :
    8 * e' = 81 * u - 1 := by
  have hrel : 4 * u' = 27 * u + 1 := four_u'_of_v_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := landing_of_W_one h'
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have h4 : 4 * (2 * e' + 1) = 4 * (3 * u') := by rw [hpeak]
  have : 8 * e' + 4 = 12 * u' := by omega
  have h12 : 12 * u' = 3 * (4 * u') := by
    have : (12 : Nat) = 3 * 4 := by decide
    rw [this, Nat.mul_assoc]
  have : 8 * e' + 4 = 3 * (27 * u + 1) := by
    rw [this, h12, hrel]
  omega

/-- Plus-five of the two-step landing, in the cofactor. -/
theorem eight_plus_five_of_two_light {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') :
    8 * (e' + 5) = 81 * u + 39 := by
  have := eight_e'_of_two_light h h'
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  omega

/-- The two-light family is `u ≡ 9 (mod 16)`, forced by LTE at `v' = 1`
(`W' = 1` iff `u' ≡ 1 (mod 4)`) together with the cofactor bridge
`4 u' = 27 u + 1`.  Not a covering list of `n`. -/
theorem u_nine_mod_sixteen {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') :
    u % 16 = 9 := by
  have hu4 := u_one_mod_four_of_v_three_W_one h
  have hrel : 4 * u' = 27 * u + 1 := four_u'_of_v_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := landing_of_W_one h'
  have he' : e' % 2 = 1 := h'.2.2.1
  have hu' : u' % 2 = 1 := h'.2.1
  omega

/-- Every such start is at least the seed `71`. -/
theorem seventy_one_le_of_two_light {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') : 71 ≤ n := by
  have hu16 := u_nine_mod_sixteen h h'
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have : 9 ≤ u := by omega
  omega


/-! ## 2.  Bridge to the third excursion -/

/-- **The next run in cofactor coordinates.**  `v'' = v₂(81 u + 7) − 3`. -/
theorem two_pow_u''_of_third {n u e u' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' v'' u'' W'' e'') :
    2 ^ (v'' + 3) * u'' = 81 * u + 7 := by
  have h8 : 8 * e' = 81 * u - 1 := eight_e'_of_two_light h h'
  have hnu : e' + 1 = 2 ^ v'' * u'' := h''.2.2.2.2.2.1
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hsucc : 8 * (e' + 1) = 81 * u + 7 := by omega
  have h8pow : (8 : Nat) = 2 ^ 3 := by decide
  rw [hnu, h8pow] at hsucc
  have hpow : 2 ^ 3 * (2 ^ v'' * u'') = 2 ^ (v'' + 3) * u'' := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm]
  rwa [hpow] at hsucc

/-- Plus-five valuation of `e'` is the valuation of `81 u + 39`, shifted by `3`. -/
theorem val2_plus_five_of_two_light {n u e u' e' r : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (hr : Val2 (e' + 5) r) :
    Val2 (81 * u + 39) (r + 3) := by
  have hid := eight_plus_five_of_two_light h h'
  have h8 : (8 : Nat) = 2 ^ 3 := by decide
  have hmul : Val2 (2 ^ 3 * (e' + 5)) (3 + r) := Val2.two_pow_mul hr 3
  have hmul' : Val2 (8 * (e' + 5)) (r + 3) := by
    rw [h8]
    simpa [Nat.add_comm] using hmul
  exact hid ▸ hmul'

/-- Specialisation: next run `v'' = 1` is `16 u'' = 81 u + 7`. -/
theorem sixteen_u''_of_v_one {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 1 u'' W'' e'') :
    16 * u'' = 81 * u + 7 := by
  have := two_pow_u''_of_third h h' h''
  simpa using this

/-- Specialisation: next run `v'' = 2` is `32 u'' = 81 u + 7`. -/
theorem thirty_two_u''_of_v_two {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 2 u'' W'' e'') :
    32 * u'' = 81 * u + 7 := by
  have := two_pow_u''_of_third h h' h''
  simpa using this

/-- Specialisation: next run `v'' = 3` is `64 u'' = 81 u + 7`. -/
theorem sixty_four_u''_of_v_three {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 3 u'' W'' e'') :
    64 * u'' = 81 * u + 7 := by
  have := two_pow_u''_of_third h h' h''
  simpa using this

/-- Fuel `5` on a `(3, 1)` start is the remainder-`1` landing, hence a
`v' = 1` second excursion (`ExcursionEleven`). -/
theorem v_one_of_fuel_five {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (11 * n + 19) 5)
    (h' : IsExcursion e v' u' W' e') : v' = 1 :=
  exit_one_is_v_one h hr h'

/-- PlusFive at the two-step landing: remainder `1` is next run `v'' = 1`. -/
theorem third_v_eq_one_of_val2 {e' v'' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' v'' u'' W'' e'') (hr : Val2 (e' + 5) 1) :
    v'' = 1 :=
  (val2_eq_one_iff h'').mp hr

/-- PlusFive: remainder `3` is `v'' = 2` with `W'' ≥ 2`. -/
theorem third_v_two_heavy_of_val2 {e' v'' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' v'' u'' W'' e'') (hr : Val2 (e' + 5) 3) :
    v'' = 2 ∧ 2 ≤ W'' :=
  (val2_eq_three_iff h'').mp hr

/-- PlusFive: remainder `≥ 4` is the light block `(v'', W'') = (2, 1)`,
the `71` family. -/
theorem third_v_two_light_of_val2 {e' v'' u'' W'' e'' r : Nat}
    (h'' : IsExcursion e' v'' u'' W'' e'') (h4 : 4 ≤ r)
    (hr : Val2 (e' + 5) r) : v'' = 2 ∧ W'' = 1 :=
  (val2_ge_four_iff h'').mp ⟨r, h4, hr⟩


/-! ## 3.  Next run `v'' = 1`: always a three-step drop -/

/-- The peak at `v'' = 1`. -/
private theorem peak_v_one {e' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' 1 u'' W'' e'') :
    3 * u'' = 2 ^ W'' * e'' + 1 := by
  have := h''.2.2.2.2.2.2
  rw [Nat.pow_one] at this
  exact this

/-- `W'' ≥ 1` gives `2 e'' ≤ 3 u'' − 1`. -/
theorem two_e''_le_v_one {e' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' 1 u'' W'' e'') :
    2 * e'' ≤ 3 * u'' - 1 := by
  have hpeak := peak_v_one h''
  have hW : 1 ≤ W'' := IsExcursion.one_le_W h''
  have h2 : 2 ≤ 2 ^ W'' := by
    have : (2 : Nat) ^ 1 ≤ 2 ^ W'' := two_pow_le_two_pow hW
    simpa using this
  have hsub : 3 * u'' - 1 = 2 ^ W'' * e'' := by
    have : 1 ≤ u'' := by
      have : u'' % 2 = 1 := h''.2.1
      omega
    omega
  have : 2 * e'' ≤ 2 ^ W'' * e'' := Nat.mul_le_mul_right e'' h2
  omega

/-- Clearing the bridge: `16 (3 u'' − 1) = 243 u + 5`. -/
private theorem cleared_v_one {u u'' : Nat}
    (hrel : 16 * u'' = 81 * u + 7) :
    16 * (3 * u'' - 1) = 243 * u + 5 := by
  have hL : 16 * (3 * u'') = 3 * (16 * u'') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h243 : (3 : Nat) * 81 = 243 := by decide
  omega

/-- **Lemma X.**  After `(3, 1)` then `(1, 1)`, a third excursion of
length `v'' = 1` lands below the original start, for every `W'' ≥ 1`. -/
theorem lemmaX_of_two_light_v_one {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 1 u'' W'' e'') (_hn : 1 < n) :
    e'' < n := by
  have hu16 := u_nine_mod_sixteen h h'
  have hrel := sixteen_u''_of_v_one h h' h''
  have hbound := two_e''_le_v_one h''
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_one hrel
  have : 32 * e'' ≤ 243 * u + 5 := by
    have : 16 * (2 * e'') ≤ 16 * (3 * u'' - 1) := Nat.mul_le_mul_left 16 hbound
    omega
  have : 32 * e'' < 32 * n := by
    have : 243 * u + 5 < 256 * u - 32 := by
      have : 9 ≤ u := by omega
      have : 37 < 13 * u := by omega
      omega
    have : 32 * n = 256 * u - 32 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this


/-! ## 4.  Next run `v'' = 2`: threshold `W'' = 2` -/

/-- The peak at `v'' = 2`. -/
private theorem peak_v_two {e' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' 2 u'' W'' e'') :
    9 * u'' = 2 ^ W'' * e'' + 1 := by
  have := h''.2.2.2.2.2.2
  rw [show (3 : Nat) ^ 2 = 9 by decide] at this
  exact this

/-- `W'' ≥ 2` gives `4 e'' ≤ 9 u'' − 1`. -/
theorem four_e''_le_v_two {e' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' 2 u'' W'' e'') (hW : 2 ≤ W'') :
    4 * e'' ≤ 9 * u'' - 1 := by
  have hpeak := peak_v_two h''
  have hsub : 9 * u'' - 1 = 2 ^ W'' * e'' := by
    have : 1 ≤ u'' := by
      have : u'' % 2 = 1 := h''.2.1
      omega
    omega
  have h4 : 4 ≤ 2 ^ W'' := by
    have : (2 : Nat) ^ 2 ≤ 2 ^ W'' := two_pow_le_two_pow hW
    simpa using this
  have : 4 * e'' ≤ 2 ^ W'' * e'' := Nat.mul_le_mul_right e'' h4
  omega

/-- `W'' = 1` gives `2 e'' + 1 = 9 u''`. -/
theorem two_e''_of_v_two_W_one {e' u'' e'' : Nat}
    (h'' : IsExcursion e' 2 u'' 1 e'') : 2 * e'' + 1 = 9 * u'' := by
  have := peak_v_two h''
  rw [Nat.pow_one] at this
  exact this.symm

/-- Clearing the bridge: `32 (9 u'' − 1) = 729 u + 31`. -/
private theorem cleared_v_two {u u'' : Nat}
    (hrel : 32 * u'' = 81 * u + 7) :
    32 * (9 * u'' - 1) = 729 * u + 31 := by
  have hL : 32 * (9 * u'') = 9 * (32 * u'') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h729 : (9 : Nat) * 81 = 729 := by decide
  omega

/-- **Lemma X.**  After `(3, 1)` then `(1, 1)`, a third `v'' = 2`
excursion with `W'' ≥ 2` lands below the original start. -/
theorem lemmaX_of_two_light_v_two {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 2 u'' W'' e'') (hW : 2 ≤ W'') (_hn : 1 < n) :
    e'' < n := by
  have hrel := thirty_two_u''_of_v_two h h' h''
  have hbound := four_e''_le_v_two h'' hW
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_two hrel
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have : 128 * e'' ≤ 729 * u + 31 := by
    have : 32 * (4 * e'') ≤ 32 * (9 * u'' - 1) := Nat.mul_le_mul_left 32 hbound
    omega
  have : 128 * e'' < 128 * n := by
    have : 729 * u + 31 < 1024 * u - 128 := by
      have : 159 < 295 * u := by omega
      omega
    have : 128 * n = 1024 * u - 128 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- `W'' = 1` landing identity: `64 e'' = 729 u + 31`. -/
private theorem sixty_four_e''_of_v_two_W_one {u u'' e'' : Nat}
    (hrel : 32 * u'' = 81 * u + 7)
    (hpeak : 2 * e'' + 1 = 9 * u'') :
    64 * e'' = 729 * u + 31 := by
  have hmul : 32 * (2 * e'' + 1) = 9 * (32 * u'') := by
    have h1 : 32 * (2 * e'' + 1) = 32 * (9 * u'') := by rw [hpeak]
    have h2 : 32 * (9 * u'') = 9 * (32 * u'') := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    exact h1.trans h2
  have h9 : 9 * (32 * u'') = 9 * (81 * u + 7) := by rw [hrel]
  have hdist : 9 * (81 * u + 7) = 729 * u + 63 := by
    have hadd := Nat.mul_add 9 (81 * u) 7
    have h729 : (9 : Nat) * 81 = 729 := by decide
    have h63 : (9 : Nat) * 7 = 63 := by decide
    have hL : 9 * (81 * u) = 729 * u := by
      rw [← Nat.mul_assoc, h729]
    rw [hadd, hL, h63]
  have hsplit : 32 * (2 * e'' + 1) = 64 * e'' + 32 := by
    have hadd : 32 * (2 * e'' + 1) = 32 * (2 * e'') + 32 := by
      rw [Nat.mul_add, Nat.mul_one]
    have h64 : 32 * (2 * e'') = 64 * e'' := by
      have : (32 : Nat) * 2 = 64 := by decide
      rw [← Nat.mul_assoc, this]
    rw [hadd, h64]
  have heq : 64 * e'' + 32 = 729 * u + 63 := by
    rw [← hsplit, hmul, h9, hdist]
  omega

private theorem sixty_four_n_of_start {n u : Nat}
    (hu : 1 ≤ u) (hn : n = 8 * u - 1) :
    64 * n = 512 * u - 64 := by omega

private theorem grow_coeff_v_two {u : Nat} (hu : 1 ≤ u) :
    512 * u - 64 < 729 * u + 31 := by omega

/-- **Negative law.**  Next `v'' = 2` with `W'' = 1` grows past the start.
This is `71 → 121 → 91 → 103`, as a law. -/
private theorem grow_v_two_aux {n u u'' e'' : Nat}
    (hu : 1 ≤ u) (hn : n = 8 * u - 1)
    (hrel : 32 * u'' = 81 * u + 7)
    (hpeak : 2 * e'' + 1 = 9 * u'') : n < e'' := by
  have heq := sixty_four_e''_of_v_two_W_one hrel hpeak
  have hn64 := sixty_four_n_of_start hu hn
  have hcmp := grow_coeff_v_two hu
  have : 64 * n < 64 * e'' := by
    rw [hn64, heq]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

theorem grows_of_two_light_v_two_W_one {n u e u' e' u'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 2 u'' 1 e'') : n < e'' := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  exact grow_v_two_aux hu (n_eq_of_v_three_W_one h)
    (thirty_two_u''_of_v_two h h' h'') (two_e''_of_v_two_W_one h'')

/-- **Dichotomy** at next `v'' = 2`. -/
theorem dichotomy_two_light_v_two {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 2 u'' W'' e'') (hn : 1 < n) :
    (2 ≤ W'' ∧ e'' < n) ∨ (W'' = 1 ∧ n < e'') := by
  have hW1 : 1 ≤ W'' := IsExcursion.one_le_W h''
  rcases Nat.eq_or_lt_of_le hW1 with hW | hW
  · subst hW
    exact Or.inr ⟨rfl, grows_of_two_light_v_two_W_one h h' h''⟩
  · have h2 : 2 ≤ W'' := by omega
    exact Or.inl ⟨h2, lemmaX_of_two_light_v_two h h' h'' h2 hn⟩


/-! ## 5.  Next run `v'' = 3`: threshold `W'' = 3` -/

/-- The peak at `v'' = 3`. -/
private theorem peak_v_three {e' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' 3 u'' W'' e'') :
    27 * u'' = 2 ^ W'' * e'' + 1 := by
  have := h''.2.2.2.2.2.2
  rw [show (3 : Nat) ^ 3 = 27 by decide] at this
  exact this

/-- `W'' ≥ 3` gives `8 e'' ≤ 27 u'' − 1`. -/
theorem eight_e''_le_v_three {e' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' 3 u'' W'' e'') (hW : 3 ≤ W'') :
    8 * e'' ≤ 27 * u'' - 1 := by
  have hpeak := peak_v_three h''
  have hsub : 27 * u'' - 1 = 2 ^ W'' * e'' := by
    have : 1 ≤ u'' := by
      have : u'' % 2 = 1 := h''.2.1
      omega
    omega
  have h8 : 8 ≤ 2 ^ W'' := by
    have : (2 : Nat) ^ 3 ≤ 2 ^ W'' := two_pow_le_two_pow hW
    simpa using this
  have : 8 * e'' ≤ 2 ^ W'' * e'' := Nat.mul_le_mul_right e'' h8
  omega

/-- `W'' ≤ 2` gives `27 u'' − 1 ≤ 4 e''`. -/
theorem four_e''_ge_v_three {e' u'' W'' e'' : Nat}
    (h'' : IsExcursion e' 3 u'' W'' e'') (hW : W'' ≤ 2) :
    27 * u'' - 1 ≤ 4 * e'' := by
  have hpeak := peak_v_three h''
  have h4 : 2 ^ W'' ≤ 4 := by
    have : (2 : Nat) ^ W'' ≤ 2 ^ 2 := two_pow_le_two_pow hW
    simpa using this
  have : 2 ^ W'' * e'' ≤ 4 * e'' := Nat.mul_le_mul_right e'' h4
  omega

/-- Clearing the bridge: `64 (27 u'' − 1) = 2187 u + 125`. -/
private theorem cleared_v_three {u u'' : Nat}
    (hrel : 64 * u'' = 81 * u + 7) :
    64 * (27 * u'' - 1) = 2187 * u + 125 := by
  have hL : 64 * (27 * u'') = 27 * (64 * u'') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2187 : (27 : Nat) * 81 = 2187 := by decide
  omega

/-- **Lemma X.**  After `(3, 1)` then `(1, 1)`, a third `v'' = 3`
excursion with `W'' ≥ 3` lands below the original start. -/
theorem lemmaX_of_two_light_v_three {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 3 u'' W'' e'') (hW : 3 ≤ W'') (_hn : 1 < n) :
    e'' < n := by
  have hrel := sixty_four_u''_of_v_three h h' h''
  have hbound := eight_e''_le_v_three h'' hW
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_three hrel
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have : 512 * e'' ≤ 2187 * u + 125 := by
    have : 64 * (8 * e'') ≤ 64 * (27 * u'' - 1) := Nat.mul_le_mul_left 64 hbound
    omega
  have : 512 * e'' < 512 * n := by
    have : 2187 * u + 125 < 4096 * u - 512 := by
      have : 637 < 1909 * u := by omega
      omega
    have : 512 * n = 4096 * u - 512 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Negative law.**  Next `v'' = 3` with `W'' ≤ 2` grows past the start. -/
theorem grows_of_two_light_v_three_light {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 3 u'' W'' e'') (hW : W'' ≤ 2) : n < e'' := by
  have hrel := sixty_four_u''_of_v_three h h' h''
  have hge := four_e''_ge_v_three h'' hW
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_three hrel
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have : 2187 * u + 125 ≤ 256 * e'' := by
    have : 64 * (27 * u'' - 1) ≤ 64 * (4 * e'') := Nat.mul_le_mul_left 64 hge
    omega
  have : 256 * n < 256 * e'' := by
    have : 2048 * u - 256 < 2187 * u + 125 := by
      have : 0 < 139 * u + 381 := by omega
      omega
    have : 256 * n = 2048 * u - 256 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy** at next `v'' = 3`. -/
theorem dichotomy_two_light_v_three {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 3 u'' W'' e'') (hn : 1 < n) :
    (3 ≤ W'' ∧ e'' < n) ∨ (W'' ≤ 2 ∧ n < e'') := by
  rcases Nat.lt_or_ge W'' 3 with hlt | hge
  · have h2 : W'' ≤ 2 := by omega
    exact Or.inr ⟨h2, grows_of_two_light_v_three_light h h' h'' h2⟩
  · exact Or.inl ⟨hge, lemmaX_of_two_light_v_three h h' h'' hge hn⟩


/-! ## 6.  Plus-five packaging -/

/-- Remainder `1` at `e'` is a three-step Lemma X witness. -/
theorem lemmaX_of_two_light_val2_one {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (hr : Val2 (e' + 5) 1) (hn : 1 < n) :
    ∃ e'' : Nat, ExChain n e'' ∧ e'' < n := by
  have heodd : e' % 2 = 1 := h'.2.2.1
  obtain ⟨v'', u'', W'', e'', h''⟩ := exists_excursion heodd
  have hv : v'' = 1 := third_v_eq_one_of_val2 h'' hr
  subst hv
  have hlt := lemmaX_of_two_light_v_one h h' h'' hn
  exact ⟨e'',
    ExChain.cons ⟨3, u, 1, h⟩
      (ExChain.cons ⟨1, u', 1, h'⟩ (ExChain.one ⟨1, u'', W'', h''⟩)),
    hlt⟩

/-- Remainder `3` at `e'` is a three-step Lemma X witness. -/
theorem lemmaX_of_two_light_val2_three {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (hr : Val2 (e' + 5) 3) (hn : 1 < n) :
    ∃ e'' : Nat, ExChain n e'' ∧ e'' < n := by
  have heodd : e' % 2 = 1 := h'.2.2.1
  obtain ⟨v'', u'', W'', e'', h''⟩ := exists_excursion heodd
  have ⟨hv, hW⟩ := third_v_two_heavy_of_val2 h'' hr
  subst hv
  have hlt := lemmaX_of_two_light_v_two h h' h'' hW hn
  exact ⟨e'',
    ExChain.cons ⟨3, u, 1, h⟩
      (ExChain.cons ⟨1, u', 1, h'⟩ (ExChain.one ⟨2, u'', W'', h''⟩)),
    hlt⟩

/-- Remainder `≥ 4` at `e'` is the complementary growth law: the third
excursion is `(2, 1)` and lands above `n`. -/
theorem grows_of_two_light_val2_ge_four {n u e u' e' r : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h4 : 4 ≤ r) (hr : Val2 (e' + 5) r) :
    ∃ e'' : Nat, n < e'' := by
  have heodd : e' % 2 = 1 := h'.2.2.1
  obtain ⟨v'', u'', W'', e'', h''⟩ := exists_excursion heodd
  have ⟨hv, hW⟩ := third_v_two_light_of_val2 h'' h4 hr
  subst hv
  subst hW
  exact ⟨e'', grows_of_two_light_v_two_W_one h h' h''⟩


/-! ## 7.  Witnesses -/

/-- `v'' = 1` drops: `455 → 769 → 577 → 433`. -/
theorem four_fifty_five_v_one :
    IsExcursion 455 3 57 1 769 ∧
    IsExcursion 769 1 385 1 577 ∧
    Val2 (577 + 5) 1 ∧
    IsExcursion 577 1 289 1 433 ∧
    433 < 455 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨291, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W'' ≥ 2` drops: `1607 → 2713 → 2035 → 1145`. -/
theorem sixteen_oh_seven_v_two_W_two :
    IsExcursion 1607 3 201 1 2713 ∧
    IsExcursion 2713 1 1357 1 2035 ∧
    Val2 (2035 + 5) 3 ∧
    IsExcursion 2035 2 509 2 1145 ∧
    1145 < 1607 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨255, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- **The seed does not drop in three steps.**
`71 → 121 → 91 → 103`, with `v₂(91 + 5) = 5` the light block `(2, 1)`. -/
theorem seventy_one_three_step_grows :
    IsExcursion 71 3 9 1 121 ∧
    Val2 (11 * 71 + 19) 5 ∧
    IsExcursion 121 1 61 1 91 ∧
    Val2 (91 + 5) 5 ∧
    IsExcursion 91 2 23 1 103 ∧
    71 < 103 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨25, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨3, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W'' = 2` at `v'' = 3` grows: `1863 → 3145 → 2359 → 1991`. -/
theorem eighteen_sixty_three_v_three_W_two :
    IsExcursion 1863 3 233 1 3145 ∧
    IsExcursion 3145 1 1573 1 2359 ∧
    Val2 (2359 + 5) 2 ∧
    IsExcursion 2359 3 295 2 1991 ∧
    1863 < 1991 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨591, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W'' = 3` at `v'' = 3` drops: `3911 → 6601 → 4951 → 2089`. -/
theorem thirty_nine_eleven_v_three_W_three :
    IsExcursion 3911 3 489 1 6601 ∧
    IsExcursion 6601 1 3301 1 4951 ∧
    Val2 (4951 + 5) 2 ∧
    IsExcursion 4951 3 619 3 2089 ∧
    2089 < 3911 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨1239, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

end ExcursionLandOneNext
end Collatz

section AxiomAudit
open Collatz.ExcursionLandOneNext
#print axioms eight_e'_of_two_light
#print axioms u_nine_mod_sixteen
#print axioms two_pow_u''_of_third
#print axioms v_one_of_fuel_five
#print axioms lemmaX_of_two_light_v_one
#print axioms lemmaX_of_two_light_v_two
#print axioms grows_of_two_light_v_two_W_one
#print axioms dichotomy_two_light_v_two
#print axioms lemmaX_of_two_light_v_three
#print axioms grows_of_two_light_v_three_light
#print axioms dichotomy_two_light_v_three
#print axioms seventy_one_three_step_grows
end AxiomAudit
