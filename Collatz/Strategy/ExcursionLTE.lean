import Collatz.Strategy.ExcursionMap

/-!
# Extra halvings from LTE and the ultrametric inequality

The landing of an excursion is cut out by `3 ^ v * u = 2 ^ W * e + 1`, so
`W = v₂(3 ^ v * u − 1)`.  Split the peak as a sum of two terms whose
valuations are known separately:

  `3 ^ v * u − 1  =  3 ^ v * (u − 1)  +  (3 ^ v − 1)`.

The first summand has valuation `v₂(u − 1)` (`3 ^ v` is odd).  The second
is the lifting-the-exponent value `v₂(3 ^ v − 1)`: `1` on odd `v`, and
`v₂(v) + 2` on even `v`.  The ultrametric law then reads `W` off those two
numbers, with no residue enumeration of `n`:

* if they differ, `W` is the minimum;
* if they agree, `W` is strictly larger.

The exact drop criterion `drop_iff` then fires from a lower bound on `W`.
This is how `v = 2` with `v₂(u − 1) ≥ 2` and odd `v = 3` with `u ≡ 3
(mod 4)` drop, and how odd `v ≥ 3` with `u ≡ 1 (mod 4)` is certified light
(`W = 1`).  The last family includes the leftover `7 (mod 32)` starts; the
device does not close them.

`expStep` still fails the mechanism: it has no extra halvings, so the
ultrametric computation of `W` never starts.
-/

namespace Collatz
namespace ExcursionLTE

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap


/-! ## 1.  The peak split -/

/-- Powers of three are odd. -/
private theorem three_pow_odd (k : Nat) : (3 : Nat) ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- `3 ^ v` has 2-adic valuation zero. -/
theorem val2_three_pow (v : Nat) : Val2 (3 ^ v) 0 :=
  Val2.of_odd (three_pow_odd v)

/-- **Peak identity.**  `3 ^ v * u − 1 = 3 ^ v * (u − 1) + (3 ^ v − 1)`. -/
theorem peak_split {v u : Nat} (hu : 1 ≤ u) :
    3 ^ v * u - 1 = 3 ^ v * (u - 1) + (3 ^ v - 1) := by
  have h3 : 1 ≤ 3 ^ v := one_le_three_pow v
  have hmul : 3 ^ v ≤ 3 ^ v * u := Nat.le_mul_of_pos_right _ hu
  have hdist : 3 ^ v * u - 3 ^ v = 3 ^ v * (u - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hR : 3 ^ v * u - 3 ^ v + (3 ^ v - 1) = 3 ^ v * u - 1 := by
    have hassoc := Nat.add_sub_assoc h3 (3 ^ v * u - 3 ^ v)
    have hcancel : 3 ^ v * u - 3 ^ v + 3 ^ v = 3 ^ v * u := Nat.sub_add_cancel hmul
    have htail : 3 ^ v * u - 3 ^ v + 3 ^ v - 1 = 3 ^ v * u - 1 := by rw [hcancel]
    exact hassoc.symm.trans htail
  rw [← hdist, hR]

/-- Scaling the cofactor gap by `3 ^ v` does not change its valuation. -/
theorem val2_scaled_u_pred {v u t : Nat} (ht : Val2 (u - 1) t) :
    Val2 (3 ^ v * (u - 1)) t := by
  have h := Val2.mul (val2_three_pow v) ht
  simpa using h

/-- An odd cofactor larger than one has even predecessor, so `v₂(u − 1) ≥ 1`. -/
theorem val2_u_pred_pos {u t : Nat} (hu : u % 2 = 1) (h1 : 1 < u)
    (ht : Val2 (u - 1) t) : 1 ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | hp
  · have hodd : (u - 1) % 2 = 1 := Val2.odd_of_zero ht
    omega
  · exact Nat.succ_le_of_lt hp


/-! ## 2.  Collision raises the valuation -/

/-- If two summands have the same valuation `r`, their sum is divisible by
`2 ^{r+1}`, so its valuation is at least `r + 1`. -/
theorem val2_add_succ_le {x y r s : Nat}
    (hx : Val2 x r) (hy : Val2 y r) (hs : Val2 (x + y) s) : r + 1 ≤ s := by
  obtain ⟨m, hm, hex⟩ := hx
  obtain ⟨m', hm', hey⟩ := hy
  have hdiv : 2 ^ (r + 1) ∣ x + y := by
    refine ⟨(m + m') / 2, ?_⟩
    have hhalf : 2 * ((m + m') / 2) = m + m' := by omega
    rw [hex, hey, ← Nat.mul_add, ← hhalf, two_pow_succ r]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact (Val2.dvd_iff_le hs).mp hdiv


/-! ## 3.  `W` from the two valuations -/

/-- Mersenne cofactor: `u = 1` makes the peak `3 ^ v − 1`, so `W` is LTE. -/
theorem W_of_u_one {n v W e : Nat} (h : IsExcursion n v 1 W e) :
    Val2 (3 ^ v - 1) W := by
  have hpeak := val2_peak_of h
  have : 3 ^ v * 1 - 1 = 3 ^ v - 1 := by rw [Nat.mul_one]
  rwa [this] at hpeak

/-- **Ultrametric, smaller cofactor gap.**  If `v₂(u − 1) < v₂(3 ^ v − 1)`
then `W = v₂(u − 1)`. -/
theorem W_eq_of_u_pred_lt {n v u W e t L : Nat}
    (h : IsExcursion n v u W e) (hu : 1 < u)
    (ht : Val2 (u - 1) t) (hL : Val2 (3 ^ v - 1) L) (hlt : t < L) :
    W = t := by
  have hsplit : 3 ^ v * u - 1 = 3 ^ v * (u - 1) + (3 ^ v - 1) :=
    peak_split (by omega)
  have hsum := Val2.add_of_lt (val2_scaled_u_pred (v := v) ht) hL hlt
  have hW : Val2 (3 ^ v * u - 1) t := hsplit ▸ hsum
  exact Val2.unique (val2_peak_of h) hW

/-- **Ultrametric, smaller LTE term.**  If `v₂(3 ^ v − 1) < v₂(u − 1)`
then `W` is the LTE value. -/
theorem W_eq_of_lte_lt {n v u W e t L : Nat}
    (h : IsExcursion n v u W e) (hu : 1 < u)
    (ht : Val2 (u - 1) t) (hL : Val2 (3 ^ v - 1) L) (hlt : L < t) :
    W = L := by
  have hsplit : 3 ^ v * u - 1 = (3 ^ v - 1) + 3 ^ v * (u - 1) := by
    rw [peak_split (by omega), Nat.add_comm]
  have hsum := Val2.add_of_lt hL (val2_scaled_u_pred (v := v) ht) hlt
  have hW : Val2 (3 ^ v * u - 1) L := hsplit ▸ hsum
  exact Val2.unique (val2_peak_of h) hW

/-- **Collision.**  Equal valuations force `W ≥ t + 1`. -/
theorem W_gt_of_eq {n v u W e t : Nat}
    (h : IsExcursion n v u W e) (hu : 1 < u)
    (ht : Val2 (u - 1) t) (hL : Val2 (3 ^ v - 1) t) :
    t + 1 ≤ W := by
  have hsplit : 3 ^ v * u - 1 = 3 ^ v * (u - 1) + (3 ^ v - 1) :=
    peak_split (by omega)
  have hW : Val2 (3 ^ v * (u - 1) + (3 ^ v - 1)) W := hsplit ▸ val2_peak_of h
  exact val2_add_succ_le (val2_scaled_u_pred (v := v) ht) hL hW


/-! ## 4.  Drop from a lower bound on `W` -/

private theorem pow_factor {v k u : Nat} :
    (2 : Nat) ^ (v + k) * u = 2 ^ k * (2 ^ v * u) := by
  rw [Nat.pow_add]
  simp [Nat.mul_assoc, Nat.mul_comm]

/-- Extra halvings help: if the exact criterion holds at `k ≤ W`, it holds
at `W`. -/
theorem drop_of_W_ge {n v u W e k : Nat}
    (h : IsExcursion n v u W e) (hk : k ≤ W)
    (hineq : 3 ^ v * u + 2 ^ k ≤ 2 ^ (v + k) * u) : e < n := by
  refine (drop_iff h).mpr ?_
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hpos : 0 < 2 ^ v * u := Nat.mul_pos (two_pow_pos v) (by omega)
  have hkW : 2 ^ k ≤ 2 ^ W := two_pow_le_two_pow hk
  have hsubk : 2 ^ k ≤ 2 ^ (v + k) * u := by
    rw [pow_factor]
    exact Nat.le_mul_of_pos_right _ hpos
  have hsubW : 2 ^ W ≤ 2 ^ (v + W) * u := by
    rw [pow_factor]
    exact Nat.le_mul_of_pos_right _ hpos
  have hA : 3 ^ v * u ≤ 2 ^ (v + k) * u - 2 ^ k :=
    Nat.le_sub_of_add_le hineq
  have hmon : 2 ^ (v + k) * u - 2 ^ k ≤ 2 ^ (v + W) * u - 2 ^ W := by
    have hk' : 2 ^ (v + k) * u - 2 ^ k = 2 ^ k * (2 ^ v * u - 1) := by
      rw [pow_factor, Nat.mul_sub_left_distrib, Nat.mul_one]
    have hW' : 2 ^ (v + W) * u - 2 ^ W = 2 ^ W * (2 ^ v * u - 1) := by
      rw [pow_factor, Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [hk', hW']
    exact Nat.mul_le_mul_right _ hkW
  have hleft : 3 ^ v * u + 2 ^ W ≤ (2 ^ (v + k) * u - 2 ^ k) + 2 ^ W :=
    Nat.add_le_add_right hA _
  have hmid : (2 ^ (v + k) * u - 2 ^ k) + 2 ^ W
      ≤ (2 ^ (v + W) * u - 2 ^ W) + 2 ^ W :=
    Nat.add_le_add_right hmon _
  have hcancel : (2 ^ (v + W) * u - 2 ^ W) + 2 ^ W = 2 ^ (v + W) * u :=
    Nat.sub_add_cancel hsubW
  omega


/-! ## 5.  Odd run length: LTE is `1` -/

/-- Odd `v` and `u ≡ 1 (mod 4)` force `W = 1`, including the Mersenne case
`u = 1`. -/
theorem W_eq_one_of_odd_v_u_one_mod_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hodd : v % 2 = 1) (hu4 : u % 4 = 1) :
    W = 1 := by
  have hL : Val2 (3 ^ v - 1) 1 := val2_three_pow_sub_one_odd hodd
  rcases Nat.eq_or_lt_of_le (by
      have : u % 2 = 1 := h.2.1
      omega : 1 ≤ u) with hu1 | hult
  · subst hu1
    exact Val2.unique (W_of_u_one h) hL
  · obtain ⟨t, ht⟩ := Val2.exists_of_pos (by omega : 0 < u - 1)
    have h4 : 4 ∣ u - 1 := by omega
    have ht2 : 2 ≤ t := (Val2.dvd_iff_le ht).mp (by
      have : (2 : Nat) ^ 2 = 4 := by decide
      rwa [this])
    exact W_eq_of_lte_lt h hult ht hL (by omega)

/-- Odd `v` and `u ≡ 3 (mod 4)` collide, so `W ≥ 2`. -/
theorem W_ge_two_of_odd_v_u_three_mod_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hodd : v % 2 = 1) (hu4 : u % 4 = 3) :
    2 ≤ W := by
  have hL : Val2 (3 ^ v - 1) 1 := val2_three_pow_sub_one_odd hodd
  have hu : 1 < u := by omega
  have ht : Val2 (u - 1) 1 := Val2.one_iff.mpr (by omega)
  exact W_gt_of_eq h hu ht hL

/-- `2 ^{v+1} ≤ 3 ^ v` for `v ≥ 2`.  Combined with `W = 1` this is a light
excursion. -/
theorem two_pow_succ_le_three_pow {v : Nat} (hv : 2 ≤ v) :
    2 ^ (v + 1) ≤ 3 ^ v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
  clear hv
  induction k with
  | zero => decide
  | succ k ih =>
    have hmul : 2 * 2 ^ (2 + k + 1) ≤ 3 * 3 ^ (2 + k) :=
      Nat.mul_le_mul (by decide : (2 : Nat) ≤ 3) ih
    have h2 : 2 + (k + 1) + 1 = (2 + k + 1) + 1 := by omega
    have h3 : 2 + (k + 1) = (2 + k) + 1 := by omega
    calc
      2 ^ (2 + (k + 1) + 1) = 2 ^ ((2 + k + 1) + 1) := by rw [h2]
      _ = 2 * 2 ^ (2 + k + 1) := two_pow_succ (2 + k + 1)
      _ ≤ 3 * 3 ^ (2 + k) := hmul
      _ = 3 ^ (2 + k) * 3 := Nat.mul_comm _ _
      _ = 3 ^ ((2 + k) + 1) := (Nat.pow_succ _ _).symm
      _ = 3 ^ (2 + (k + 1)) := by rw [h3]

/-- Odd `v ≥ 3` and `u ≡ 1 (mod 4)` make a light first excursion: no
one-step drop.  This is the leftover `7 (mod 32)` family at `v = 3`. -/
theorem no_first_drop_of_odd_v_u_one_mod_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hodd : v % 2 = 1) (hv : 3 ≤ v)
    (hu4 : u % 4 = 1) : n ≤ e := by
  have hW : W = 1 := W_eq_one_of_odd_v_u_one_mod_four h hodd hu4
  have hlight : 2 ^ (v + W) ≤ 3 ^ v := by
    rw [hW]
    exact two_pow_succ_le_three_pow (by omega)
  exact no_drop_of_light h hlight


/-! ## 6.  Payoff drops, from the lower bound on `W` -/

/-- `v = 3` and `u ≡ 3 (mod 4)` drop in one excursion.  In start coordinates
this is `n ≡ 23 (mod 32)`, recovered from LTE rather than a covering list. -/
theorem drop_of_v_three_u_three_mod_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 3) (hu4 : u % 4 = 3)
    (_hn : 1 < n) : e < n := by
  subst hv
  have hW : 2 ≤ W := W_ge_two_of_odd_v_u_three_mod_four h (by decide) hu4
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  refine drop_of_W_ge h hW ?_
  have hpow : (2 : Nat) ^ (3 + 2) = 32 := by decide
  have h3 : (3 : Nat) ^ 3 = 27 := by decide
  have h2 : (2 : Nat) ^ 2 = 4 := by decide
  rw [h3, h2, hpow]
  omega

/-- LTE at `v = 2` is `v₂(3 ^ 2 − 1) = 3`. -/
private theorem lte_v_two : Val2 (3 ^ 2 - 1) 3 := by
  have hv : Val2 (2 : Nat) 1 := Val2.one_iff.mpr rfl
  have h := val2_three_pow_sub_one (a := 2) (t := 1) (by omega) hv
  simpa using h

/-- `v = 2` and `v₂(u − 1) ≥ 2` force `W ≥ 2`, hence a drop.  This is
`drop_of_v_two` read off the ultrametric comparison with LTE `= 3`. -/
theorem drop_of_v_two_of_val2 {n v u W e t : Nat}
    (h : IsExcursion n v u W e) (hv : v = 2) (ht : Val2 (u - 1) t)
    (ht2 : 2 ≤ t) (hn : 1 < n) : e < n := by
  subst hv
  have hu : 1 < u := by
    have hle : 2 ^ t ≤ u - 1 := Val2.le ht
    have h4 : 4 ≤ 2 ^ t := by
      have : (2 : Nat) ^ 2 ≤ 2 ^ t := two_pow_le_two_pow ht2
      simpa using this
    omega
  have hW : 2 ≤ W := by
    rcases Nat.lt_trichotomy t 3 with hlt | heq | hgt
    · have hWt : W = t := W_eq_of_u_pred_lt h hu ht lte_v_two hlt
      omega
    · subst heq
      have := W_gt_of_eq h hu ht lte_v_two
      omega
    · have hWL : W = 3 := W_eq_of_lte_lt h hu ht lte_v_two hgt
      omega
  exact drop_of_v_two h rfl hW hn

/-- Lemma X on the LTE class `v = 3`, `u ≡ 3 (mod 4)`. -/
theorem lemmaX_of_v_three_u_three_mod_four {n : Nat}
    (hn : 1 < n) (hodd : n % 2 = 1)
    (hvu : ∀ v u W e : Nat, IsExcursion n v u W e → v = 3 ∧ u % 4 = 3) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have ⟨hv, hu4⟩ := hvu v u W e h
  exact ⟨e, ExChain.one ⟨v, u, W, h⟩, drop_of_v_three_u_three_mod_four h hv hu4 hn⟩

/-- Direct form: an excursion with `v = 3` and `u ≡ 3 (mod 4)` is a
Lemma X witness. -/
theorem lemmaX_of_excursion_v_three {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 3) (hu4 : u % 4 = 3)
    (hn : 1 < n) : ExChain n e ∧ e < n :=
  ⟨ExChain.one ⟨v, u, W, h⟩, drop_of_v_three_u_three_mod_four h hv hu4 hn⟩


/-! ## 7.  Witnesses: the device is sharp on odd `v` -/

/-- `7` is the odd-`v` light case: `v = 3`, `u = 1 ≡ 1 (mod 4)`, `W = 1`,
landing `13 > 7`. -/
theorem seven_is_light : ∃ v u W e : Nat,
    IsExcursion 7 v u W e ∧ v = 3 ∧ u = 1 ∧ W = 1 ∧ 7 ≤ e :=
  ⟨3, 1, 1, 13, ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    rfl, rfl, rfl, by omega⟩

end ExcursionLTE
end Collatz

section AxiomAudit
open Collatz.ExcursionLTE
#print axioms peak_split
#print axioms W_eq_of_u_pred_lt
#print axioms W_eq_of_lte_lt
#print axioms W_gt_of_eq
#print axioms drop_of_W_ge
#print axioms W_eq_one_of_odd_v_u_one_mod_four
#print axioms W_ge_two_of_odd_v_u_three_mod_four
#print axioms no_first_drop_of_odd_v_u_one_mod_four
#print axioms drop_of_v_three_u_three_mod_four
#print axioms drop_of_v_two_of_val2
end AxiomAudit
