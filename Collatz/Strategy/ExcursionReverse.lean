import Collatz.Strategy.ExcursionMap

/-!
# The inverse of the excursion map

Forward, an odd start `n` has a unique next odd state `e = Φ(n)`:
`n + 1 = 2^v u` and `3^v u = 2^W e + 1` (`IsExcursion`).  Reading the same
equations backwards, the odd parents of an odd landing `e` are exactly those

  `n = 2^v u − 1`

for which `v, W ≥ 1`, `3^v` divides `2^W e + 1`, and the quotient `u` is odd.

The even branch is separate: every odd `e` has parent `2e`.

The comparison `n ? e` is the one-step drop criterion read in reverse.

* `e < n` (forward drop) iff `3^v u + 2^W ≤ 2^{v+W} u`.  Surplus halvings
  `3^v < 2^{v+W}` are necessary, so the reverse of a drop is a climb.
* `2^{v+W} ≤ 3^v` (a light excursion) forces `n ≤ e`, so the reverse of a
  light step is a descent-or-stay.  Growth forward is descent backward.
* Surplus is not sufficient: the fixed point `1 ↦ 1` has `3 < 4` and `n = e`.

A never-dropper's own excursion landings stay at or above it, so reversing
its odd orbit is non-increasing.  Any reverse path that *climbs* therefore
starts at a number that has already dropped.  That is all the inverse of `Φ`
says about never-droppers.  It does not obstruct divergence: a hypothetical
never-dropper `n > 1` is consistent with an infinite even doubling ray
`2^k n` and with odd dropping parents, none of which need themselves never
drop.
-/

namespace Collatz
namespace ExcursionReverse

open Collatz.Arith Collatz.ExcursionMap Collatz.NeverDrops


/-! ## 1.  Even-branch inverse -/

/-- **Every odd `e` has even parent `2e`.**  This is the inverse of
`even_branch_contracts`, not of `Φ`. -/
theorem even_parent {e : Nat} (he : e % 2 = 1) :
    acceleratedStep (2 * e) = e := by
  have hmod : (2 * e) % 2 = 0 := Nat.mul_mod_right 2 e
  rw [acceleratedStep, if_pos hmod]
  omega

/-- The even parent sits strictly above the landing. -/
theorem even_parent_gt {e : Nat} (he : e % 2 = 1) : e < 2 * e := by
  omega


/-! ## 2.  Unpacking, and the inverse formula -/

/-- `n = 2^v u − 1`. -/
theorem parent_eq {n v u W e : Nat} (h : IsExcursion n v u W e) :
    n = 2 ^ v * u - 1 := by
  have : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  omega

/-- `3^v` divides the reverse peak `2^W e + 1`. -/
theorem three_pow_dvd_peak {n v u W e : Nat} (h : IsExcursion n v u W e) :
    3 ^ v ∣ 2 ^ W * e + 1 :=
  ⟨u, (h.2.2.2.2.2.2).symm⟩

/-- The odd cofactor is the `Nat.div` quotient. -/
theorem u_eq_div {n v u W e : Nat} (h : IsExcursion n v u W e) :
    u = (2 ^ W * e + 1) / 3 ^ v := by
  have hpeak : 2 ^ W * e + 1 = 3 ^ v * u := (h.2.2.2.2.2.2).symm
  rw [hpeak]
  exact (Nat.mul_div_cancel_left u (three_pow_pos v)).symm

private theorem two_pow_mul_even {v u : Nat} (hv : 0 < v) :
    (2 ^ v * u) % 2 = 0 := by
  have hv' : v = (v - 1) + 1 := by omega
  rw [hv', two_pow_succ, Nat.mul_assoc]
  exact Nat.mul_mod_right 2 _

/-- **Inverse of `Φ`.**  If `3^v u = 2^W e + 1` with `u` odd and `v, W ≥ 1`,
then `n = 2^v u − 1` is an odd parent of `e`. -/
theorem of_reverse {e v u W : Nat}
    (he : e % 2 = 1) (hu : u % 2 = 1)
    (hv : 0 < v) (hW : 0 < W)
    (hpeak : 3 ^ v * u = 2 ^ W * e + 1) :
    IsExcursion (2 ^ v * u - 1) v u W e := by
  have hu0 : 0 < u := by omega
  have hpos : 0 < 2 ^ v * u := Nat.mul_pos (two_pow_pos v) hu0
  have hn1 : (2 ^ v * u - 1) + 1 = 2 ^ v * u := by omega
  have hn : (2 ^ v * u - 1) % 2 = 1 := by
    have : (2 ^ v * u) % 2 = 0 := two_pow_mul_even hv
    omega
  exact ⟨hn, hu, he, hv, hW, hn1, hpeak⟩

/-- The same construction with the divisibility test written as `Nat.div`. -/
theorem of_reverse_div {e v W : Nat} (he : e % 2 = 1)
    (hv : 0 < v) (hW : 0 < W)
    (hdvd : 3 ^ v ∣ 2 ^ W * e + 1)
    (hu : ((2 ^ W * e + 1) / 3 ^ v) % 2 = 1) :
    IsExcursion (2 ^ v * ((2 ^ W * e + 1) / 3 ^ v) - 1)
      v ((2 ^ W * e + 1) / 3 ^ v) W e := by
  obtain ⟨u, hu0⟩ := hdvd
  have hdiv : (2 ^ W * e + 1) / 3 ^ v = u := by
    rw [hu0]
    exact Nat.mul_div_cancel_left u (three_pow_pos v)
  rw [hdiv]
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := hu0.symm
  rw [hdiv] at hu
  exact of_reverse he hu hv hW hpeak

/-- **Odd parents are exactly the reverse data of `IsExcursion`.** -/
theorem next_odd_iff {n e : Nat} :
    NextOdd n e ↔
      n % 2 = 1 ∧ e % 2 = 1 ∧
        ∃ v u W : Nat, 0 < v ∧ 0 < W ∧ u % 2 = 1 ∧
          3 ^ v * u = 2 ^ W * e + 1 ∧ n + 1 = 2 ^ v * u := by
  constructor
  · intro ⟨v, u, W, h⟩
    exact ⟨h.1, h.2.2.1, v, u, W, h.2.2.2.1, h.2.2.2.2.1, h.2.1,
      h.2.2.2.2.2.2, h.2.2.2.2.2.1⟩
  · intro ⟨hn, he, v, u, W, hv, hW, hu, hpeak, hnu⟩
    exact ⟨v, u, W, hn, hu, he, hv, hW, hnu, hpeak⟩


/-! ## 3.  Reverse of a drop is a climb -/

/-- **Climb iff drop.**  An odd parent sits strictly above its landing iff
the forward excursion drops iff `3^v u + 2^W ≤ 2^{v+W} u`. -/
theorem climb_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    e < n ↔ 3 ^ v * u + 2 ^ W ≤ 2 ^ (v + W) * u :=
  drop_iff h

/-- A climb forces surplus halvings. -/
theorem climb_needs_surplus {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hgt : e < n) :
    3 ^ v < 2 ^ (v + W) :=
  drop_needs_surplus h hgt

/-- **Reverse of a light excursion is a descent-or-stay.**  If the extra
halvings do not beat `log₂ 3 − 1`, the odd parent sits at or below the
landing.  Growth forward is descent backward. -/
theorem parent_le_of_light {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hlight : 2 ^ (v + W) ≤ 3 ^ v) :
    n ≤ e :=
  no_drop_of_light h hlight

/-- Surplus is necessary for a climb, not sufficient: `1` is a fixed point
of `Φ` with `3^1 < 2^{2}`. -/
theorem one_fixed :
    IsExcursion 1 1 1 1 1 ∧ ¬ (1 < 1) ∧ 3 ^ 1 < 2 ^ (1 + 1) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega, by decide⟩

/-- Worked reverse of a light (non-dropping) excursion: `7` is the odd
parent of `13`, and `7 ≤ 13`. -/
theorem seven_parent_of_thirteen :
    IsExcursion 7 3 1 1 13 ∧ 7 ≤ 13 ∧ 2 ^ (3 + 1) ≤ 3 ^ 3 :=
  ⟨seven_first_excursion, by omega, by decide⟩

/-- Worked reverse of a drop: `15` is the odd parent of `5`, and `5 < 15`. -/
theorem fifteen_parent_of_five :
    IsExcursion 15 4 1 4 5 ∧ 5 < 15 ∧ 3 ^ 4 < 2 ^ (4 + 4) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega, by decide⟩


/-! ## 4.  Never-droppers, read backwards -/

/-- If the start never drops, every excursion landing stays at or above it.
Reversing the actual odd orbit is a descent-or-stay. -/
theorem never_drops_landing_ge {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hnd : NeverDrops n) : n ≤ e := by
  have := hnd (v + W)
  rwa [landing_eq h] at this

/-- The same for a finite chain of excursions. -/
theorem chain_ge_of_never_drops {m e : Nat}
    (hnd : NeverDrops m) (h : ExChain m e) : m ≤ e := by
  obtain ⟨t, ht⟩ := chain_is_orbit h
  have := hnd t
  rwa [ht] at this

/-- **An odd parent (or chain) strictly above the landing has already dropped.**
The reverse tree of odd states above any `e` consists of dropping starts, hence
of numbers that do not never-drop. -/
theorem chain_above_not_never {m e : Nat}
    (h : ExChain m e) (hlt : e < m) : ¬ NeverDrops m := by
  intro hnd
  have := chain_ge_of_never_drops hnd h
  omega

/-- One-step form. -/
theorem parent_above_not_never {n e : Nat}
    (h : NextOdd n e) (hgt : e < n) : ¬ NeverDrops n :=
  chain_above_not_never (ExChain.one h) hgt

end ExcursionReverse
end Collatz

section AxiomAudit
open Collatz.ExcursionReverse
#print axioms even_parent
#print axioms of_reverse
#print axioms of_reverse_div
#print axioms next_odd_iff
#print axioms climb_iff
#print axioms parent_le_of_light
#print axioms never_drops_landing_ge
#print axioms chain_above_not_never
end AxiomAudit
