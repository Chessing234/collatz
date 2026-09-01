import Collatz.Strategy.ExcursionOddLight
import Collatz.Strategy.ExcursionLand

/-!
# Remainder `1` after a `(3, 1)` step

A leftover `(v, W) = (3, 1)` step with `v₂(e + 5) = 1` lands on
`e ≡ 1 (mod 4)`, so the next excursion is `v' = 1`.  The second
extra-halving count splits the class:

* `W' ≥ 2` contracts enough that the second landing is below the
  original start (`(27/16) · (3/4) = 81/64` is the wrong comparison —
  the `v = 1` map is `(3u' − 1)/2^{W'}`, and `W' ≥ 2` is `≤ (3u' − 1)/4`.
  The integer comparison is `81u − 1 < 128u − 16`);
* `W' = 1` **grows**: `e' = (81u − 1)/8 > 8u − 1 = n` for every such
  start.  That is `71 → 121 → 91`, as a law, not a special witness.

The seed `7 → 13 → 5` has `W' = 2` and drops.  `expStep` has no extra
halvings on the `v = 1` step, so the `W' ≥ 2` bound never appears.
-/

namespace Collatz
namespace ExcursionLandOne

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionOddLight Collatz.ExcursionLand


/-! ## 1.  Remainder `1` is `v' = 1`, and the cofactor bridge -/

/-- Remainder `1` at the landing is `e ≡ 1 (mod 4)`. -/
theorem land_one_mod_four {e : Nat} (hr : Val2 (e + 5) 1) :
    e % 4 = 1 := by
  have : (e + 5) % 4 = 2 := Val2.one_iff.mp hr
  omega

/-- Bridge: `4 u' = 27 u + 1` when the landing has `v' = 1`. -/
theorem four_u'_of_v_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' W' e') :
    4 * u' = 27 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
  have hnu' : e + 1 = 2 * u' := by
    have := h'.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  omega


/-! ## 2.  `W' ≥ 2` drops below the original start -/

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

/-- **The integer comparison.**  `3 u' − 1 < 4 (8 u − 1)` when
`4 u' = 27 u + 1` and `u ≥ 1`. -/
private theorem second_lt_aux {u u' : Nat}
    (hu : 1 ≤ u) (hrel : 4 * u' = 27 * u + 1) :
    3 * u' - 1 < 4 * (8 * u - 1) := by
  have h12 : 12 * u' = 81 * u + 3 := by
    have : 12 * u' = 3 * (4 * u') := by
      have h : (12 : Nat) = 3 * 4 := by decide
      rw [h, Nat.mul_assoc]
    rw [this, hrel]
    omega
  have hL : 4 * (3 * u' - 1) = 12 * u' - 4 := by omega
  have hR : 4 * (4 * (8 * u - 1)) = 128 * u - 16 := by omega
  have hcmp : 12 * u' - 4 < 128 * u - 16 := by
    rw [h12]
    have : 81 * u + 3 - 4 = 81 * u - 1 := by omega
    have : 15 < 47 * u := by omega
    omega
  have : 4 * (3 * u' - 1) < 4 * (4 * (8 * u - 1)) := by
    rw [hL, hR]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Lemma X on `(3, 1)` landings of plus-five valuation `1` with
`W' ≥ 2`.**  The second excursion is `v = 1` with at least two extra
halvings, and lands below the original start. -/
theorem lemmaX_of_v_three_land_one_heavy {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (_hr : Val2 (e + 5) 1)
    (h' : IsExcursion e 1 u' W' e') (hW : 2 ≤ W') (_hn : 1 < n) :
    e' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hrel : 4 * u' = 27 * u + 1 := four_u'_of_v_one h h'
  have hbound := four_e'_le_v_one h' hW
  have hlt : 3 * u' - 1 < 4 * (8 * u - 1) := second_lt_aux hu hrel
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have : 4 * e' < 4 * n := by omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- Packaged as a Lemma X witness. -/
theorem lemmaX_of_v_three_land_one {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (e + 5) 1) (hn : 1 < n)
    (hheavy : ∀ u' W' e' : Nat, IsExcursion e 1 u' W' e' → 2 ≤ W') :
    ∃ e' : Nat, ExChain n e' ∧ e' < n := by
  have he4 := land_one_mod_four hr
  have heodd : e % 2 = 1 := h.2.2.1
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have hv' : v' = 1 := (v_eq_one_iff h').mpr he4
  have h'1 : IsExcursion e 1 u' W' e' := hv' ▸ h'
  have hW : 2 ≤ W' := hheavy u' W' e' h'1
  have hlt := lemmaX_of_v_three_land_one_heavy h hr h'1 hW hn
  exact ⟨e', ExChain.cons ⟨3, u, 1, h⟩ (ExChain.one ⟨v', u', W', h'⟩), hlt⟩


/-! ## 3.  `W' = 1` always grows past the original start -/

/-- When `W' = 1`, the landing is `(3 u' − 1)/2`. -/
theorem landing_of_W_one {e u' e' : Nat}
    (h' : IsExcursion e 1 u' 1 e') : 2 * e' + 1 = 3 * u' := by
  have := h'.2.2.2.2.2.2
  rw [Nat.pow_one, Nat.pow_one] at this
  exact this.symm

/-- **Negative law.**  `(3, 1)` then remainder `1` with `W' = 1` satisfies
`n < e'`.  The second landing is `(81 u − 1)/8`, strictly above `8 u − 1`. -/
theorem grows_of_v_three_land_one_light {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (_hr : Val2 (e + 5) 1)
    (h' : IsExcursion e 1 u' 1 e') : n < e' := by
  have hrel : 4 * u' = 27 * u + 1 := four_u'_of_v_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := landing_of_W_one h'
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  -- 8 e' = 12 u' - 4 = 3 (27 u + 1) - 4 = 81 u - 1
  have h8e : 8 * e' = 81 * u - 1 := by
    have h4 : 4 * (2 * e' + 1) = 4 * (3 * u') := by rw [hpeak]
    have : 8 * e' + 4 = 12 * u' := by omega
    have h12 : 12 * u' = 3 * (4 * u') := by
      have : (12 : Nat) = 3 * 4 := by decide
      rw [this, Nat.mul_assoc]
    have : 8 * e' + 4 = 3 * (27 * u + 1) := by
      rw [this, h12, hrel]
    omega
  have : 8 * n = 64 * u - 8 := by omega
  have hcmp : 64 * u - 8 < 81 * u - 1 := by
    have : 7 < 17 * u := by omega
    omega
  have : 8 * n < 8 * e' := by
    rw [this, h8e]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy.**  After `(3, 1)` with remainder `1`, the next `v = 1`
excursion either drops below the start (`W' ≥ 2`) or grows past it
(`W' = 1`). -/
theorem dichotomy_land_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (e + 5) 1)
    (h' : IsExcursion e 1 u' W' e') (hn : 1 < n) :
    (2 ≤ W' ∧ e' < n) ∨ (W' = 1 ∧ n < e') := by
  have hW1 : 1 ≤ W' := IsExcursion.one_le_W h'
  rcases Nat.eq_or_lt_of_le hW1 with hW | hW
  · subst hW
    exact Or.inr ⟨rfl, grows_of_v_three_land_one_light h hr h'⟩
  · have h2 : 2 ≤ W' := by omega
    exact Or.inl ⟨h2, lemmaX_of_v_three_land_one_heavy h hr h' h2 hn⟩


/-! ## 4.  Witnesses -/

/-- `W' ≥ 2` drops: `7 → 13 → 5`. -/
theorem seven_land_one_heavy :
    IsExcursion 7 3 1 1 13 ∧ Val2 (13 + 5) 1 ∧
    IsExcursion 13 1 7 2 5 ∧ 5 < 7 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨9, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 1` grows: `71 → 121 → 91`. -/
theorem seventy_one_land_one_light :
    IsExcursion 71 3 9 1 121 ∧ Val2 (121 + 5) 1 ∧
    IsExcursion 121 1 61 1 91 ∧ 71 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨63, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

end ExcursionLandOne
end Collatz

section AxiomAudit
open Collatz.ExcursionLandOne
#print axioms land_one_mod_four
#print axioms four_u'_of_v_one
#print axioms lemmaX_of_v_three_land_one_heavy
#print axioms grows_of_v_three_land_one_light
#print axioms dichotomy_land_one
end AxiomAudit
