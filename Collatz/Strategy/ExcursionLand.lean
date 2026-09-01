import Collatz.Strategy.ExcursionOddLight
import Collatz.Strategy.ExcursionPlusFive

/-!
# Landing plus-five after a `(3, 1)` step

A leftover start has `v₂(n + 5) = 2`.  The light odd run `(v, W) = (3, 1)`
grows by `27/16`.  If the landing `e` has `v₂(e + 5) = 3`, then `e ≡ 3
(mod 16)` and the next excursion is the already-closed `v = 2`, `W ≥ 2`
drop, which contracts by at most `9/16`.

  `(27/16) * (9/16) = 243/256 < 1`,

so the second landing is below the *original* start, not merely below `e`.
The hypothesis is a 2-adic fact about the landing (`Val2 (e + 5) 3`), not
a residue of `n`.  The seed `7 → 13` has `v₂(13 + 5) = 1` and is excluded;
`71 → 121` has remainder `1` and is the known counterexample that a
`v = 1` landing need not fall below `n`.

`expStep` has no extra halvings on the second step, so the `9/16` factor
never appears.
-/

namespace Collatz
namespace ExcursionLand

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionOddLight Collatz.ExcursionPlusFive


/-! ## 1.  The landing of a `(3, 1)` step -/

/-- Bridge between cofactors: `8 u' = 27 u + 1` when the landing has
`v = 2`. -/
theorem eight_u'_of_v_two {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 2 u' W' e') :
    8 * u' = 27 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
  have hnu' : e + 1 = 4 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  omega

/-- Remainder `3` at the landing is `e ≡ 3 (mod 16)`. -/
theorem land_three_mod_sixteen {e : Nat} (hr : Val2 (e + 5) 3) :
    e % 16 = 3 := by
  have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
  have : (e + 5) % 16 = 8 := by
    have := Val2.mod hr
    rwa [hpow] at this
  omega


/-! ## 2.  The `W ≥ 2` bound on the second landing -/

/-- Crude bound: `W ≥ 2` gives `4 e' ≤ 9 u' − 1`. -/
theorem four_e'_le {e u' W' e' : Nat}
    (h' : IsExcursion e 2 u' W' e') (hW : 2 ≤ W') :
    4 * e' ≤ 9 * u' - 1 := by
  have hpeak : 9 * u' = 2 ^ W' * e' + 1 := by
    have := h'.2.2.2.2.2.2
    rw [show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have hsub : 9 * u' - 1 = 2 ^ W' * e' := by omega
  have h4 : 4 ≤ 2 ^ W' := by
    have : (2 : Nat) ^ 2 ≤ 2 ^ W' := two_pow_le_two_pow hW
    simpa using this
  have : 4 * e' ≤ 2 ^ W' * e' := Nat.mul_le_mul_right e' h4
  omega

/-- **The 243/256 comparison.**  For `u ≥ 5`,
`9 u' − 1 < 4 (8 u − 1)` whenever `8 u' = 27 u + 1`. -/
private theorem second_lt_aux {u u' : Nat}
    (hu : 5 ≤ u) (hrel : 8 * u' = 27 * u + 1) :
    9 * u' - 1 < 4 * (8 * u - 1) := by
  have h72 : 72 * u' = 243 * u + 9 := by
    have : 72 * u' = 9 * (8 * u') := by
      have h78 : (72 : Nat) = 9 * 8 := by decide
      rw [h78, Nat.mul_assoc]
    rw [this, hrel]
    omega
  have hcmp : 72 * u' < 256 * u - 24 := by
    rw [h72]
    have : 33 < 13 * u := by omega
    omega
  have h8L : 8 * (9 * u') = 72 * u' := by
    have : (8 : Nat) * 9 = 72 := by decide
    rw [← Nat.mul_assoc, this]
  have h8R : 8 * (32 * u - 3) = 256 * u - 24 := by omega
  have h9 : 9 * u' < 32 * u - 3 := by
    have : 8 * (9 * u') < 8 * (32 * u - 3) := by
      rw [h8L, h8R]
      exact hcmp
    exact Nat.lt_of_mul_lt_mul_left this
  omega


/-! ## 3.  Two-step drop below the original start -/

/-- `u = 1` is the seed `7 → 13`, whose landing has remainder `1`, not `3`. -/
theorem not_u_one_of_land_three {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (e + 5) 3) : 5 ≤ u := by
  have hu : u % 2 = 1 := h.2.1
  have hu4 : u % 4 = 1 := u_one_mod_four_of_v_three_W_one h
  rcases Nat.eq_or_lt_of_le (show 1 ≤ u by omega) with hu1 | hgt
  · subst hu1
    have he : e = 13 := by
      have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
      omega
    subst he
    have : Val2 (13 + 5) 1 := ⟨9, rfl, rfl⟩
    have : (3 : Nat) = 1 := Val2.unique hr this
    omega
  · omega

/-- **Lemma X on `(3, 1)` landings of plus-five valuation `3`.**  One light
odd run, then a `3 (mod 16)` drop, lands below the original start. -/
theorem lemmaX_of_v_three_land_three {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (e + 5) 3) (_hn : 1 < n) :
    ∃ e' : Nat, ExChain n e' ∧ e' < n := by
  have heodd : e % 2 = 1 := h.2.2.1
  have h16 := land_three_mod_sixteen hr
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have ⟨hv', hW'⟩ := (v_two_W_ge_two_iff h').mpr h16
  have h'2 : IsExcursion e 2 u' W' e' := hv' ▸ h'
  have hu : 5 ≤ u := not_u_one_of_land_three h hr
  have hrel : 8 * u' = 27 * u + 1 := eight_u'_of_v_two h h'2
  have hbound := four_e'_le h'2 hW'
  have hlt : 9 * u' - 1 < 4 * (8 * u - 1) := second_lt_aux hu hrel
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have : 4 * e' < 4 * n := by
    have : 4 * e' ≤ 9 * u' - 1 := hbound
    omega
  have hltn : e' < n := Nat.lt_of_mul_lt_mul_left this
  exact ⟨e', ExChain.cons ⟨3, u, 1, h⟩ (ExChain.one ⟨v', u', W', h'⟩), hltn⟩

/-- The witness `39 → 67 → 19`: remainder `3` after one `(3, 1)` step. -/
theorem thirty_nine_land_three :
    IsExcursion 39 3 5 1 67 ∧ Val2 (67 + 5) 3 ∧
    IsExcursion 67 2 17 3 19 ∧ 19 < 39 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨9, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- Remainder `1` after `(3, 1)` is not this theorem: `71 → 121 → 91 > 71`. -/
theorem seventy_one_land_one :
    IsExcursion 71 3 9 1 121 ∧ Val2 (121 + 5) 1 ∧ 91 < 121 ∧ 71 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨63, rfl, rfl⟩,
    by omega, by omega⟩

end ExcursionLand
end Collatz

section AxiomAudit
open Collatz.ExcursionLand
#print axioms land_three_mod_sixteen
#print axioms four_e'_le
#print axioms lemmaX_of_v_three_land_three
end AxiomAudit
