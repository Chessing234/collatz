import Collatz.Strategy.ExcursionOddLight

/-!
# Remainder `2` after a `(3, 1)` step

A leftover `(v, W) = (3, 1)` step with `v₂(e + 5) = 2` lands on
`e ≡ 7 (mod 8)`, so the next run has odd length `≥ 3`.  The next
extra-halving count then splits each length:

* next `v' = 3` and `W' ≥ 3` contracts below the original start
  (`8 e' ≤ 27 u' − 1`, and `16 u' = 27 u + 1`);
* next `v' = 3` and `W' ≤ 2` **grows** (`487 → 823 → 695` is the `W' = 2`
  law, not a special witness; `W' = 1` is a second `(3, 1)` step);
* next `v' = 4` and `W' ≥ 4` contracts (`16 e' ≤ 81 u' − 1`);
* next `v' = 4` and `W' ≤ 3` **grows** (`2663 → 4495 → 2845`).

`expStep` has no extra halvings, so the `W'` thresholds never appear.
-/

namespace Collatz
namespace ExcursionLandVal2

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionOddLight


/-! ## 1.  Remainder `2` is `e ≡ 7 (mod 8)` -/

/-- Remainder `2` at the landing is `e ≡ 7 (mod 8)`. -/
theorem land_two_mod_eight {e : Nat} (hr : Val2 (e + 5) 2) :
    e % 8 = 7 := by
  have hpow : (2 : Nat) ^ (2 + 1) = 8 := by decide
  have : (e + 5) % 8 = 4 := by
    have := Val2.mod hr
    rwa [hpow] at this
  omega


/-! ## 2.  Next run `v' = 3` -/

/-- Bridge: `16 u' = 27 u + 1` when the landing has `v' = 3`. -/
theorem sixteen_u'_of_v_three {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 3 u' W' e') :
    16 * u' = 27 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
  have hnu' : e + 1 = 8 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  omega

/-- The peak at `v' = 3`. -/
private theorem peak_v_three {e u' W' e' : Nat}
    (h' : IsExcursion e 3 u' W' e') :
    27 * u' = 2 ^ W' * e' + 1 := by
  have := h'.2.2.2.2.2.2
  rw [show (3 : Nat) ^ 3 = 27 by decide] at this
  exact this

/-- `W' ≥ 3` gives `8 e' ≤ 27 u' − 1`. -/
theorem eight_e'_le_v_three {e u' W' e' : Nat}
    (h' : IsExcursion e 3 u' W' e') (hW : 3 ≤ W') :
    8 * e' ≤ 27 * u' - 1 := by
  have hpeak := peak_v_three h'
  have hsub : 27 * u' - 1 = 2 ^ W' * e' := by
    have : 1 ≤ 27 * u' := by
      have : 1 ≤ u' := by
        have : u' % 2 = 1 := h'.2.1
        omega
      omega
    omega
  have h8 : 8 ≤ 2 ^ W' := by
    have : (2 : Nat) ^ 3 ≤ 2 ^ W' := two_pow_le_two_pow hW
    simpa using this
  have : 8 * e' ≤ 2 ^ W' * e' := Nat.mul_le_mul_right e' h8
  omega

/-- `W' ≤ 2` gives `27 u' − 1 ≤ 4 e'`. -/
theorem four_e'_ge_v_three {e u' W' e' : Nat}
    (h' : IsExcursion e 3 u' W' e') (hW : W' ≤ 2) :
    27 * u' - 1 ≤ 4 * e' := by
  have hpeak := peak_v_three h'
  have h4 : 2 ^ W' ≤ 4 := by
    have : (2 : Nat) ^ W' ≤ 2 ^ 2 := two_pow_le_two_pow hW
    simpa using this
  have : 2 ^ W' * e' ≤ 4 * e' := Nat.mul_le_mul_right e' h4
  omega

/-- Clearing the bridge: `16 (27 u' − 1) = 729 u + 11`. -/
private theorem cleared_v_three {u u' : Nat}
    (hrel : 16 * u' = 27 * u + 1) :
    16 * (27 * u' - 1) = 729 * u + 11 := by
  have hL : 16 * (27 * u') = 27 * (16 * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h729 : (27 : Nat) * 27 = 729 := by decide
  omega

/-- **Lemma X on `(3, 1)` remainder-`2` landings of next run `v' = 3`
with `W' ≥ 3`.** -/
theorem lemmaX_of_land_two_v_three {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (_hr : Val2 (e + 5) 2)
    (h' : IsExcursion e 3 u' W' e') (hW : 3 ≤ W') (_hn : 1 < n) :
    e' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hrel := sixteen_u'_of_v_three h h'
  have hbound := eight_e'_le_v_three h' hW
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_three hrel
  have : 128 * e' ≤ 729 * u + 11 := by
    have : 16 * (8 * e') ≤ 16 * (27 * u' - 1) := Nat.mul_le_mul_left 16 hbound
    omega
  have : 128 * e' < 128 * n := by
    have : 729 * u + 11 < 1024 * u - 128 := by
      have : 139 < 295 * u := by omega
      omega
    have : 128 * n = 1024 * u - 128 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Negative law.**  Next `v' = 3` with `W' ≤ 2` grows past the start. -/
theorem grows_of_land_two_v_three_light {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (_hr : Val2 (e + 5) 2)
    (h' : IsExcursion e 3 u' W' e') (hW : W' ≤ 2) : n < e' := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hrel := sixteen_u'_of_v_three h h'
  have hge := four_e'_ge_v_three h' hW
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_three hrel
  have : 729 * u + 11 ≤ 64 * e' := by
    have : 16 * (27 * u' - 1) ≤ 16 * (4 * e') := Nat.mul_le_mul_left 16 hge
    omega
  have : 64 * n < 64 * e' := by
    have : 512 * u - 64 < 729 * u + 11 := by
      have : 0 < 217 * u + 75 := by omega
      omega
    have : 64 * n = 512 * u - 64 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy** at next `v' = 3`. -/
theorem dichotomy_land_two_v_three {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (e + 5) 2)
    (h' : IsExcursion e 3 u' W' e') (hn : 1 < n) :
    (3 ≤ W' ∧ e' < n) ∨ (W' ≤ 2 ∧ n < e') := by
  rcases Nat.lt_or_ge W' 3 with hlt | hge
  · have h2 : W' ≤ 2 := by omega
    exact Or.inr ⟨h2, grows_of_land_two_v_three_light h hr h' h2⟩
  · exact Or.inl ⟨hge, lemmaX_of_land_two_v_three h hr h' hge hn⟩


/-! ## 3.  Next run `v' = 4` -/

/-- Bridge: `32 u' = 27 u + 1` when the landing has `v' = 4`. -/
theorem thirty_two_u'_of_v_four {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 4 u' W' e') :
    32 * u' = 27 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
  have hnu' : e + 1 = 16 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 4 = 16 by decide] at this
    exact this
  omega

/-- The peak at `v' = 4`. -/
private theorem peak_v_four {e u' W' e' : Nat}
    (h' : IsExcursion e 4 u' W' e') :
    81 * u' = 2 ^ W' * e' + 1 := by
  have := h'.2.2.2.2.2.2
  rw [show (3 : Nat) ^ 4 = 81 by decide] at this
  exact this

/-- `W' ≥ 4` gives `16 e' ≤ 81 u' − 1`. -/
theorem sixteen_e'_le_v_four {e u' W' e' : Nat}
    (h' : IsExcursion e 4 u' W' e') (hW : 4 ≤ W') :
    16 * e' ≤ 81 * u' - 1 := by
  have hpeak := peak_v_four h'
  have hsub : 81 * u' - 1 = 2 ^ W' * e' := by
    have : 1 ≤ 81 * u' := by
      have : 1 ≤ u' := by
        have : u' % 2 = 1 := h'.2.1
        omega
      omega
    omega
  have h16 : 16 ≤ 2 ^ W' := by
    have : (2 : Nat) ^ 4 ≤ 2 ^ W' := two_pow_le_two_pow hW
    simpa using this
  have : 16 * e' ≤ 2 ^ W' * e' := Nat.mul_le_mul_right e' h16
  omega

/-- `W' ≤ 3` gives `81 u' − 1 ≤ 8 e'`. -/
theorem eight_e'_ge_v_four {e u' W' e' : Nat}
    (h' : IsExcursion e 4 u' W' e') (hW : W' ≤ 3) :
    81 * u' - 1 ≤ 8 * e' := by
  have hpeak := peak_v_four h'
  have h8 : 2 ^ W' ≤ 8 := by
    have : (2 : Nat) ^ W' ≤ 2 ^ 3 := two_pow_le_two_pow hW
    simpa using this
  have : 2 ^ W' * e' ≤ 8 * e' := Nat.mul_le_mul_right e' h8
  omega

/-- Clearing the bridge: `32 (81 u' − 1) = 2187 u + 49`. -/
private theorem cleared_v_four {u u' : Nat}
    (hrel : 32 * u' = 27 * u + 1) :
    32 * (81 * u' - 1) = 2187 * u + 49 := by
  have hL : 32 * (81 * u') = 81 * (32 * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2187 : (81 : Nat) * 27 = 2187 := by decide
  omega

/-- **Lemma X on `(3, 1)` remainder-`2` landings of next run `v' = 4`
with `W' ≥ 4`.** -/
theorem lemmaX_of_land_two_v_four {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (_hr : Val2 (e + 5) 2)
    (h' : IsExcursion e 4 u' W' e') (hW : 4 ≤ W') (_hn : 1 < n) :
    e' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hrel := thirty_two_u'_of_v_four h h'
  have hbound := sixteen_e'_le_v_four h' hW
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_four hrel
  have : 512 * e' ≤ 2187 * u + 49 := by
    have : 32 * (16 * e') ≤ 32 * (81 * u' - 1) := Nat.mul_le_mul_left 32 hbound
    omega
  have : 512 * e' < 512 * n := by
    have : 2187 * u + 49 < 4096 * u - 512 := by
      have : 561 < 1909 * u := by omega
      omega
    have : 512 * n = 4096 * u - 512 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Negative law.**  Next `v' = 4` with `W' ≤ 3` grows past the start. -/
theorem grows_of_land_two_v_four_light {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (_hr : Val2 (e + 5) 2)
    (h' : IsExcursion e 4 u' W' e') (hW : W' ≤ 3) : n < e' := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hrel := thirty_two_u'_of_v_four h h'
  have hge := eight_e'_ge_v_four h' hW
  have hn_eq : n = 8 * u - 1 := n_eq_of_v_three_W_one h
  have hcleared := cleared_v_four hrel
  have : 2187 * u + 49 ≤ 256 * e' := by
    have : 32 * (81 * u' - 1) ≤ 32 * (8 * e') := Nat.mul_le_mul_left 32 hge
    omega
  have : 256 * n < 256 * e' := by
    have : 2048 * u - 256 < 2187 * u + 49 := by
      have : 0 < 139 * u + 305 := by omega
      omega
    have : 256 * n = 2048 * u - 256 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy** at next `v' = 4`. -/
theorem dichotomy_land_two_v_four {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (hr : Val2 (e + 5) 2)
    (h' : IsExcursion e 4 u' W' e') (hn : 1 < n) :
    (4 ≤ W' ∧ e' < n) ∨ (W' ≤ 3 ∧ n < e') := by
  rcases Nat.lt_or_ge W' 4 with hlt | hge
  · have h3 : W' ≤ 3 := by omega
    exact Or.inr ⟨h3, grows_of_land_two_v_four_light h hr h' h3⟩
  · exact Or.inl ⟨hge, lemmaX_of_land_two_v_four h hr h' hge hn⟩


/-! ## 4.  Witnesses -/

/-- `W' = 2` grows: `487 → 823 → 695`. -/
theorem four_eighty_seven_v_three_W_two :
    IsExcursion 487 3 61 1 823 ∧ Val2 (823 + 5) 2 ∧
    IsExcursion 823 3 103 2 695 ∧ 487 < 695 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨207, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 3` drops: `2023 → 3415 → 1441`. -/
theorem two_thousand_twenty_three_v_three_W_three :
    IsExcursion 2023 3 253 1 3415 ∧ Val2 (3415 + 5) 2 ∧
    IsExcursion 3415 3 427 3 1441 ∧ 1441 < 2023 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨855, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 3` grows: `2663 → 4495 → 2845`. -/
theorem two_six_six_three_v_four_W_three :
    IsExcursion 2663 3 333 1 4495 ∧ Val2 (4495 + 5) 2 ∧
    IsExcursion 4495 4 281 3 2845 ∧ 2663 < 2845 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨1125, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 4` drops: `615 → 1039 → 329`. -/
theorem six_fifteen_v_four_W_four :
    IsExcursion 615 3 77 1 1039 ∧ Val2 (1039 + 5) 2 ∧
    IsExcursion 1039 4 65 4 329 ∧ 329 < 615 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨261, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

end ExcursionLandVal2
end Collatz

section AxiomAudit
open Collatz.ExcursionLandVal2
#print axioms land_two_mod_eight
#print axioms lemmaX_of_land_two_v_three
#print axioms grows_of_land_two_v_three_light
#print axioms dichotomy_land_two_v_three
#print axioms lemmaX_of_land_two_v_four
#print axioms grows_of_land_two_v_four_light
#print axioms dichotomy_land_two_v_four
end AxiomAudit
