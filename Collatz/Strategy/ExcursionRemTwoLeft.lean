import Collatz.Strategy.ExcursionRemTwo
import Collatz.Strategy.ExcursionNineK

/-!
# Remainder `2` after a `(2, 1)` step, leftover next runs

`ExcursionRemTwo` closed the slice `v' = 4`, `W' ≥ 3`.  The other
next-run lengths split on extra halvings the same way:

* next `v' = 3` and `W' ≥ 2` drops below the original start
  (`4 e' ≤ 27 u' − 1`, and `16 u' = 9 u + 1`);
* next `v' = 3` and `W' = 1` **grows** (`91 → 103 → 175`);
* next `v' = 5` and `W' ≥ 4` drops (`16 e' ≤ 243 u' − 1`);
* next `v' = 5` and `W' ≤ 3` **grows** (`539 → 607 → 577` is `W' = 3`;
  the seed `27 → 31 → 121` is `W' = 1`).

NineK names the next length from `v₂(k − 1)` without a residue covering
of `n`: predecessor valuation `1` is `v' = 3`, and `t > 3` is `v' = 5`.
The remaining open slice is `v' ≥ 6` (NineK collision `t = 3`).
-/

namespace Collatz
namespace ExcursionRemTwoLeft

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionBlock Collatz.ExcursionExit Collatz.ExcursionNineK
open Collatz.ExcursionRemTwo


/-! ## 1.  Next run `v' = 3` -/

/-- Bridge: `16 u' = 9 u + 1` when the landing has `v' = 3`. -/
theorem sixteen_u'_of_v_three {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 3 u' W' e') :
    16 * u' = 9 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_two_W_one h
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

/-- Remainder `2` forces `u ≥ 7`. -/
theorem seven_le_u_of_rem_two {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2) : 7 ≤ u := by
  have hn5 := val2_n_plus_five h hrem
  have h32 : (2 : Nat) ^ 5 = 32 := by decide
  have hdvd : 32 ∣ n + 5 := by
    have := (Val2.dvd_iff_le hn5).mpr (by omega : 5 ≤ 5)
    rwa [h32] at this
  have hn : 27 ≤ n := by
    have : 32 ≤ n + 5 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hn_eq : n = 4 * u - 1 := n_eq_of_v_two_W_one h
  omega

/-- `W' ≥ 2` gives `4 e' ≤ 27 u' − 1`. -/
theorem four_e'_le_v_three {e u' W' e' : Nat}
    (h' : IsExcursion e 3 u' W' e') (hW : 2 ≤ W') :
    4 * e' ≤ 27 * u' - 1 := by
  have hpeak := peak_v_three h'
  have hsub : 27 * u' - 1 = 2 ^ W' * e' := by
    have : 1 ≤ 27 * u' := by
      have : 1 ≤ u' := by
        have : u' % 2 = 1 := h'.2.1
        omega
      omega
    omega
  have h4 : 4 ≤ 2 ^ W' := by
    have : (2 : Nat) ^ 2 ≤ 2 ^ W' := two_pow_le_two_pow hW
    simpa using this
  have : 4 * e' ≤ 2 ^ W' * e' := Nat.mul_le_mul_right e' h4
  omega

/-- `W' = 1` gives `2 e' + 1 = 27 u'`. -/
theorem two_e'_of_W_one {e u' e' : Nat}
    (h' : IsExcursion e 3 u' 1 e') : 2 * e' + 1 = 27 * u' := by
  have := peak_v_three h'
  rw [Nat.pow_one] at this
  omega

/-- Clearing the bridge: `16 (27 u' − 1) = 243 u + 11`. -/
private theorem cleared_v_three {u u' : Nat}
    (hrel : 16 * u' = 9 * u + 1) :
    16 * (27 * u' - 1) = 243 * u + 11 := by
  have hL : 16 * (27 * u') = 27 * (16 * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h243 : (27 : Nat) * 9 = 243 := by decide
  omega

/-- **Lemma X on remainder-`2` landings of next run `v' = 3` with
`W' ≥ 2`.** -/
theorem lemmaX_of_rem_two_v_three {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (h' : IsExcursion e 3 u' W' e') (hW : 2 ≤ W') (_hn : 1 < n) :
    e' < n := by
  have hu := seven_le_u_of_rem_two h hrem
  have hrel := sixteen_u'_of_v_three h h'
  have hbound := four_e'_le_v_three h' hW
  have hn_eq : n = 4 * u - 1 := n_eq_of_v_two_W_one h
  have hcleared := cleared_v_three hrel
  have : 64 * e' ≤ 243 * u + 11 := by
    have : 16 * (4 * e') ≤ 16 * (27 * u' - 1) := Nat.mul_le_mul_left 16 hbound
    omega
  have : 64 * e' < 64 * n := by
    have : 243 * u + 11 < 256 * u - 64 := by
      have : 75 < 13 * u := by omega
      omega
    have : 64 * n = 256 * u - 64 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Negative law.**  Next `v' = 3` with `W' = 1` grows past the start. -/
theorem grows_of_rem_two_v_three_light {n u e u' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (h' : IsExcursion e 3 u' 1 e') : n < e' := by
  have hu := seven_le_u_of_rem_two h hrem
  have hrel := sixteen_u'_of_v_three h h'
  have hpeak := two_e'_of_W_one h'
  have hn_eq : n = 4 * u - 1 := n_eq_of_v_two_W_one h
  have hcleared := cleared_v_three hrel
  have : 32 * e' = 243 * u + 11 := by
    have : 16 * (2 * e' + 1 - 1) = 16 * (27 * u' - 1) := by
      have : 2 * e' + 1 - 1 = 27 * u' - 1 := by omega
      rw [this, hcleared]
    omega
  have : 32 * n < 32 * e' := by
    have : 128 * u - 32 < 243 * u + 11 := by
      have : 0 < 115 * u + 43 := by omega
      omega
    have : 32 * n = 128 * u - 32 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- Predecessor valuation `1` is next run `v' = 3`. -/
theorem next_v_eq_three_of_pred_one {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e')
    (ht : Val2 (k - 1) 1) :
    v' = 3 :=
  (next_v_of_pred_lt h hrem hodd hk hnext ht (by omega : (1 : Nat) < 3)).1

/-- **Dichotomy** at next `v' = 3`. -/
theorem dichotomy_rem_two_v_three {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (h' : IsExcursion e 3 u' W' e') (hn : 1 < n) :
    (2 ≤ W' ∧ e' < n) ∨ (W' = 1 ∧ n < e') := by
  have hW1 : 1 ≤ W' := IsExcursion.one_le_W h'
  rcases Nat.eq_or_lt_of_le hW1 with hW | hW
  · subst hW
    exact Or.inr ⟨rfl, grows_of_rem_two_v_three_light h hrem h'⟩
  · have h2 : 2 ≤ W' := by omega
    exact Or.inl ⟨h2, lemmaX_of_rem_two_v_three h hrem h' h2 hn⟩


/-! ## 2.  Next run `v' = 5` -/

/-- Bridge: `64 u' = 9 u + 1` when the landing has `v' = 5`. -/
theorem sixty_four_u'_of_v_five {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 5 u' W' e') :
    64 * u' = 9 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_two_W_one h
  have hnu' : e + 1 = 32 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 5 = 32 by decide] at this
    exact this
  omega

/-- The peak at `v' = 5`. -/
private theorem peak_v_five {e u' W' e' : Nat}
    (h' : IsExcursion e 5 u' W' e') :
    243 * u' = 2 ^ W' * e' + 1 := by
  have := h'.2.2.2.2.2.2
  rw [show (3 : Nat) ^ 5 = 243 by decide] at this
  exact this

/-- `W' ≥ 4` gives `16 e' ≤ 243 u' − 1`. -/
theorem sixteen_e'_le_v_five {e u' W' e' : Nat}
    (h' : IsExcursion e 5 u' W' e') (hW : 4 ≤ W') :
    16 * e' ≤ 243 * u' - 1 := by
  have hpeak := peak_v_five h'
  have hsub : 243 * u' - 1 = 2 ^ W' * e' := by
    have : 1 ≤ 243 * u' := by
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

/-- `W' ≤ 3` gives `243 u' − 1 ≤ 8 e'`. -/
theorem eight_e'_ge_v_five {e u' W' e' : Nat}
    (h' : IsExcursion e 5 u' W' e') (hW : W' ≤ 3) :
    243 * u' - 1 ≤ 8 * e' := by
  have hpeak := peak_v_five h'
  have h8 : 2 ^ W' ≤ 8 := by
    have : (2 : Nat) ^ W' ≤ 2 ^ 3 := two_pow_le_two_pow hW
    simpa using this
  have : 2 ^ W' * e' ≤ 8 * e' := Nat.mul_le_mul_right e' h8
  omega

/-- Clearing the bridge: `64 (243 u' − 1) = 2187 u + 179`. -/
private theorem cleared_v_five {u u' : Nat}
    (hrel : 64 * u' = 9 * u + 1) :
    64 * (243 * u' - 1) = 2187 * u + 179 := by
  have hL : 64 * (243 * u') = 243 * (64 * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2187 : (243 : Nat) * 9 = 2187 := by decide
  omega

/-- **Lemma X on remainder-`2` landings of next run `v' = 5` with
`W' ≥ 4`.** -/
theorem lemmaX_of_rem_two_v_five {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (h' : IsExcursion e 5 u' W' e') (hW : 4 ≤ W') (_hn : 1 < n) :
    e' < n := by
  have hu := seven_le_u_of_rem_two h hrem
  have hrel := sixty_four_u'_of_v_five h h'
  have hbound := sixteen_e'_le_v_five h' hW
  have hn_eq : n = 4 * u - 1 := n_eq_of_v_two_W_one h
  have hcleared := cleared_v_five hrel
  have : 1024 * e' ≤ 2187 * u + 179 := by
    have : 64 * (16 * e') ≤ 64 * (243 * u' - 1) := Nat.mul_le_mul_left 64 hbound
    omega
  have : 1024 * e' < 1024 * n := by
    have : 2187 * u + 179 < 4096 * u - 1024 := by
      have : 1203 < 1909 * u := by omega
      omega
    have : 1024 * n = 4096 * u - 1024 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Negative law.**  Next `v' = 5` with `W' ≤ 3` grows past the start. -/
theorem grows_of_rem_two_v_five_light {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (h' : IsExcursion e 5 u' W' e') (hW : W' ≤ 3) : n < e' := by
  have hu := seven_le_u_of_rem_two h hrem
  have hrel := sixty_four_u'_of_v_five h h'
  have hge := eight_e'_ge_v_five h' hW
  have hn_eq : n = 4 * u - 1 := n_eq_of_v_two_W_one h
  have hcleared := cleared_v_five hrel
  have : 2187 * u + 179 ≤ 512 * e' := by
    have : 64 * (243 * u' - 1) ≤ 64 * (8 * e') := Nat.mul_le_mul_left 64 hge
    omega
  have : 512 * n < 512 * e' := by
    have : 2048 * u - 512 < 2187 * u + 179 := by
      have : 0 < 139 * u + 691 := by omega
      omega
    have : 512 * n = 2048 * u - 512 := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Dichotomy** at next `v' = 5`. -/
theorem dichotomy_rem_two_v_five {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (h' : IsExcursion e 5 u' W' e') (hn : 1 < n) :
    (4 ≤ W' ∧ e' < n) ∨ (W' ≤ 3 ∧ n < e') := by
  rcases Nat.lt_or_ge W' 4 with hlt | hge
  · have h3 : W' ≤ 3 := by omega
    exact Or.inr ⟨h3, grows_of_rem_two_v_five_light h hrem h' h3⟩
  · exact Or.inl ⟨hge, lemmaX_of_rem_two_v_five h hrem h' hge hn⟩


/-! ## 3.  Witnesses -/

/-- `W' = 1` grows: `91 → 103 → 175`. -/
theorem ninety_one_v_three_W_one :
    IsExcursion 91 2 23 1 103 ∧ Val2 (103 + 5) 2 ∧
    IsExcursion 103 3 13 1 175 ∧ 91 < 175 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨27, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 2` drops: `219 → 247 → 209`. -/
theorem two_nineteen_v_three_W_two :
    IsExcursion 219 2 55 1 247 ∧ Val2 (247 + 5) 2 ∧
    IsExcursion 247 3 31 2 209 ∧ 209 < 219 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨63, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 3` grows: `539 → 607 → 577`. -/
theorem five_thirty_nine_v_five_W_three :
    IsExcursion 539 2 135 1 607 ∧ Val2 (607 + 5) 2 ∧
    IsExcursion 607 5 19 3 577 ∧ 539 < 577 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨153, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 5` drops: `2587 → 2911 → 691`. -/
theorem twenty_five_eighty_seven_v_five_W_five :
    IsExcursion 2587 2 647 1 2911 ∧ Val2 (2911 + 5) 2 ∧
    IsExcursion 2911 5 91 5 691 ∧ 691 < 2587 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨729, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

end ExcursionRemTwoLeft
end Collatz

section AxiomAudit
open Collatz.ExcursionRemTwoLeft
#print axioms lemmaX_of_rem_two_v_three
#print axioms grows_of_rem_two_v_three_light
#print axioms dichotomy_rem_two_v_three
#print axioms lemmaX_of_rem_two_v_five
#print axioms grows_of_rem_two_v_five_light
#print axioms dichotomy_rem_two_v_five
end AxiomAudit
