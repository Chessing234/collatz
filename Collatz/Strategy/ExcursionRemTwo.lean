import Collatz.Strategy.ExcursionBlock
import Collatz.Strategy.ExcursionExit
import Collatz.Strategy.ExcursionNineK

/-!
# Remainder `2` then a `v' = 4` drop with `W' ≥ 3`

A leftover `(v, W) = (2, 1)` step with remaining valuation `2` has
`n + 5 = 32k` (`k` odd) and next run length `v' = 2 + v₂(9k − 1)`
(`ExcursionNineK`).  The ultrametric case `v₂(k − 1) = 2` is exactly
`v' = 4`.

One light step grows by `9/8`.  A `v = 4` landing with `W ≥ 3` contracts
by at most `81 / 2^7 = 81/128`.  The product is

  `(9/8) * (81/128) = 729/1024 < 1`,

so the second landing sits below the *original* start, not merely below
`e`.  The `W = 3` upper bound is already strictly contracting for every
`(2, 1)` start; larger `W` only helps.  The hypothesis is the next
excursion itself (`v' = 4` and `W' ≥ 3`), not a residue of `n`.

The seed `27 → 31` has remainder `2` but `v' = 5` (`k = 1`), and lands
at `121 > 27`.  That is not this theorem.  The `W = 1` and `W = 2`
siblings of `v' = 4` grow (`155 → 445`, `411 → 587`); three extra
halvings are the threshold.
-/

namespace Collatz
namespace ExcursionRemTwo

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionBlock Collatz.ExcursionExit Collatz.ExcursionNineK


/-! ## 1.  NineK specialisation: `v₂(k − 1) = 2` is `v' = 4` -/

/-- **The next run is length four.**  Predecessor valuation `2` is the
strictly smaller summand in `9k − 1 = (k − 1) + 8k`, so
`v₂(9k − 1) = 2` and `v' = 2 + 2`. -/
theorem next_v_eq_four_of_pred_two {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e')
    (ht : Val2 (k - 1) 2) :
    v' = 4 :=
  (next_v_of_pred_lt h hrem hodd hk hnext ht (by omega : (2 : Nat) < 3)).1


/-! ## 2.  The `W = 3` upper bound -/

/-- Every `(2, 1)` start is at least `11`: the cofactor `u = 1` would
force an even landing. -/
theorem eleven_le_of_v_two_W_one {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) : 11 ≤ n := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_two_W_one h
  have he : e % 2 = 1 := h.2.2.1
  have hu : u % 2 = 1 := h.2.1
  omega

/-- `W ≥ 3` gives `2^{W+7} ≥ 1024`. -/
private theorem pow_W_ge_ten {W : Nat} (hW : 3 ≤ W) :
    1024 ≤ 2 ^ (W + 7) := by
  have h10 : (2 : Nat) ^ 10 = 1024 := by decide
  have : (2 : Nat) ^ 10 ≤ 2 ^ (W + 7) := two_pow_le_two_pow (by omega)
  rwa [h10] at this

/-- Integer form of the two-step peak at `v' = 4`. -/
theorem two_step_v_four {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hnext : IsExcursion e 4 u' W' e') :
    81 * (9 * n + 13) = 2 ^ (W' + 7) * e' + 128 := by
  have hid := two_step_identity h hnext
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  have hR : (2 : Nat) ^ (4 + 3) = 128 := by decide
  have hL : 4 + W' + 3 = W' + 7 := by omega
  rw [h81, hR, hL] at hid
  exact hid

/-- **The 729/1024 comparison.**  A `v = 4`, `W ≥ 3` landing after one
`(2, 1)` step satisfies `1024 e' ≤ 729 n + 925`, with equality at
`W = 3`. -/
theorem landing_upper_of_v_four_W_ge_three {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hnext : IsExcursion e 4 u' W' e')
    (hW : 3 ≤ W') :
    1024 * e' ≤ 729 * n + 925 := by
  have hid := two_step_v_four h hnext
  have hpow := pow_W_ge_ten hW
  have hmul : 1024 * e' ≤ 2 ^ (W' + 7) * e' := Nat.mul_le_mul_right e' hpow
  have hsub : 2 ^ (W' + 7) * e' = 81 * (9 * n + 13) - 128 := by omega
  have hdist : 81 * (9 * n + 13) = 729 * n + 1053 := by
    have hadd : 81 * (9 * n + 13) = 81 * (9 * n) + 81 * 13 :=
      Nat.mul_add 81 (9 * n) 13
    have h729 : 81 * (9 * n) = 729 * n := by
      have hc : (81 : Nat) * 9 = 729 := by decide
      rw [← Nat.mul_assoc, hc]
    have h13 : (81 : Nat) * 13 = 1053 := by decide
    rw [hadd, h729, h13]
  have hrhs : 81 * (9 * n + 13) - 128 = 729 * n + 925 := by
    rw [hdist]
    omega
  calc
    1024 * e' ≤ 2 ^ (W' + 7) * e' := hmul
    _ = 81 * (9 * n + 13) - 128 := hsub
    _ = 729 * n + 925 := hrhs

/-- The composition is strictly contracting once `n ≥ 11`. -/
private theorem drop_coeff {n : Nat} (hn : 11 ≤ n) :
    729 * n + 925 < 1024 * n := by
  have h295 : 925 < 295 * n := by
    have hmin : 295 * 11 ≤ 295 * n := Nat.mul_le_mul_left 295 hn
    have hnum : (925 : Nat) < 295 * 11 := by decide
    omega
  have hsum : (729 : Nat) + 295 = 1024 := by decide
  have hsplit : 729 * n + 295 * n = 1024 * n := by
    rw [← Nat.add_mul, hsum]
  omega


/-! ## 3.  Two-step drop below the original start -/

/-- **Lemma X on remainder-`2` landings of next run `v' = 4` with
`W' ≥ 3`.**  One light even run, then a heavy `v = 4` drop, lands below
the original start. -/
theorem lemmaX_of_rem_two_v_four {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (_hrem : Val2 (e + 5) 2)
    (hnext : IsExcursion e 4 u' W' e') (hW : 3 ≤ W') (_hn : 1 < n) :
    e' < n := by
  have hn11 := eleven_le_of_v_two_W_one h
  have hbound := landing_upper_of_v_four_W_ge_three h hnext hW
  have hcoeff := drop_coeff hn11
  have : 1024 * e' < 1024 * n := Nat.lt_of_le_of_lt hbound hcoeff
  exact Nat.lt_of_mul_lt_mul_left this

/-- Same drop, with `v' = 4` supplied by `v₂(k − 1) = 2` rather than as
a hypothesis on the next excursion. -/
theorem lemmaX_of_pred_two {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (ht : Val2 (k - 1) 2)
    (hnext : IsExcursion e v' u' W' e') (hW : 3 ≤ W') (hn : 1 < n) :
    e' < n := by
  have hv : v' = 4 := next_v_eq_four_of_pred_two h hrem hodd hk hnext ht
  subst hv
  exact lemmaX_of_rem_two_v_four h hrem hnext hW hn


/-! ## 4.  Witnesses -/

/-- The `W = 3` bound is attained and still drops:
`1947 → 2191 → 1387`.  Here `k = 61` and `v₂(k − 1) = 2`. -/
theorem nineteen_forty_seven_v_four_W_three :
    IsExcursion 1947 2 487 1 2191 ∧
    Val2 (2191 + 5) 2 ∧
    1947 + 5 = 32 * 61 ∧
    Val2 (61 - 1) 2 ∧
    IsExcursion 2191 4 137 3 1387 ∧
    1387 < 1947 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨549, rfl, rfl⟩,
    rfl,
    ⟨15, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- Remainder `2` with `v' = 5` is not this theorem: the seed
`27 → 31 → 121` grows. -/
theorem twenty_seven_v_five :
    IsExcursion 27 2 7 1 31 ∧
    Val2 (31 + 5) 2 ∧
    IsExcursion 31 5 1 1 121 ∧
    27 < 121 :=
  twenty_seven_next_grows

/-- `W' = 1` after `v' = 4` grows: `155 → 175 → 445`. -/
theorem one_fifty_five_W_one :
    IsExcursion 155 2 39 1 175 ∧
    Val2 (175 + 5) 2 ∧
    IsExcursion 175 4 11 1 445 ∧
    155 < 445 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨45, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- `W' = 2` after `v' = 4` grows: `411 → 463 → 587`. -/
theorem four_eleven_W_two :
    IsExcursion 411 2 103 1 463 ∧
    Val2 (463 + 5) 2 ∧
    IsExcursion 463 4 29 2 587 ∧
    411 < 587 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨117, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

end ExcursionRemTwo
end Collatz

section AxiomAudit
open Collatz.ExcursionRemTwo
#print axioms next_v_eq_four_of_pred_two
#print axioms eleven_le_of_v_two_W_one
#print axioms two_step_v_four
#print axioms landing_upper_of_v_four_W_ge_three
#print axioms lemmaX_of_rem_two_v_four
#print axioms lemmaX_of_pred_two
#print axioms nineteen_forty_seven_v_four_W_three
#print axioms twenty_seven_v_five
end AxiomAudit
