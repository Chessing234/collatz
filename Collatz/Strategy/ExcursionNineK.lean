import Collatz.Strategy.ExcursionExit
import Collatz.Strategy.ExcursionLTE

/-!
# Next run length after remainder `2`, via `v₂(9k − 1)`

`ExcursionExit` names a `(v, W) = (2, 1)` step with remaining valuation
`2` as `n + 5 = 32k` with `k` odd, and gives the next opening run as

  `v' = 2 + v₂(9k − 1)`.

This file computes that valuation by the ultrametric law, not by a
residue covering of `k`.  Split

  `9k − 1  =  (k − 1)  +  8k`.

The second summand has valuation `3` (`k` is odd).  For `k > 1` the
first has some `t ≥ 1`, and:

* `t < 3` ⇒ `v₂(9k − 1) = t`, hence `v' = 2 + t ∈ {3, 4}`;
* `t > 3` ⇒ `v₂(9k − 1) = 3`, hence `v' = 5`;
* `t = 3` ⇒ `v₂(9k − 1) ≥ 4`, hence `v' ≥ 6`.

The seed `k = 1` is `n = 27`: `k − 1 = 0` carries no valuation, and
`9k − 1 = 8` has `v₂ = 3`, so `v' = 5` (the run `31` of length `5`).
That next excursion lands at `121 > 27`.  The formula for `v'` does
**not** force a drop below the original start.
-/

namespace Collatz
namespace ExcursionNineK

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionExit Collatz.ExcursionLTE


/-! ## 1.  The split `9k − 1 = (k − 1) + 8k` -/

/-- **Algebraic identity.**  Valid for every positive `k`, including the
seed `k = 1` where the first summand is `0`. -/
theorem nine_k_split {k : Nat} (hk : 1 ≤ k) :
    9 * k - 1 = (k - 1) + 8 * k := by
  omega


/-! ## 2.  Valuations of the two summands -/

/-- Scaling by `8 = 2 ^ 3` on an odd cofactor. -/
theorem val2_eight_k {k : Nat} (hodd : k % 2 = 1) : Val2 (8 * k) 3 := by
  have h8 : Val2 (8 : Nat) 3 := by
    have : (8 : Nat) = 2 ^ 3 := by decide
    rw [this]
    exact Val2.two_pow 3
  have := Val2.mul h8 (Val2.of_odd hodd)
  simpa using this

/-- Odd `k > 1` has even predecessor, so `v₂(k − 1) ≥ 1`. -/
theorem val2_k_pred_pos {k t : Nat} (hodd : k % 2 = 1) (h1 : 1 < k)
    (ht : Val2 (k - 1) t) : 1 ≤ t :=
  val2_u_pred_pos hodd h1 ht


/-! ## 3.  Ultrametric reading of `v₂(9k − 1)` -/

/-- **Smaller predecessor.**  If `v₂(k − 1) < 3` then `v₂(9k − 1)` is
that value. -/
theorem val2_nine_k_of_pred_lt {k t : Nat}
    (hodd : k % 2 = 1) (h1 : 1 < k)
    (ht : Val2 (k - 1) t) (hlt : t < 3) :
    Val2 (9 * k - 1) t := by
  have hsplit := nine_k_split (Nat.le_of_lt h1)
  have hsum := Val2.add_of_lt ht (val2_eight_k hodd) hlt
  exact hsplit ▸ hsum

/-- **Smaller eight-term.**  If `3 < v₂(k − 1)` then `v₂(9k − 1) = 3`. -/
theorem val2_nine_k_of_pred_gt {k t : Nat}
    (hodd : k % 2 = 1) (h1 : 1 < k)
    (ht : Val2 (k - 1) t) (hgt : 3 < t) :
    Val2 (9 * k - 1) 3 := by
  have hsplit : 9 * k - 1 = 8 * k + (k - 1) := by
    rw [nine_k_split (Nat.le_of_lt h1), Nat.add_comm]
  have hsum := Val2.add_of_lt (val2_eight_k hodd) ht hgt
  exact hsplit ▸ hsum

/-- **Collision.**  Equal valuations force `v₂(9k − 1) ≥ 4`. -/
theorem val2_nine_k_of_pred_eq {k s : Nat}
    (hodd : k % 2 = 1) (h1 : 1 < k)
    (ht : Val2 (k - 1) 3) (hs : Val2 (9 * k - 1) s) :
    4 ≤ s := by
  have hsplit := nine_k_split (Nat.le_of_lt h1)
  have hsum : Val2 ((k - 1) + 8 * k) s := hsplit ▸ hs
  exact val2_add_succ_le ht (val2_eight_k hodd) hsum

/-- The collision, producing the valuation rather than assuming it. -/
theorem exists_val2_nine_k_of_pred_eq {k : Nat}
    (hodd : k % 2 = 1) (h1 : 1 < k) (ht : Val2 (k - 1) 3) :
    ∃ s, 4 ≤ s ∧ Val2 (9 * k - 1) s := by
  have hpos : 0 < 9 * k - 1 := by omega
  obtain ⟨s, hs⟩ := Val2.exists_of_pos hpos
  exact ⟨s, val2_nine_k_of_pred_eq hodd h1 ht hs, hs⟩


/-! ## 4.  The seed `k = 1` -/

/-- `k = 1` is the unique start `n = 27`. -/
theorem eq_twenty_seven_of_k_one {n : Nat} (hk : n + 5 = 32 * 1) : n = 27 := by
  omega

/-- Direct computation: `9 · 1 − 1 = 8` has valuation `3`.  (`k − 1 = 0`
has no `Val2`, so the ultrametric cases above do not apply.) -/
theorem val2_nine_one : Val2 (9 * 1 - 1) 3 := by
  have h : (9 : Nat) * 1 - 1 = 8 := by decide
  have h8 : (8 : Nat) = 2 ^ 3 := by decide
  rw [h, h8]
  exact Val2.two_pow 3


/-! ## 5.  The next run length `v'` -/

/-- Translation: `v' = 2 + v₂(9k − 1)`. -/
theorem next_v_eq_add {n u e k v' u' W' e' s : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e')
    (hs : Val2 (9 * k - 1) s) :
    v' = s + 2 := by
  have hv := val2_nine_k h hrem hodd hk hnext
  have heq := Val2.unique hv hs
  have hge := next_v_ge_three h hrem hnext
  omega

/-- `t < 3` gives `v' = 2 + t ∈ {3, 4}`. -/
theorem next_v_of_pred_lt {n u e k v' u' W' e' t : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e')
    (ht : Val2 (k - 1) t) (hlt : t < 3) :
    v' = 2 + t ∧ (v' = 3 ∨ v' = 4) := by
  have h1 : 1 < k := by
    have : 0 < k - 1 := Val2.pos ht
    omega
  have hs := val2_nine_k_of_pred_lt hodd h1 ht hlt
  have hv := next_v_eq_add h hrem hodd hk hnext hs
  have ht1 := val2_k_pred_pos hodd h1 ht
  omega

/-- `3 < t` gives `v' = 5`. -/
theorem next_v_of_pred_gt {n u e k v' u' W' e' t : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e')
    (ht : Val2 (k - 1) t) (hgt : 3 < t) :
    v' = 5 := by
  have h1 : 1 < k := by
    have : 0 < k - 1 := Val2.pos ht
    omega
  have hs := val2_nine_k_of_pred_gt hodd h1 ht hgt
  have hv := next_v_eq_add h hrem hodd hk hnext hs
  omega

/-- `t = 3` gives `v' ≥ 6`. -/
theorem next_v_of_pred_eq {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e')
    (ht : Val2 (k - 1) 3) :
    6 ≤ v' := by
  have h1 : 1 < k := by
    have : 0 < k - 1 := Val2.pos ht
    omega
  have hv := val2_nine_k h hrem hodd hk hnext
  have hge := val2_nine_k_of_pred_eq hodd h1 ht hv
  have : 3 ≤ v' := next_v_ge_three h hrem hnext
  omega

/-- The seed: `k = 1` gives `v' = 5`. -/
theorem next_v_of_k_one {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hk : n + 5 = 32 * 1)
    (hnext : IsExcursion e v' u' W' e') :
    v' = 5 := by
  have hodd : (1 : Nat) % 2 = 1 := by decide
  have hv := next_v_eq_add h hrem hodd hk hnext val2_nine_one
  omega

/-- **The formula, whole.**  Every odd `k` is the seed or has a predecessor
valuation, and `v'` is determined either way. -/
theorem next_v_formula {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e') :
    (k = 1 ∧ v' = 5) ∨
      (∃ t, Val2 (k - 1) t ∧
        ((t < 3 ∧ v' = 2 + t) ∨ (3 < t ∧ v' = 5) ∨ (t = 3 ∧ 6 ≤ v'))) := by
  have hk1 : 1 ≤ k := by omega
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt
  · exact Or.inl ⟨rfl, next_v_of_k_one h hrem hk hnext⟩
  · obtain ⟨t, ht⟩ := Val2.exists_of_pos (by omega : 0 < k - 1)
    refine Or.inr ⟨t, ht, ?_⟩
    rcases Nat.lt_trichotomy t 3 with h1 | h2 | h3
    · exact Or.inl ⟨h1, (next_v_of_pred_lt h hrem hodd hk hnext ht h1).1⟩
    · subst h2
      exact Or.inr (Or.inr ⟨rfl, next_v_of_pred_eq h hrem hodd hk hnext ht⟩)
    · exact Or.inr (Or.inl ⟨h3, next_v_of_pred_gt h hrem hodd hk hnext ht h3⟩)


/-! ## 6.  The formula does not force a drop -/

/-- The seed realises `k = 1`, `v' = 5`, and grows: `27 → 31 → 121`. -/
theorem twenty_seven_is_k_one :
    IsExcursion 27 2 7 1 31 ∧
    Val2 (31 + 5) 2 ∧
    27 + 5 = 32 * 1 ∧
    IsExcursion 31 5 1 1 121 ∧
    Val2 (9 * 1 - 1) 3 ∧
    27 < 121 :=
  ⟨twenty_seven_next_grows.1, twenty_seven_next_grows.2.1, rfl,
    twenty_seven_next_grows.2.2.1, val2_nine_one,
    twenty_seven_next_grows.2.2.2⟩

/-- **Negative theorem.**  A remainder-`2` `(2, 1)` step followed by its
next excursion is not forced below the original start. -/
theorem next_not_force_drop :
    ¬ (∀ n u e v' u' W' e' : Nat,
        IsExcursion n 2 u 1 e →
        Val2 (e + 5) 2 →
        IsExcursion e v' u' W' e' →
        e' < n) :=
  ExcursionExit.next_not_force_drop

end ExcursionNineK
end Collatz

section AxiomAudit
open Collatz.ExcursionNineK
#print axioms nine_k_split
#print axioms val2_eight_k
#print axioms val2_k_pred_pos
#print axioms val2_nine_k_of_pred_lt
#print axioms val2_nine_k_of_pred_gt
#print axioms val2_nine_k_of_pred_eq
#print axioms exists_val2_nine_k_of_pred_eq
#print axioms val2_nine_one
#print axioms next_v_eq_add
#print axioms next_v_of_pred_lt
#print axioms next_v_of_pred_gt
#print axioms next_v_of_pred_eq
#print axioms next_v_of_k_one
#print axioms next_v_formula
#print axioms twenty_seven_is_k_one
#print axioms next_not_force_drop
end AxiomAudit
