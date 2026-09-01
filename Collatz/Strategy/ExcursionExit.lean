import Collatz.Strategy.ExcursionBlock
import Collatz.Strategy.ExcursionMap
import Collatz.Strategy.LiftExponent

/-!
# Exit from a `(2, 1)` step with remaining valuation `2`

A `(v, W) = (2, 1)` excursion has the integer clock

  `8(e + 5) = 9(n + 5)`,

so the 2-adic valuation drops by exactly three: `v₂(e + 5) = v₂(n + 5) − 3`.
After that fuel is spent the remainder is `1`, `2`, or `3`:

* remainder `1` is `e ≡ 1 (mod 4)`, hence `drop_of_v_one`;
* remainder `3` is `e ≡ 3 (mod 16)`, hence `drop_of_three_mod_sixteen`;
* remainder `2` is `e ≡ 7 (mod 8)`, an opening run of odd length `≥ 3`.

This file names the **exact next excursion** of that last case, from
`IsExcursion n 2 u 1 e` and `Val2 (e + 5) 2`, with no modulus covering.

The start is `n + 5 = 32k` with `k` odd.  The landing satisfies
`e + 1 = 4(9k − 1)`, so the next run length is

  `v' = v₂(e + 1) = 2 + v₂(9k − 1)`,

and the next extra-halving count `W'` is cut out by the peak identity

  `3^{v'} (9k − 1) = 2^{v'−2} (2^{W'} e' + 1)`.

That is an equality of naturals, not a list of residues.  The next
excursion does **not** drop below the original start: `27 → 31 → 121`
with `121 > 27`.  No 7-mod-8 sieve is attempted.
-/

namespace Collatz
namespace ExcursionExit

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap Collatz.ExcursionBlock


/-! ## 1.  The `(2, 1)` clock, and the valuation shift -/

/-- **Integer clock.**  Dual of `landing_n_of_v_two_W_one`, written as a
translation that preserves the 2-adic content of `n + 5`. -/
theorem eight_clock {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    8 * (e + 5) = 9 * (n + 5) := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_two_W_one h
  omega

/-- The same clock as a successor identity: `8(e + 1) = 9n + 13`. -/
theorem eight_succ {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    8 * (e + 1) = 9 * n + 13 := by
  have hclock := eight_clock h
  omega

/-- Scaling by `9` does not change the valuation. -/
private theorem val2_nine_mul {x r : Nat} (h : Val2 x r) : Val2 (9 * x) r := by
  have h9 : Val2 (9 : Nat) 0 := Val2.of_odd (by decide)
  have := Val2.mul h9 h
  simpa using this

/-- Converse: the odd factor `9` can be cancelled from a valuation. -/
private theorem val2_of_nine_mul {x r : Nat} (hx : 0 < x) (h : Val2 (9 * x) r) :
    Val2 x r := by
  obtain ⟨s, hs⟩ := Val2.exists_of_pos hx
  exact (Val2.unique (val2_nine_mul hs) h) ▸ hs

/-- Scaling by `8 = 2 ^ 3` raises the valuation by exactly three. -/
private theorem val2_eight_mul {x r : Nat} (h : Val2 x r) :
    Val2 (8 * x) (r + 3) := by
  have h8 : (8 : Nat) = 2 ^ 3 := by decide
  rw [h8]
  have := Val2.two_pow_mul h 3
  simpa [Nat.add_comm] using this

/-- **Fuel identity.**  The clock shifts the valuation of `· + 5` by `−3`. -/
theorem val2_plus_five_shift {n u e r : Nat}
    (h : IsExcursion n 2 u 1 e) (hr : Val2 (e + 5) r) :
    Val2 (n + 5) (r + 3) := by
  have hclock := eight_clock h
  have h8 := val2_eight_mul hr
  have hpos : 0 < n + 5 := by
    have : 0 < 8 * (e + 5) := Val2.pos h8
    omega
  have h9 : Val2 (9 * (n + 5)) (r + 3) := hclock ▸ h8
  exact val2_of_nine_mul hpos h9

/-- Remainder `2` at the landing is valuation `5` at the start. -/
theorem val2_n_plus_five {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2) :
    Val2 (n + 5) 5 := by
  have := val2_plus_five_shift h hrem
  simpa using this


/-! ## 2.  Remainder `2` is `e ≡ 7 (mod 8)`, so the next run has length `≥ 3` -/

/-- `v₂(e + 5) = 2` is the class `e ≡ 7 (mod 8)`. -/
theorem e_seven_mod_eight {n u e : Nat}
    (_h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2) :
    e % 8 = 7 := by
  have : (e + 5) % 8 = 4 := Val2.two_iff.mp hrem
  omega

/-- The next opening run is an odd-`v` leftover: length at least three. -/
theorem next_v_ge_three {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hnext : IsExcursion e v' u' W' e') :
    3 ≤ v' := by
  have he8 := e_seven_mod_eight h hrem
  have hval := val2_succ_of hnext
  have hdvd : (2 : Nat) ^ 3 ∣ e + 1 := by
    have : (e + 1) % 8 = 0 := by omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hval).mp hdvd


/-! ## 3.  Odd cofactor of `n + 5`, and the exact next `v'` -/

/-- **The start in remaining-valuation coordinates.**  Remainder `2` means
`n + 5 = 32k` with `k` odd. -/
theorem exists_k {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2) :
    ∃ k : Nat, k % 2 = 1 ∧ n + 5 = 32 * k := by
  obtain ⟨k, hk, heq⟩ := val2_n_plus_five h hrem
  refine ⟨k, hk, ?_⟩
  have h32 : (2 : Nat) ^ 5 = 32 := by decide
  rwa [h32] at heq

/-- The clock evaluated on `n + 5 = 32k`. -/
theorem e_plus_five_of_k {n u e k : Nat}
    (h : IsExcursion n 2 u 1 e) (hk : n + 5 = 32 * k) :
    e + 5 = 36 * k := by
  have hclock := eight_clock h
  have hmul : 8 * (e + 5) = 8 * (36 * k) := by
    rw [hclock, hk]
    have h9 : (9 : Nat) * 32 = 8 * 36 := by decide
    calc
      9 * (32 * k) = (9 * 32) * k := (Nat.mul_assoc 9 32 k).symm
      _ = (8 * 36) * k := by rw [h9]
      _ = 8 * (36 * k) := Nat.mul_assoc 8 36 k
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) hmul

/-- **Exact next odd-plus-one.**  The landing of a remainder-`2` `(2, 1)`
step satisfies `e + 1 = 4(9k − 1)`. -/
theorem e_succ_of_k {n u e k : Nat}
    (h : IsExcursion n 2 u 1 e) (hk : n + 5 = 32 * k) (hpos : 0 < k) :
    e + 1 = 4 * (9 * k - 1) := by
  have he5 := e_plus_five_of_k h hk
  have h4 : 4 ≤ 36 * k := Nat.le_trans (by omega : 4 ≤ 36)
    (Nat.le_mul_of_pos_right 36 hpos)
  have hsplit : 36 * k - 4 = 4 * (9 * k - 1) := by omega
  omega

/-- The next cofactor equation, still an equality of naturals. -/
theorem next_v_identity {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (_hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e') :
    4 * (9 * k - 1) = 2 ^ v' * u' := by
  have hpos : 0 < k := by
    have : k % 2 = 1 := hodd
    omega
  have he1 := e_succ_of_k h hk hpos
  have hnu : e + 1 = 2 ^ v' * u' := hnext.2.2.2.2.2.1
  exact he1.symm.trans hnu

/-- Cancelling the factor `4` gives the odd part of `9k − 1`. -/
theorem nine_k_eq {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e') :
    9 * k - 1 = 2 ^ (v' - 2) * u' := by
  have hid := next_v_identity h hrem hodd hk hnext
  have hv : 2 ≤ v' := Nat.le_trans (by omega : 2 ≤ 3) (next_v_ge_three h hrem hnext)
  have hpow : (2 : Nat) ^ v' = 4 * 2 ^ (v' - 2) := by
    have hsum : (2 : Nat) ^ ((v' - 2) + 2) = 2 ^ (v' - 2) * 2 ^ 2 :=
      Nat.pow_add _ _ _
    rw [show v' - 2 + 2 = v' by omega] at hsum
    rw [show (2 : Nat) ^ 2 = 4 by decide, Nat.mul_comm] at hsum
    exact hsum
  rw [hpow, Nat.mul_assoc] at hid
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) hid

/-- **The next run length.**  `v' = 2 + v₂(9k − 1)`. -/
theorem val2_nine_k {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e') :
    Val2 (9 * k - 1) (v' - 2) := by
  have hid := nine_k_eq h hrem hodd hk hnext
  have hu : u' % 2 = 1 := hnext.2.1
  exact ⟨u', hu, hid⟩


/-! ## 4.  Exact identity for the next `(v', W')` -/

/-- **Peak identity of the next excursion, in `k`.**  The extra-halving
count `W'` is whatever makes

  `3^{v'} (9k − 1) = 2^{v'−2} (2^{W'} e' + 1)`

an equality of naturals.  No residue of `e` is enumerated. -/
theorem next_W_identity {n u e k v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hrem : Val2 (e + 5) 2)
    (hodd : k % 2 = 1) (hk : n + 5 = 32 * k)
    (hnext : IsExcursion e v' u' W' e') :
    3 ^ v' * (9 * k - 1) = 2 ^ (v' - 2) * (2 ^ W' * e' + 1) := by
  have hid := nine_k_eq h hrem hodd hk hnext
  have hpeak : 3 ^ v' * u' = 2 ^ W' * e' + 1 := hnext.2.2.2.2.2.2
  have hcomm : 3 ^ v' * (2 ^ (v' - 2) * u') =
      2 ^ (v' - 2) * (3 ^ v' * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hid, hcomm, hpeak]

/-- Two-step landing identity in the original start, for any next
excursion after a `(2, 1)` step (remainder `2` not required). -/
theorem two_step_identity {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (hnext : IsExcursion e v' u' W' e') :
    3 ^ v' * (9 * n + 13) = 2 ^ (v' + W' + 3) * e' + 2 ^ (v' + 3) := by
  have h8 := eight_succ h
  have hnu : e + 1 = 2 ^ v' * u' := hnext.2.2.2.2.2.1
  have hpeak : 3 ^ v' * u' = 2 ^ W' * e' + 1 := hnext.2.2.2.2.2.2
  have hmid : 3 ^ v' * (e + 1) = 2 ^ (v' + W') * e' + 2 ^ v' := by
    rw [hnu]
    have hcomm : 3 ^ v' * (2 ^ v' * u') = 2 ^ v' * (3 ^ v' * u') := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hcomm, hpeak, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_add]
  have hscale : 3 ^ v' * (9 * n + 13) = 8 * (3 ^ v' * (e + 1)) := by
    rw [← h8]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h8pow : (8 : Nat) = 2 ^ 3 := by decide
  rw [hscale, hmid, Nat.mul_add, h8pow]
  have hL : 2 ^ 3 * (2 ^ (v' + W') * e') = 2 ^ (v' + W' + 3) * e' := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm]
  have hR : 2 ^ 3 * 2 ^ v' = 2 ^ (v' + 3) := by
    rw [← Nat.pow_add, Nat.add_comm]
  rw [hL, hR]


/-! ## 5.  The next excursion does not drop below the original start -/

/-- The remainder-`2` seed: `27 → 31` with `v₂(31 + 5) = 2`. -/
theorem twenty_seven_rem_two :
    IsExcursion 27 2 7 1 31 ∧ Val2 (31 + 5) 2 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, ⟨9, rfl, rfl⟩⟩

/-- **Witness.**  The next excursion of `31` is `(v', W') = (5, 1)` and
lands at `121 > 27`.  A remainder-`2` `(2, 1)` step followed by its next
excursion is not a drop below the original start. -/
theorem twenty_seven_next_grows :
    IsExcursion 27 2 7 1 31 ∧
    Val2 (31 + 5) 2 ∧
    IsExcursion 31 5 1 1 121 ∧
    27 < 121 :=
  ⟨twenty_seven_rem_two.1, twenty_seven_rem_two.2,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- The identities on the witness: `k = 1`, `v' = 5`, `W' = 1`. -/
theorem twenty_seven_identities :
    27 + 5 = 32 * 1 ∧
    31 + 1 = 4 * (9 * 1 - 1) ∧
    3 ^ 5 * (9 * 1 - 1) = 2 ^ (5 - 2) * (2 ^ 1 * 121 + 1) := by
  decide

/-- **Negative theorem.**  The next excursion after remainder `2` is not
forced below the original `n`. -/
theorem next_not_force_drop :
    ¬ (∀ n u e v' u' W' e' : Nat,
        IsExcursion n 2 u 1 e →
        Val2 (e + 5) 2 →
        IsExcursion e v' u' W' e' →
        e' < n) := by
  intro hf
  have hlt :=
    hf 27 7 31 5 1 1 121
      twenty_seven_next_grows.1 twenty_seven_next_grows.2.1
      twenty_seven_next_grows.2.2.1
  omega

end ExcursionExit
end Collatz

section AxiomAudit
open Collatz.ExcursionExit
#print axioms eight_clock
#print axioms val2_plus_five_shift
#print axioms val2_n_plus_five
#print axioms e_seven_mod_eight
#print axioms next_v_ge_three
#print axioms e_succ_of_k
#print axioms next_v_identity
#print axioms nine_k_eq
#print axioms val2_nine_k
#print axioms next_W_identity
#print axioms two_step_identity
#print axioms twenty_seven_next_grows
#print axioms next_not_force_drop
end AxiomAudit
