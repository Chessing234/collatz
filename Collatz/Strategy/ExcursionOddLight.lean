import Collatz.Strategy.ExcursionLTE

/-!
# The odd-`v` light family `(v, W) = (3, 1)`

`ExcursionLTE` names the leftover light class: odd `v ≥ 3` with
`u ≡ 1 (mod 4)`, equivalently `W = 1`.  At `v = 3` this is
`n ≡ 7 (mod 32)`: `n = 8u − 1` and

  `e = (27u − 1) / 2 = (27n + 19) / 16`.

The `(2, 1)` light map has an integer clock `8(e + 5) = 9(n + 5)`, because
its fixed point is `−5`.  The `(3, 1)` map has fixed point `−19/11`, which
is not an integer.  There is therefore **no** `Nat` `c` with
`16(e + c) = 27(n + c)`.  The unique rational (and 2-adic: `11` is odd)
clock, written without denominators, is

  `16(11e + 19) = 27(11n + 19)`.

The landing residue is not uniformly `v = 1`: `u = 4k + 1` gives
`e = 54k + 13`, hence `e ≡ 1 (mod 4)` on even `k` and `e ≡ 3 (mod 4)` on
odd `k`.  Witness `39 → 67` (`67 ≡ 3 (mod 4)`).  So a two-step covering
via `drop_of_v_one` does not exist on this family.  Even the `v = 1`
landings need not drop below the start (`71 → 121 → 91`).
-/

namespace Collatz
namespace ExcursionOddLight

open Collatz.Arith Collatz.ExcursionMap Collatz.ExcursionLTE


/-! ## 1.  Unpacking a single `(3, 1)` excursion -/

/-- The defining equations at `(v, W) = (3, 1)`. -/
theorem eqs_of_v_three_W_one {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    n + 1 = 8 * u ∧ 27 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 3 = 8 by decide] at hnu
  rw [show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

/-- **Start in cofactor coordinates.**  `v = 3` is `n = 8u − 1`. -/
theorem n_eq_of_v_three_W_one {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    n = 8 * u - 1 := by
  have ⟨hnu, _⟩ := eqs_of_v_three_W_one h
  omega

/-- `W = 1` with odd `v` forces `u ≡ 1 (mod 4)`.  Dual of
`W_eq_one_of_odd_v_u_one_mod_four`. -/
theorem u_one_mod_four_of_v_three_W_one {n u e : Nat}
    (h : IsExcursion n 3 u 1 e) : u % 4 = 1 := by
  have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
  have he : e % 2 = 1 := h.2.2.1
  have : (27 * u) % 4 = 3 := by omega
  have : (27 : Nat) % 4 = 3 := by decide
  have hmul : (27 * u) % 4 = (3 * (u % 4)) % 4 := by
    rw [Nat.mul_mod, this]
  omega

/-- A single `(3, 1)` step is strictly expanding. -/
theorem v_three_W_one_grows {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    n < e := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_three_W_one h
  omega


/-! ## 2.  Exact one-step landing -/

/-- **The one-step light map in the cofactor.**  For `n = 8u − 1` with
`(v, W) = (3, 1)`, the landing is `(27u − 1) / 2`. -/
theorem landing_u_of_v_three_W_one {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    e = (27 * u - 1) / 2 := by
  have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
  have hsub : 27 * u - 1 = 2 * e := by omega
  rw [hsub]
  exact (Nat.mul_div_cancel_left e (by omega : 0 < 2)).symm

/-- **The one-step light map in `n`.**  Affine form `(27/16) n + 19/16`. -/
theorem landing_n_of_v_three_W_one {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    e = (27 * n + 19) / 16 := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_three_W_one h
  have h16 : 16 * e = 27 * n + 19 := by omega
  have : 27 * n + 19 = 16 * e := h16.symm
  rw [this]
  exact (Nat.mul_div_cancel_left e (by omega : 0 < 16)).symm


/-! ## 3.  No integer clock; the unique 2-adic clock, written integrally -/

/-- Any putative integer clock `16(e + c) = 27(n + c)` forces `11c = 19`. -/
theorem clock_forces_eleven_c {n u e c : Nat} (h : IsExcursion n 3 u 1 e)
    (heq : 16 * (e + c) = 27 * (n + c)) : 11 * c = 19 := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_three_W_one h
  omega

/-- **Negative theorem.**  There is no `Nat` `c > 0` with
`16(e + c) = 27(n + c)` on a `(3, 1)` excursion.  The obstruction is
`11c = 19` (which also rules out `c = 0`). -/
theorem no_nat_clock {n u e c : Nat} (h : IsExcursion n 3 u 1 e)
    (_hc : 0 < c) : 16 * (e + c) ≠ 27 * (n + c) := by
  intro heq
  have := clock_forces_eleven_c h heq
  omega

/-- `7 ↦ 13` is a `(3, 1)` excursion. -/
theorem seven_is_v_three_W_one : IsExcursion 7 3 1 1 13 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

/-- The same obstruction at the Mersenne seed `7 ↦ 13`. -/
theorem seven_no_clock {c : Nat} (hc : 0 < c) :
    16 * (13 + c) ≠ 27 * (7 + c) :=
  no_nat_clock seven_is_v_three_W_one hc

/-- **The unique rational / 2-adic clock**, cleared of the denominator `11`.
This is `16(e + 19/11) = 27(n + 19/11)`, not an integer-`c` identity. -/
theorem two_adic_clock {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    16 * (11 * e + 19) = 27 * (11 * n + 19) := by
  have ⟨hnu, hpeak⟩ := eqs_of_v_three_W_one h
  omega


/-! ## 4.  Landing residue: `e = 54k + 13`, not always `v = 1` -/

/-- Every `(3, 1)` cofactor is `u = 4k + 1`. -/
theorem exists_k_of_v_three_W_one {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    ∃ k : Nat, u = 4 * k + 1 := by
  have hu4 := u_one_mod_four_of_v_three_W_one h
  exact ⟨u / 4, (Nat.div_add_mod u 4).symm.trans (by rw [hu4])⟩

/-- **Exact next residue.**  On `u = 4k + 1` the landing is `54k + 13`. -/
theorem landing_of_u_one_mod_four {n k e : Nat}
    (h : IsExcursion n 3 (4 * k + 1) 1 e) : e = 54 * k + 13 := by
  have ⟨_, hpeak⟩ := eqs_of_v_three_W_one h
  omega

/-- The landing is `≡ 1 (mod 4)` on even `k` and `≡ 3 (mod 4)` on odd `k`. -/
theorem landing_mod_four {n k e : Nat}
    (h : IsExcursion n 3 (4 * k + 1) 1 e) :
    e % 4 = 2 * (k % 2) + 1 := by
  have he := landing_of_u_one_mod_four h
  omega

/-- `39 → 67` with `u = 5 ≡ 1 (mod 4)` and `67 ≡ 3 (mod 4)`.  The landing
is not `v = 1`, so `drop_of_v_one` is not a two-step covering of `(3, 1)`. -/
theorem thirty_nine_not_v_one :
    IsExcursion 39 3 5 1 67 ∧ 5 % 4 = 1 ∧ 67 % 4 = 3 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, rfl, rfl⟩

/-- Contrast: `71 → 121` *does* land on `v = 1` (`121 ≡ 1 (mod 4)`), because
`u = 9 ≡ 1 (mod 8)` is the even-`k` half.  The wrong witness for
“not always `v = 1`”. -/
theorem seventy_one_lands_v_one :
    IsExcursion 71 3 9 1 121 ∧ 9 % 8 = 1 ∧ 121 % 4 = 1 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, rfl, rfl⟩

/-- Even a `v = 1` landing need not drop below the start:
`71 → 121 → 91` with `91 > 71`. -/
theorem seventy_one_two_step_grows :
    IsExcursion 71 3 9 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧
    71 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega⟩

/-- Sanity: the closed form on the two witnesses. -/
theorem landing_closed_form_on_witnesses :
    (27 * 39 + 19) / 16 = 67 ∧ (27 * 71 + 19) / 16 = 121 := by
  decide

end ExcursionOddLight
end Collatz

section AxiomAudit
open Collatz.ExcursionOddLight
#print axioms landing_u_of_v_three_W_one
#print axioms landing_n_of_v_three_W_one
#print axioms no_nat_clock
#print axioms seven_no_clock
#print axioms two_adic_clock
#print axioms landing_of_u_one_mod_four
#print axioms thirty_nine_not_v_one
#print axioms seventy_one_two_step_grows
end AxiomAudit
