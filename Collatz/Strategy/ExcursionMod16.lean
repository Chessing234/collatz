import Collatz.Strategy.ExcursionSevenMod32

/-!
# Round XVI — Lemma X on `n ≡ 15 (mod 16)` except `n ≡ 15 (mod 128)`

`ExcursionMod8` closed `n ≡ 15 (mod 128)` by a one-step heavy `v = 4` drop
(`W ≥ 3`).  The rest of `n ≡ 15 (mod 16)` is `31, 47, 63, 79, 95, 111, 127
(mod 128)`, together with the `v = 4` class `n ≡ 15 (mod 32)` that is not
`15 (mod 128)`.

This is **not** a short uniform law on the whole family.  `31` survives three
excursions (`31 → 121 → 91 → 103`); `47` and `63` have no first drop.  The
class `15 (mod 64)` is not a one-step family (`79` has `v = 4`, `W = 2`),
and `79 (mod 128)` is not a two-step family (`207` is light on the second
landing).

What *does* drop, on infinite arithmetic progressions:

* `n ≡ 95 (mod 256)` — `v = 5`, `W ≥ 3`, one excursion.
* `n ≡ 575 (mod 1024)` — `v = 6`, `W ≥ 4`, one excursion.
* `n ≡ 79 (mod 256)` — `v = 4`, `W = 2`, then a `v = 1` landing below start.
* `n ≡ 175 (mod 256)` — `v = 4`, `W = 1`, landing `≡ 5 (mod 8)`, then `v = 1`.
* `n ≡ 287 (mod 1024)` — `v = 5`, `W = 1`, landing `≡ 5 (mod 16)`, then `v = 1`.
  This is a subclass of `31 (mod 256)`; `31` itself is the obstruction.
* `n ≡ 735 (mod 1024)` — `v = 5`, `W = 2`, landing `≡ 5 (mod 8)`, then `v = 1`.
* `n ≡ 367 (mod 1024)` — `v = 4`, `W = 1`, landing `≡ 3 (mod 32)`, then heavy
  `v = 2`.
* `n ≡ 975 (mod 1024)` — `v = 4`, `W = 2`, landing `≡ 3 (mod 16)`, then heavy
  `v = 2`.
-/

namespace Collatz
namespace ExcursionMod16

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionMod8 Collatz.NeverDrops


/-! ## 1.  Valuation from residue -/

/-- `v = 5` is the residue `31 mod 64`. -/
theorem v_eq_five_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 5 ↔ n % 64 = 31 := by
  constructor
  · intro hv
    obtain ⟨_, hu, _, _, _, hnu, _⟩ := h
    rw [hv] at hnu
    have h32 : (2 : Nat) ^ 5 = 32 := by decide
    rw [h32] at hnu
    have : (n + 1) % 64 = 32 := by
      have : (32 * u) % 64 = 32 := by omega
      omega
    omega
  · intro h64
    have hval : Val2 (n + 1) 5 := by
      refine Val2.of_mod ?_
      have hpow : (2 : Nat) ^ (5 + 1) = 64 := by decide
      rw [hpow]
      have hadd : (n + 1) % 64 = (n % 64 + 1) % 64 := Nat.add_mod n 1 64
      rw [hadd, h64]
    exact Val2.unique (val2_succ_of h) hval

/-- `v = 6` is the residue `63 mod 128`. -/
theorem v_eq_six_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 6 ↔ n % 128 = 63 := by
  constructor
  · intro hv
    obtain ⟨_, hu, _, _, _, hnu, _⟩ := h
    rw [hv] at hnu
    have h64 : (2 : Nat) ^ 6 = 64 := by decide
    rw [h64] at hnu
    have : (n + 1) % 128 = 64 := by
      have : (64 * u) % 128 = 64 := by omega
      omega
    omega
  · intro h128
    have hval : Val2 (n + 1) 6 := by
      refine Val2.of_mod ?_
      have hpow : (2 : Nat) ^ (6 + 1) = 128 := by decide
      rw [hpow]
      have hadd : (n + 1) % 128 = (n % 128 + 1) % 128 := Nat.add_mod n 1 128
      rw [hadd, h128]
    exact Val2.unique (val2_succ_of h) hval


/-! ## 2.  Extra halvings from a finer residue -/

private theorem sixteen_mul_mod_256 (u : Nat) : (16 * u) % 256 = 16 * (u % 16) := by
  have hdecomp : u = 16 * (u / 16) + u % 16 := (Nat.div_add_mod u 16).symm
  have hex : 16 * u = 256 * (u / 16) + 16 * (u % 16) := by omega
  have hlt : 16 * (u % 16) < 256 := by
    have : u % 16 < 16 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem thirty_two_mul_mod_256 (u : Nat) : (32 * u) % 256 = 32 * (u % 8) := by
  have hdecomp : u = 8 * (u / 8) + u % 8 := (Nat.div_add_mod u 8).symm
  have hex : 32 * u = 256 * (u / 8) + 32 * (u % 8) := by omega
  have hlt : 32 * (u % 8) < 256 := by
    have : u % 8 < 8 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem thirty_two_mul_mod_1024 (u : Nat) :
    (32 * u) % 1024 = 32 * (u % 32) := by
  have hdecomp : u = 32 * (u / 32) + u % 32 := (Nat.div_add_mod u 32).symm
  have hex : 32 * u = 1024 * (u / 32) + 32 * (u % 32) := by omega
  have hlt : 32 * (u % 32) < 1024 := by
    have : u % 32 < 32 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem sixty_four_mul_mod_1024 (u : Nat) :
    (64 * u) % 1024 = 64 * (u % 16) := by
  have hdecomp : u = 16 * (u / 16) + u % 16 := (Nat.div_add_mod u 16).symm
  have hex : 64 * u = 1024 * (u / 16) + 64 * (u % 16) := by omega
  have hlt : 64 * (u % 16) < 1024 := by
    have : u % 16 < 16 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem eight_mul_mod_128 (u : Nat) : (16 * u) % 128 = 16 * (u % 8) := by
  have hdecomp : u = 8 * (u / 8) + u % 8 := (Nat.div_add_mod u 8).symm
  have hex : 16 * u = 128 * (u / 8) + 16 * (u % 8) := by omega
  have hlt : 16 * (u % 8) < 128 := by
    have : u % 8 < 8 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- On `n ≡ 5 (mod 16)` the first excursion has `v = 1` and `W ≥ 3`. -/
theorem W_ge_three_of_five_mod_sixteen {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h16 : n % 16 = 5) : 3 ≤ W := by
  have hv : v = 1 := (v_eq_one_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv, Nat.pow_one] at hnu
  have hu8 : u % 8 = 3 := by omega
  have h8dvd : (2 : Nat) ^ 3 ∣ 3 ^ v * u - 1 := by
    rw [hv, Nat.pow_one]
    have : (3 * u - 1) % 8 = 0 := by
      have hmul : (3 * u) % 8 = 1 := by
        rw [Nat.mul_mod, hu8]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h8dvd

/-- On `n ≡ 3 (mod 32)` the first excursion has `v = 2` and `W ≥ 3`. -/
theorem W_ge_three_of_three_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 3) : 3 ≤ W := by
  have hv : v = 2 := (v_eq_two_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  rw [h4] at hnu
  have hu8 : u % 8 = 1 := by omega
  have h8dvd : (2 : Nat) ^ 3 ∣ 3 ^ v * u - 1 := by
    rw [hv, show (3 : Nat) ^ 2 = 9 by decide]
    have : (9 * u - 1) % 8 = 0 := by
      have hmul : (9 * u) % 8 = 1 := by
        rw [Nat.mul_mod, hu8]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h8dvd

/-- On `n ≡ 47 (mod 64)` the first excursion has `v = 4` and `W = 1`. -/
theorem W_eq_one_of_forty_seven_mod_sixty_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h64 : n % 64 = 47) : W = 1 := by
  have hv : v = 4 := (v_eq_four_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h16 : (2 : Nat) ^ 4 = 16 := by decide
  rw [h16] at hnu
  have hu4 : u % 4 = 3 := by omega
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  rw [h81] at hpeakVal
  have hpeak4 : (81 * u - 1) % 4 = 2 := by
    have hmul : (81 * u) % 4 = 3 := by
      have : 81 % 4 = 1 := by decide
      rw [Nat.mul_mod, this, hu4]
    omega
  have hval : Val2 (81 * u - 1) 1 := Val2.one_iff.mpr hpeak4
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 79 (mod 128)` the first excursion has `v = 4` and `W = 2`. -/
theorem W_eq_two_of_seventy_nine_mod_one_twenty_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h128 : n % 128 = 79) : W = 2 := by
  have hv : v = 4 := (v_eq_four_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h16 : (2 : Nat) ^ 4 = 16 := by decide
  rw [h16] at hnu
  have hu8 : u % 8 = 5 := by
    have : (16 * u) % 128 = 80 := by omega
    have := eight_mul_mod_128 u
    omega
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  rw [h81] at hpeakVal
  have hpeak8 : (81 * u - 1) % 8 = 4 := by
    have hmul : (81 * u) % 8 = 5 := by
      have : 81 % 8 = 1 := by decide
      rw [Nat.mul_mod, this, hu8]
    omega
  have hval : Val2 (81 * u - 1) 2 := Val2.two_iff.mpr hpeak8
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 31 (mod 128)` the first excursion has `v = 5` and `W = 1`. -/
theorem W_eq_one_of_thirty_one_mod_one_twenty_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h128 : n % 128 = 31) : W = 1 := by
  have hv : v = 5 := (v_eq_five_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h32 : (2 : Nat) ^ 5 = 32 := by decide
  rw [h32] at hnu
  have hu4 : u % 4 = 1 := by omega
  have h243 : (3 : Nat) ^ 5 = 243 := by decide
  rw [h243] at hpeakVal
  have hpeak4 : (243 * u - 1) % 4 = 2 := by
    have hmul : (243 * u) % 4 = 3 := by
      have : 243 % 4 = 3 := by decide
      rw [Nat.mul_mod, this, hu4]
    omega
  have hval : Val2 (243 * u - 1) 1 := Val2.one_iff.mpr hpeak4
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 95 (mod 256)` the first excursion has `v = 5` and `W ≥ 3`. -/
theorem W_ge_three_of_ninety_five_mod_two_fifty_six {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h256 : n % 256 = 95) : 3 ≤ W := by
  have hv : v = 5 := (v_eq_five_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu
  have h32 : (2 : Nat) ^ 5 = 32 := by decide
  rw [h32] at hnu
  have h243 : (3 : Nat) ^ 5 = 243 := by decide
  have h8dvd : (2 : Nat) ^ 3 ∣ 3 ^ v * u - 1 := by
    rw [hv, h243]
    have : (243 * u - 1) % 8 = 0 := by
      have hu8 : u % 8 = 3 := by
        have : (32 * u) % 256 = 96 := by omega
        have := thirty_two_mul_mod_256 u
        omega
      have hmul : (243 * u) % 8 = 1 := by
        have : 243 % 8 = 3 := by decide
        rw [Nat.mul_mod, this, hu8]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h8dvd

/-- On `n ≡ 575 (mod 1024)` the first excursion has `v = 6` and `W ≥ 4`. -/
theorem W_ge_four_of_five_seventy_five_mod_1024 {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h1024 : n % 1024 = 575) : 4 ≤ W := by
  have hv : v = 6 := (v_eq_six_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu
  have h64 : (2 : Nat) ^ 6 = 64 := by decide
  rw [h64] at hnu
  have h729 : (3 : Nat) ^ 6 = 729 := by decide
  have h16dvd : (2 : Nat) ^ 4 ∣ 3 ^ v * u - 1 := by
    rw [hv, h729]
    have : (729 * u - 1) % 16 = 0 := by
      have hu16 : u % 16 = 9 := by
        have : (64 * u) % 1024 = 576 := by omega
        have := sixty_four_mul_mod_1024 u
        omega
      have hmul : (729 * u) % 16 = 1 := by
        have : 729 % 16 = 9 := by decide
        rw [Nat.mul_mod, this, hu16]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h16dvd

/-- On `n ≡ 287 (mod 1024)` the first excursion has `v = 5` and `W = 1`. -/
theorem W_eq_one_of_two_eighty_seven_mod_1024 {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h1024 : n % 1024 = 287) : W = 1 := by
  have hv : v = 5 := (v_eq_five_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h32 : (2 : Nat) ^ 5 = 32 := by decide
  rw [h32] at hnu
  have hu4 : u % 4 = 1 := by
    have : (32 * u) % 1024 = 288 := by omega
    have := thirty_two_mul_mod_1024 u
    omega
  have h243 : (3 : Nat) ^ 5 = 243 := by decide
  rw [h243] at hpeakVal
  have hpeak4 : (243 * u - 1) % 4 = 2 := by
    have hmul : (243 * u) % 4 = 3 := by
      have : 243 % 4 = 3 := by decide
      rw [Nat.mul_mod, this, hu4]
    omega
  have hval : Val2 (243 * u - 1) 1 := Val2.one_iff.mpr hpeak4
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 735 (mod 1024)` the first excursion has `v = 5` and `W = 2`. -/
theorem W_eq_two_of_seven_thirty_five_mod_1024 {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h1024 : n % 1024 = 735) : W = 2 := by
  have hv : v = 5 := (v_eq_five_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h32 : (2 : Nat) ^ 5 = 32 := by decide
  rw [h32] at hnu
  have hu8 : u % 8 = 7 := by
    have : (32 * u) % 1024 = 736 := by omega
    have := thirty_two_mul_mod_1024 u
    omega
  have h243 : (3 : Nat) ^ 5 = 243 := by decide
  rw [h243] at hpeakVal
  have hpeak8 : (243 * u - 1) % 8 = 4 := by
    have hmul : (243 * u) % 8 = 5 := by
      have : 243 % 8 = 3 := by decide
      rw [Nat.mul_mod, this, hu8]
    omega
  have hval : Val2 (243 * u - 1) 2 := Val2.two_iff.mpr hpeak8
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 367 (mod 1024)` the first excursion has `v = 4` and `W = 1`. -/
theorem W_eq_one_of_three_sixty_seven_mod_1024 {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h1024 : n % 1024 = 367) : W = 1 := by
  have hv : v = 4 := (v_eq_four_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h16 : (2 : Nat) ^ 4 = 16 := by decide
  rw [h16] at hnu
  have hu4 : u % 4 = 3 := by
    have : (16 * u) % 256 = 112 := by
      have : n % 256 = 111 := by omega
      omega
    have := sixteen_mul_mod_256 u
    omega
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  rw [h81] at hpeakVal
  have hpeak4 : (81 * u - 1) % 4 = 2 := by
    have hmul : (81 * u) % 4 = 3 := by
      have : 81 % 4 = 1 := by decide
      rw [Nat.mul_mod, this, hu4]
    omega
  have hval : Val2 (81 * u - 1) 1 := Val2.one_iff.mpr hpeak4
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 975 (mod 1024)` the first excursion has `v = 4` and `W = 2`. -/
theorem W_eq_two_of_nine_seventy_five_mod_1024 {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h1024 : n % 1024 = 975) : W = 2 := by
  have hv : v = 4 := (v_eq_four_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h16 : (2 : Nat) ^ 4 = 16 := by decide
  rw [h16] at hnu
  have hu8 : u % 8 = 5 := by
    have : n % 128 = 79 := by omega
    have : (16 * u) % 128 = 80 := by omega
    have := eight_mul_mod_128 u
    omega
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  rw [h81] at hpeakVal
  have hpeak8 : (81 * u - 1) % 8 = 4 := by
    have hmul : (81 * u) % 8 = 5 := by
      have : 81 % 8 = 1 := by decide
      rw [Nat.mul_mod, this, hu8]
    omega
  have hval : Val2 (81 * u - 1) 2 := Val2.two_iff.mpr hpeak8
  exact Val2.unique hpeakVal hval


/-! ## 3.  Drop inequalities at `v = 5` and `v = 6` -/

private theorem eight_le_two_pow {W : Nat} (hW : 3 ≤ W) : 8 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 3 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

private theorem four_le_two_pow {W : Nat} (hW : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

private theorem sixteen_le_two_pow {W : Nat} (hW : 4 ≤ W) : 16 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 4 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

/-- `(2c) k + 2d = 2 (c k + d)`. -/
private theorem two_mul_linear (c d k : Nat) :
    (2 * c) * k + 2 * d = 2 * (c * k + d) := by
  rw [Nat.mul_assoc, Nat.mul_add]

/-- `(4c) k + 4d = 4 (c k + d)`. -/
private theorem four_mul_linear (c d k : Nat) :
    (4 * c) * k + 4 * d = 4 * (c * k + d) := by
  rw [Nat.mul_assoc, Nat.mul_add]

/-- `243 u + 2^W ≤ 32 · 2^W · u` for `W ≥ 3`. -/
private theorem v_five_drop_ineq {u W : Nat} (hu : 1 ≤ u) (hW : 3 ≤ W) :
    243 * u + 2 ^ W ≤ 32 * 2 ^ W * u := by
  have h8 := eight_le_two_pow hW
  have h243 : 243 ≤ 31 * 2 ^ W := by
    have : 31 * 8 ≤ 31 * 2 ^ W := Nat.mul_le_mul_left 31 h8
    omega
  have hsum : 243 + 2 ^ W ≤ 32 * 2 ^ W := by omega
  have hB : 2 ^ W ≤ 2 ^ W * u := Nat.le_mul_of_pos_right (2 ^ W) hu
  calc 243 * u + 2 ^ W
      ≤ 243 * u + 2 ^ W * u := Nat.add_le_add_left hB _
    _ = (243 + 2 ^ W) * u := (Nat.add_mul 243 (2 ^ W) u).symm
    _ ≤ (32 * 2 ^ W) * u := Nat.mul_le_mul_right u hsum
    _ = 32 * 2 ^ W * u := by simp [Nat.mul_assoc]

/-- `729 u + 2^W ≤ 64 · 2^W · u` for `W ≥ 4`. -/
private theorem v_six_drop_ineq {u W : Nat} (hu : 1 ≤ u) (hW : 4 ≤ W) :
    729 * u + 2 ^ W ≤ 64 * 2 ^ W * u := by
  have h16 := sixteen_le_two_pow hW
  have h729 : 729 ≤ 63 * 2 ^ W := by
    have : 63 * 16 ≤ 63 * 2 ^ W := Nat.mul_le_mul_left 63 h16
    omega
  have hsum : 729 + 2 ^ W ≤ 64 * 2 ^ W := by omega
  have hB : 2 ^ W ≤ 2 ^ W * u := Nat.le_mul_of_pos_right (2 ^ W) hu
  calc 729 * u + 2 ^ W
      ≤ 729 * u + 2 ^ W * u := Nat.add_le_add_left hB _
    _ = (729 + 2 ^ W) * u := (Nat.add_mul 729 (2 ^ W) u).symm
    _ ≤ (64 * 2 ^ W) * u := Nat.mul_le_mul_right u hsum
    _ = 64 * 2 ^ W * u := by simp [Nat.mul_assoc]

/-- **Heavy `v = 5` drops.**  Three extra halvings beat `3^5 = 243`. -/
theorem drop_of_v_five_heavy {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 5) (hW : 3 ≤ W) : e < n := by
  subst hv
  refine (drop_iff h).mpr ?_
  have h243 : (3 : Nat) ^ 5 = 243 := by decide
  have hpow : (2 : Nat) ^ (5 + W) = 32 * 2 ^ W := by rw [Nat.pow_add]
  rw [h243, hpow]
  have hu : 1 ≤ u := by
    have := h.2.1
    omega
  exact v_five_drop_ineq hu hW

/-- **Heavy `v = 6` drops.**  Four extra halvings beat `3^6 = 729`. -/
theorem drop_of_v_six_heavy {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 6) (hW : 4 ≤ W) : e < n := by
  subst hv
  refine (drop_iff h).mpr ?_
  have h729 : (3 : Nat) ^ 6 = 729 := by decide
  have hpow : (2 : Nat) ^ (6 + W) = 64 * 2 ^ W := by rw [Nat.pow_add]
  rw [h729, hpow]
  have hu : 1 ≤ u := by
    have := h.2.1
    omega
  exact v_six_drop_ineq hu hW


/-! ## 4.  One-step drops -/

/-- **Every `n ≡ 95 (mod 256)` drops in one excursion.** -/
theorem drop_of_ninety_five_mod_two_fifty_six {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h256 : n % 256 = 95) : e < n :=
  drop_of_v_five_heavy h ((v_eq_five_iff h).mpr (by omega))
    (W_ge_three_of_ninety_five_mod_two_fifty_six h h256)

/-- **Every `n ≡ 575 (mod 1024)` drops in one excursion.** -/
theorem drop_of_five_seventy_five_mod_1024 {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h1024 : n % 1024 = 575) : e < n :=
  drop_of_v_six_heavy h ((v_eq_six_iff h).mpr (by omega))
    (W_ge_four_of_five_seventy_five_mod_1024 h h1024)

theorem lemmaX_of_ninety_five_mod_two_fifty_six {n : Nat}
    (_hn : 1 < n) (hmod : n % 256 = 95) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  exact ⟨e, ExChain.one ⟨v, u, W, h⟩, drop_of_ninety_five_mod_two_fifty_six h hmod⟩

theorem lemmaX_of_five_seventy_five_mod_1024 {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 575) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  exact ⟨e, ExChain.one ⟨v, u, W, h⟩, drop_of_five_seventy_five_mod_1024 h hmod⟩


/-! ## 5.  Two-step drops with a `v = 1` second excursion -/

/-- **Every `n ≡ 79 (mod 256)` drops in two excursions.** -/
theorem lemmaX_of_seventy_nine_mod_two_fifty_six {n : Nat}
    (_hn : 1 < n) (hmod : n % 256 = 79) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 4 := (v_eq_four_iff hex).mpr (by omega)
  have hW : W = 2 := W_eq_two_of_seventy_nine_mod_one_twenty_eight hex (by omega)
  have hk : n = 256 * (n / 256) + 79 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 16 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 4 = 16 by decide] at this
    exact this
  have hpeak : 81 * u = 4 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 4 = 81 by decide] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 16 * k + 5 := by
    have : 16 * u = 256 * k + 80 := by omega
    have : 16 * u = 16 * (16 * k + 5) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 16) this
  have he : e = 324 * k + 101 := by
    have : 81 * u = 4 * e + 1 := hpeak
    rw [hu] at this
    have : 4 * e = 4 * (324 * k + 101) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he4 : e % 4 = 1 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 1 := (v_eq_one_iff hex2).mpr he4
  have hW2 : 1 ≤ W2 := IsExcursion.one_le_W hex2
  have hnu2 : e + 1 = 2 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, Nat.pow_one] at this
    exact this
  have hpeak2 : 3 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 162 * k + 51 := by
    have : 2 * u2 = 324 * k + 102 := by omega
    have : 2 * u2 = 2 * (162 * k + 51) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have h2 : 2 ≤ 2 ^ W2 := two_le_two_pow (by omega)
  have hle : 2 * e2 ≤ 3 * u2 - 1 := by
    have hmul : 2 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h2
    have : 2 ^ W2 * e2 = 3 * u2 - 1 := by omega
    omega
  have hnum : 3 * u2 - 1 = 2 * (243 * k + 76) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 2 * e2 ≤ 2 * (243 * k + 76) := by omega
    have : e2 ≤ 243 * k + 76 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩

/-- **Every `n ≡ 175 (mod 256)` drops in two excursions.** -/
theorem lemmaX_of_one_seventy_five_mod_two_fifty_six {n : Nat}
    (_hn : 1 < n) (hmod : n % 256 = 175) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 4 := (v_eq_four_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_forty_seven_mod_sixty_four hex (by omega)
  have hk : n = 256 * (n / 256) + 175 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 16 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 4 = 16 by decide] at this
    exact this
  have hpeak : 81 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 4 = 81 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 16 * k + 11 := by
    have : 16 * u = 256 * k + 176 := by omega
    have : 16 * u = 16 * (16 * k + 11) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 16) this
  have he : e = 648 * k + 445 := by
    have : 81 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (648 * k + 445) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he8 : e % 8 = 5 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 1 := (v_eq_one_iff hex2).mpr (by omega)
  have hW2 : 2 ≤ W2 := W_ge_two_of_five_mod_eight hex2 he8
  have hnu2 : e + 1 = 2 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, Nat.pow_one] at this
    exact this
  have hpeak2 : 3 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 324 * k + 223 := by
    have : 2 * u2 = 648 * k + 446 := by omega
    have : 2 * u2 = 2 * (324 * k + 223) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have h4 := four_le_two_pow hW2
  have hle : 4 * e2 ≤ 3 * u2 - 1 := by
    have hmul : 4 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h4
    have : 2 ^ W2 * e2 = 3 * u2 - 1 := by omega
    omega
  have hnum : 3 * u2 - 1 = 4 * (243 * k + 167) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 4 * e2 ≤ 4 * (243 * k + 167) := by omega
    have : e2 ≤ 243 * k + 167 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩

/-- **Every `n ≡ 287 (mod 1024)` drops in two excursions.**  This is a
subclass of `31 (mod 256)`.  The residue `31` itself is *not* of this shape
and survives three excursions. -/
theorem lemmaX_of_two_eighty_seven_mod_1024 {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 287) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 5 := (v_eq_five_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_two_eighty_seven_mod_1024 hex hmod
  have hk : n = 1024 * (n / 1024) + 287 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 32 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 5 = 32 by decide] at this
    exact this
  have hpeak : 243 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 5 = 243 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 32 * k + 9 := by
    have : 32 * u = 1024 * k + 288 := by omega
    have : 32 * u = 32 * (32 * k + 9) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 32) this
  have he : e = 3888 * k + 1093 := by
    have : 243 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (3888 * k + 1093) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he16 : e % 16 = 5 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 1 := (v_eq_one_iff hex2).mpr (by omega)
  have hW2 : 3 ≤ W2 := W_ge_three_of_five_mod_sixteen hex2 he16
  have hnu2 : e + 1 = 2 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, Nat.pow_one] at this
    exact this
  have hpeak2 : 3 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 1944 * k + 547 := by
    have hsum : 2 * u2 = 3888 * k + 1094 := by omega
    have hsplit : 3888 * k + 1094 = 2 * (1944 * k + 547) := by
      have hc : (3888 : Nat) = 2 * 1944 := by decide
      have hd : (1094 : Nat) = 2 * 547 := by decide
      rw [hc, hd]
      exact two_mul_linear 1944 547 k
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) (hsum.trans hsplit)
  have h8 := eight_le_two_pow hW2
  have hle : 8 * e2 ≤ 3 * u2 - 1 := by
    have hmul : 8 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h8
    have : 2 ^ W2 * e2 = 3 * u2 - 1 := by omega
    omega
  have hnum : 3 * u2 - 1 = 8 * (729 * k + 205) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 8 * e2 ≤ 8 * (729 * k + 205) := by omega
    have : e2 ≤ 729 * k + 205 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩

/-- **Every `n ≡ 735 (mod 1024)` drops in two excursions.** -/
theorem lemmaX_of_seven_thirty_five_mod_1024 {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 735) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 5 := (v_eq_five_iff hex).mpr (by omega)
  have hW : W = 2 := W_eq_two_of_seven_thirty_five_mod_1024 hex hmod
  have hk : n = 1024 * (n / 1024) + 735 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 32 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 5 = 32 by decide] at this
    exact this
  have hpeak : 243 * u = 4 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 5 = 243 by decide] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 32 * k + 23 := by
    have : 32 * u = 1024 * k + 736 := by omega
    have : 32 * u = 32 * (32 * k + 23) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 32) this
  have he : e = 1944 * k + 1397 := by
    have : 243 * u = 4 * e + 1 := hpeak
    rw [hu] at this
    have : 4 * e = 4 * (1944 * k + 1397) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he8 : e % 8 = 5 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 1 := (v_eq_one_iff hex2).mpr (by omega)
  have hW2 : 2 ≤ W2 := W_ge_two_of_five_mod_eight hex2 he8
  have hnu2 : e + 1 = 2 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, Nat.pow_one] at this
    exact this
  have hpeak2 : 3 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 972 * k + 699 := by
    have hsum : 2 * u2 = 1944 * k + 1398 := by omega
    have hsplit : 1944 * k + 1398 = 2 * (972 * k + 699) := by
      have hc : (1944 : Nat) = 2 * 972 := by decide
      have hd : (1398 : Nat) = 2 * 699 := by decide
      rw [hc, hd]
      exact two_mul_linear 972 699 k
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) (hsum.trans hsplit)
  have h4 := four_le_two_pow hW2
  have hle : 4 * e2 ≤ 3 * u2 - 1 := by
    have hmul : 4 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h4
    have : 2 ^ W2 * e2 = 3 * u2 - 1 := by omega
    omega
  have hnum : 3 * u2 - 1 = 4 * (729 * k + 524) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 4 * e2 ≤ 4 * (729 * k + 524) := by omega
    have : e2 ≤ 729 * k + 524 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩


/-! ## 6.  Two-step drops with a heavy `v = 2` second excursion -/

/-- **Every `n ≡ 367 (mod 1024)` drops in two excursions.** -/
theorem lemmaX_of_three_sixty_seven_mod_1024 {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 367) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 4 := (v_eq_four_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_three_sixty_seven_mod_1024 hex hmod
  have hk : n = 1024 * (n / 1024) + 367 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 16 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 4 = 16 by decide] at this
    exact this
  have hpeak : 81 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 4 = 81 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 64 * k + 23 := by
    have : 16 * u = 1024 * k + 368 := by omega
    have : 16 * u = 16 * (64 * k + 23) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 16) this
  have he : e = 2592 * k + 931 := by
    have : 81 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (2592 * k + 931) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he32 : e % 32 = 3 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 2 := (v_eq_two_iff hex2).mpr (by omega)
  have hW2 : 3 ≤ W2 := W_ge_three_of_three_mod_thirty_two hex2 he32
  have hnu2 : e + 1 = 4 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak2 : 9 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have hu2 : u2 = 648 * k + 233 := by
    have : 4 * u2 = 2592 * k + 932 := by omega
    have : 4 * u2 = 4 * (648 * k + 233) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have h8 := eight_le_two_pow hW2
  have hle : 8 * e2 ≤ 9 * u2 - 1 := by
    have hmul : 8 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h8
    have : 2 ^ W2 * e2 = 9 * u2 - 1 := by omega
    omega
  have hnum : 9 * u2 - 1 = 8 * (729 * k + 262) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 8 * e2 ≤ 8 * (729 * k + 262) := by omega
    have : e2 ≤ 729 * k + 262 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩

/-- **Every `n ≡ 975 (mod 1024)` drops in two excursions.** -/
theorem lemmaX_of_nine_seventy_five_mod_1024 {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 975) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 4 := (v_eq_four_iff hex).mpr (by omega)
  have hW : W = 2 := W_eq_two_of_nine_seventy_five_mod_1024 hex hmod
  have hk : n = 1024 * (n / 1024) + 975 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 16 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 4 = 16 by decide] at this
    exact this
  have hpeak : 81 * u = 4 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 4 = 81 by decide] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 64 * k + 61 := by
    have : 16 * u = 1024 * k + 976 := by omega
    have : 16 * u = 16 * (64 * k + 61) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 16) this
  have he : e = 1296 * k + 1235 := by
    have : 81 * u = 4 * e + 1 := hpeak
    rw [hu] at this
    have : 4 * e = 4 * (1296 * k + 1235) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he16 : e % 16 = 3 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 2 := (v_eq_two_iff hex2).mpr (by omega)
  have hW2 : 2 ≤ W2 := ((v_two_W_ge_two_iff hex2).mpr he16).2
  have hnu2 : e + 1 = 4 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak2 : 9 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have hu2 : u2 = 324 * k + 309 := by
    have hsum : 4 * u2 = 1296 * k + 1236 := by omega
    have hsplit : 1296 * k + 1236 = 4 * (324 * k + 309) := by
      have hc : (1296 : Nat) = 4 * 324 := by decide
      have hd : (1236 : Nat) = 4 * 309 := by decide
      rw [hc, hd]
      exact four_mul_linear 324 309 k
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) (hsum.trans hsplit)
  have h4 := four_le_two_pow hW2
  have hle : 4 * e2 ≤ 9 * u2 - 1 := by
    have hmul : 4 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h4
    have : 2 ^ W2 * e2 = 9 * u2 - 1 := by omega
    omega
  have hnum : 9 * u2 - 1 = 4 * (729 * k + 695) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 4 * e2 ≤ 4 * (729 * k + 695) := by omega
    have : e2 ≤ 729 * k + 695 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩


/-! ## 7.  Honesty: classes that do not drop uniformly -/

/-- The first excursion of `n ≡ 47 (mod 64)` cannot drop: `v = 4`, `W = 1`
and `2^5 = 32 ≤ 81 = 3^4`. -/
theorem no_first_drop_of_forty_seven_mod_sixty_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h64 : n % 64 = 47) : n ≤ e := by
  have hv : v = 4 := (v_eq_four_iff h).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_forty_seven_mod_sixty_four h h64
  subst hv; subst hW
  exact no_drop_of_light h (by decide)

/-- The first excursion of `n ≡ 79 (mod 128)` cannot drop: `v = 4`, `W = 2`
and `2^6 = 64 ≤ 81 = 3^4`.  So `15 (mod 64)` is not a one-step class. -/
theorem no_first_drop_of_seventy_nine_mod_one_twenty_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h128 : n % 128 = 79) : n ≤ e := by
  have hv : v = 4 := (v_eq_four_iff h).mpr (by omega)
  have hW : W = 2 := W_eq_two_of_seventy_nine_mod_one_twenty_eight h h128
  subst hv; subst hW
  exact no_drop_of_light h (by decide)

/-- The first excursion of `n ≡ 31 (mod 128)` cannot drop: `v = 5`, `W = 1`
and `2^6 = 64 ≤ 243 = 3^5`. -/
theorem no_first_drop_of_thirty_one_mod_one_twenty_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h128 : n % 128 = 31) : n ≤ e := by
  have hv : v = 5 := (v_eq_five_iff h).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_thirty_one_mod_one_twenty_eight h h128
  subst hv; subst hW
  exact no_drop_of_light h (by decide)

/-- `15` itself drops (`v = 4`, `W = 4`). -/
theorem fifteen_drops : IsExcursion 15 4 1 4 5 ∧ 5 < 15 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `31` is the obstruction to a short uniform law on `n ≡ 15 (mod 16)`:
it survives three excursions. -/
theorem thirty_one_survives_three : IsExcursion 31 5 1 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧ IsExcursion 91 2 23 1 103 ∧
    31 ≤ 121 ∧ 31 ≤ 91 ∧ 31 ≤ 103 :=
  ExcursionMod8.thirty_one_survives_three

/-- `47` has no first drop. -/
theorem forty_seven_no_first_drop : IsExcursion 47 4 3 1 121 ∧ 47 ≤ 121 :=
  ExcursionMod8.forty_seven_no_first_drop

/-- `63` has no first drop. -/
theorem sixty_three_no_first_drop : IsExcursion 63 6 1 3 91 ∧ 63 ≤ 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Witness that `15 (mod 64)` is not a uniform one-step class. -/
theorem seventy_nine_no_first_drop : IsExcursion 79 4 5 2 101 ∧ 79 ≤ 101 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Witness that `79 (mod 128)` is not a uniform two-step class:
`207 ≡ 79 (mod 128)` lands `207 → 263 → 395`, both above `207`. -/
theorem two_hundred_seven_survives_two :
    IsExcursion 207 4 13 2 263 ∧ IsExcursion 263 3 33 1 445 ∧
      207 ≤ 263 ∧ 207 ≤ 445 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega⟩

/-- `111` has no first drop. -/
theorem one_eleven_no_first_drop : IsExcursion 111 4 7 1 283 ∧ 111 ≤ 283 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `223 ≡ 95 (mod 128)` is the complementary half of that class: `v = 5`,
`W = 2`, no first drop.  Only `95 (mod 256)` is a one-step family. -/
theorem two_twenty_three_no_first_drop : IsExcursion 223 5 7 2 425 ∧ 223 ≤ 425 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩


/-! ## 8.  The remaining input -/

/-- **What remains of Lemma X on `15 (mod 16)` after this file.**  Combined
with the even branch, `v = 1`, `3 mod 16`, `11 mod 32`, the closed subclasses
of `7 mod 8` and `27 mod 32`, and `15 mod 128`, Collatz follows from Lemma X
on the complement. -/
theorem collatz_of_open_classes
    (h39 : ∀ n : Nat, 1 < n → n % 128 = 39 → n % 256 ≠ 39 → n % 1024 ≠ 423 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h71 : ∀ n : Nat, 1 < n → n % 128 = 71 → n % 256 ≠ 199 → n % 1024 ≠ 583 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h103 : ∀ n : Nat, 1 < n → n % 128 = 103 → n % 1024 ≠ 999 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h15 : ∀ n : Nat, 1 < n → n % 16 = 15 → n % 128 ≠ 15 →
      n % 256 ≠ 95 → n % 256 ≠ 79 → n % 256 ≠ 175 →
      n % 1024 ≠ 287 → n % 1024 ≠ 367 → n % 1024 ≠ 575 →
      n % 1024 ≠ 735 → n % 1024 ≠ 975 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h27 : ∀ n : Nat, 1 < n → n % 32 = 27 → n % 128 ≠ 59 →
      n % 256 ≠ 123 → n % 256 ≠ 219 →
      ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  ExcursionSevenMod32.collatz_of_open_classes h39 h71 h103
    (fun n hn h15mod hne15 =>
      if h95 : n % 256 = 95 then
        lemmaX_of_ninety_five_mod_two_fifty_six hn h95
      else if h79 : n % 256 = 79 then
        lemmaX_of_seventy_nine_mod_two_fifty_six hn h79
      else if h175 : n % 256 = 175 then
        lemmaX_of_one_seventy_five_mod_two_fifty_six hn h175
      else if h287 : n % 1024 = 287 then
        lemmaX_of_two_eighty_seven_mod_1024 hn h287
      else if h367 : n % 1024 = 367 then
        lemmaX_of_three_sixty_seven_mod_1024 hn h367
      else if h575 : n % 1024 = 575 then
        lemmaX_of_five_seventy_five_mod_1024 hn h575
      else if h735 : n % 1024 = 735 then
        lemmaX_of_seven_thirty_five_mod_1024 hn h735
      else if h975 : n % 1024 = 975 then
        lemmaX_of_nine_seventy_five_mod_1024 hn h975
      else
        h15 n hn h15mod hne15 h95 h79 h175 h287 h367 h575 h735 h975)
    h27

end ExcursionMod16
end Collatz

section AxiomAudit
open Collatz.ExcursionMod16
#print axioms drop_of_ninety_five_mod_two_fifty_six
#print axioms drop_of_five_seventy_five_mod_1024
#print axioms lemmaX_of_seventy_nine_mod_two_fifty_six
#print axioms lemmaX_of_one_seventy_five_mod_two_fifty_six
#print axioms lemmaX_of_two_eighty_seven_mod_1024
#print axioms lemmaX_of_seven_thirty_five_mod_1024
#print axioms lemmaX_of_three_sixty_seven_mod_1024
#print axioms lemmaX_of_nine_seventy_five_mod_1024
#print axioms collatz_of_open_classes
#print axioms thirty_one_survives_three
end AxiomAudit
