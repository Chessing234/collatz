import Collatz.Strategy.ExcursionMod32

/-!
# Round XVI — Lemma X on `n ≡ 7 (mod 32)` except `7 (mod 128)`

`ExcursionMod8` closed `n ≡ 7 (mod 128)` by a two-step chain: the first
landing is `≡ 5 (mod 8)`, so the second excursion is a heavy `v = 1` drop
below the original start.  The complementary residues mod 128 of the class
`n ≡ 7 (mod 32)` are `39, 71, 103`.  None of these is a uniform two-step
class (`71` is the known witness, and every `n ≡ 71 (mod 128)` has second
landing strictly above the start).

What *does* drop, on infinite arithmetic progressions:

* `n ≡ 39 (mod 256)` — first landing `≡ 3 (mod 16)`, so the second excursion
  is a heavy `v = 2` drop already below the original start.
* `n ≡ 999 (mod 1024)` — first landing `≡ 23 (mod 64)`, so the second
  excursion is a heavy `v = 3`, `W ≥ 3` drop already below the original start.
* `n ≡ 199 (mod 256)` — two landings `(v, W) = (3, 1)` then `(1, 1)`, then a
  `v = 1` drop below the original start (three-step `ExChain`).
* `n ≡ 423 (mod 1024)` — `(3, 1)` then light `(2, 1)`, then a heavy `v = 1`
  drop (`≡ 5 (mod 8)`) below the original start.
* `n ≡ 583 (mod 1024)` — `(3, 1)` then `(1, 1)`, then a heavy `v = 2` drop
  (`≡ 3 (mod 16)`) below the original start.

Not a 2-step law on all of `7 (mod 32)`.  Survivors of a uniform 2-step (and
of a 3-step, on the complementary subclasses) are recorded below.
-/

namespace Collatz
namespace ExcursionSevenMod32

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionMod8 Collatz.NeverDrops


/-! ## 1.  Extra halvings from a finer residue -/

private theorem eight_mul_mod_sixty_four (u : Nat) :
    (8 * u) % 64 = 8 * (u % 8) := by
  have hdecomp : u = 8 * (u / 8) + u % 8 := (Nat.div_add_mod u 8).symm
  have hex : 8 * u = 64 * (u / 8) + 8 * (u % 8) := by omega
  have hlt : 8 * (u % 8) < 64 := by
    have : u % 8 < 8 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem four_le_two_pow {W : Nat} (hW : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

private theorem eight_le_two_pow {W : Nat} (hW : 3 ≤ W) : 8 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 3 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

/-- `c (ak + b) = (ca) k + cb`, for pushing closed forms through `omega`. -/
private theorem mul_linear (c a b k : Nat) :
    c * (a * k + b) = (c * a) * k + c * b := by
  rw [Nat.mul_add, Nat.mul_assoc]

/-- `(2c) k + 2d = 2 (c k + d)`. -/
private theorem two_mul_linear (c d k : Nat) :
    (2 * c) * k + 2 * d = 2 * (c * k + d) := by
  rw [Nat.mul_assoc, Nat.mul_add]

/-- `(4c) k + 4d = 4 (c k + d)`. -/
private theorem four_mul_linear (c d k : Nat) :
    (4 * c) * k + 4 * d = 4 * (c * k + d) := by
  rw [Nat.mul_assoc, Nat.mul_add]

/-- On `n ≡ 1 (mod 8)` the first excursion has `v = 1` and `W = 1`. -/
theorem W_eq_one_of_one_mod_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h8 : n % 8 = 1) : W = 1 := by
  have hv : v = 1 := (v_eq_one_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv, Nat.pow_one] at hnu
  have hu4 : u % 4 = 1 := by
    have : 2 * u = 8 * (n / 8) + 2 := by omega
    have : 2 * u = 2 * (4 * (n / 8) + 1) := by omega
    have : u = 4 * (n / 8) + 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
    omega
  have hpeak4 : (3 * u - 1) % 4 = 2 := by
    have hmul : (3 * u) % 4 = 3 := by
      rw [Nat.mul_mod, hu4]
    omega
  have hval : Val2 (3 * u - 1) 1 := Val2.one_iff.mpr hpeak4
  rw [hv, Nat.pow_one] at hpeakVal
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 23 (mod 64)` the first excursion has `v = 3` and `W ≥ 3`. -/
theorem W_ge_three_of_twenty_three_mod_sixty_four {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h64 : n % 64 = 23) : 3 ≤ W := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu
  have h8 : (2 : Nat) ^ 3 = 8 := by decide
  rw [h8] at hnu
  have hu8 : u % 8 = 3 := by
    have : (8 * u) % 64 = 24 := by omega
    have := eight_mul_mod_sixty_four u
    omega
  have h27 : (3 : Nat) ^ 3 = 27 := by decide
  have h8dvd : (2 : Nat) ^ 3 ∣ 3 ^ v * u - 1 := by
    rw [hv, h27]
    have : (27 * u - 1) % 8 = 0 := by
      have hmul : (27 * u) % 8 = 1 := by
        have : 27 % 8 = 3 := by decide
        rw [Nat.mul_mod, this, hu8]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h8dvd


/-! ## 2.  Two-step drop on `n ≡ 39 (mod 256)` -/

/-- On `n ≡ 39 (mod 256)` the first landing is `≡ 3 (mod 16)`. -/
theorem landing_three_mod_sixteen_of_thirty_nine_mod_two_fifty_six
    {n v u W e : Nat} (h : IsExcursion n v u W e) (hmod : n % 256 = 39) :
    e % 16 = 3 := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two h (by omega)
  have hk : n = 256 * (n / 256) + 39 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 8 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have hu : u = 32 * k + 5 := by
    have : 8 * u = 256 * k + 40 := by omega
    have : 8 * u = 8 * (32 * k + 5) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 432 * k + 67 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (432 * k + 67) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  omega

/-- **Every `n ≡ 39 (mod 256)` drops in two excursions.**  The first landing
is `≡ 3 (mod 16)`, so the second excursion has `v = 2` and `W ≥ 2`, and that
landing sits strictly below the original start. -/
theorem lemmaX_of_thirty_nine_mod_two_fifty_six {n : Nat}
    (_hn : 1 < n) (hmod : n % 256 = 39) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 3 := (v_eq_three_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two hex (by omega)
  have hk : n = 256 * (n / 256) + 39 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 8 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 32 * k + 5 := by
    have : 8 * u = 256 * k + 40 := by omega
    have : 8 * u = 8 * (32 * k + 5) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 432 * k + 67 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (432 * k + 67) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
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
  have hu2 : u2 = 108 * k + 17 := by
    have : 4 * u2 = 432 * k + 68 := by omega
    have : 4 * u2 = 4 * (108 * k + 17) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have h4 := four_le_two_pow hW2
  have hle : 4 * e2 ≤ 9 * u2 - 1 := by
    have hmul : 4 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h4
    have : 2 ^ W2 * e2 = 9 * u2 - 1 := by omega
    omega
  have hnum : 9 * u2 - 1 = 4 * (243 * k + 38) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 4 * e2 ≤ 4 * (243 * k + 38) := by omega
    have : e2 ≤ 243 * k + 38 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩


/-! ## 3.  Two-step drop on `n ≡ 999 (mod 1024)` -/

/-- On `n ≡ 999 (mod 1024)` the first landing is `≡ 23 (mod 64)`. -/
theorem landing_twenty_three_mod_sixty_four_of_nine_ninety_nine_mod_ten_twenty_four
    {n v u W e : Nat} (h : IsExcursion n v u W e) (hmod : n % 1024 = 999) :
    e % 64 = 23 := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two h (by omega)
  have hk : n = 1024 * (n / 1024) + 999 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 8 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have hu : u = 128 * k + 125 := by
    have : 8 * u = 1024 * k + 1000 := by omega
    have : 8 * u = 8 * (128 * k + 125) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 1728 * k + 1687 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (1728 * k + 1687) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  omega

/-- **Every `n ≡ 999 (mod 1024)` drops in two excursions.**  The first landing
is `≡ 23 (mod 64)`, so the second excursion has `v = 3` and `W ≥ 3`, and that
landing sits strictly below the original start. -/
theorem lemmaX_of_nine_ninety_nine_mod_ten_twenty_four {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 999) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 3 := (v_eq_three_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two hex (by omega)
  have hk : n = 1024 * (n / 1024) + 999 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 8 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 128 * k + 125 := by
    have : 8 * u = 1024 * k + 1000 := by omega
    have : 8 * u = 8 * (128 * k + 125) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 1728 * k + 1687 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (1728 * k + 1687) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he64 : e % 64 = 23 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 3 := (v_eq_three_iff hex2).mpr (by omega)
  have hW2 : 3 ≤ W2 := W_ge_three_of_twenty_three_mod_sixty_four hex2 he64
  have hnu2 : e + 1 = 8 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak2 : 27 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, show (3 : Nat) ^ 3 = 27 by decide] at this
    exact this
  have hu2 : u2 = 216 * k + 211 := by
    have : 8 * u2 = 1728 * k + 1688 := by omega
    have : 8 * u2 = 8 * (216 * k + 211) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have h8 := eight_le_two_pow hW2
  have hle : 8 * e2 ≤ 27 * u2 - 1 := by
    have hmul : 8 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h8
    have : 2 ^ W2 * e2 = 27 * u2 - 1 := by omega
    omega
  have hnum : 27 * u2 - 1 = 8 * (729 * k + 712) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 8 * e2 ≤ 8 * (729 * k + 712) := by omega
    have : e2 ≤ 729 * k + 712 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩


/-! ## 4.  Three-step drop on `n ≡ 199 (mod 256)` -/

/-- **Every `n ≡ 199 (mod 256)` drops in three excursions.**  This is the
odd-quotient half of `n ≡ 71 (mod 128)`: after two light landings the state
is `≡ 1 (mod 4)`, and that `v = 1` drop already sits below the original
start.  The even-quotient half has no such 3-step law (`71` survives three). -/
theorem lemmaX_of_one_ninety_nine_mod_two_fifty_six {n : Nat}
    (_hn : 1 < n) (hmod : n % 256 = 199) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 3 := (v_eq_three_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two hex (by omega)
  have hk : n = 256 * (n / 256) + 199 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 8 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 32 * k + 25 := by
    have : 8 * u = 256 * k + 200 := by omega
    have : 8 * u = 8 * (32 * k + 25) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 432 * k + 337 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (432 * k + 337) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he8 : e % 8 = 1 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 1 := (v_eq_one_iff hex2).mpr (by omega)
  have hW2 : W2 = 1 := W_eq_one_of_one_mod_eight hex2 he8
  have he2odd : e2 % 2 = 1 := hex2.2.2.1
  have hnu2 : e + 1 = 2 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, Nat.pow_one] at this
    exact this
  have hpeak2 : 3 * u2 = 2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, hW2, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 216 * k + 169 := by
    have : 2 * u2 = 432 * k + 338 := by omega
    have : 2 * u2 = 2 * (216 * k + 169) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he2 : e2 = 324 * k + 253 := by
    have : 3 * u2 = 2 * e2 + 1 := hpeak2
    rw [hu2] at this
    have : 2 * e2 = 2 * (324 * k + 253) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he24 : e2 % 4 = 1 := by omega
  obtain ⟨v3, u3, W3, e3, hex3⟩ := exists_excursion he2odd
  have hv3 : v3 = 1 := (v_eq_one_iff hex3).mpr he24
  have hW3 : 1 ≤ W3 := IsExcursion.one_le_W hex3
  have hnu3 : e2 + 1 = 2 * u3 := by
    have := hex3.2.2.2.2.2.1
    rw [hv3, Nat.pow_one] at this
    exact this
  have hpeak3 : 3 * u3 = 2 ^ W3 * e3 + 1 := by
    have := hex3.2.2.2.2.2.2
    rw [hv3, Nat.pow_one] at this
    exact this
  have hu3 : u3 = 162 * k + 127 := by
    have : 2 * u3 = 324 * k + 254 := by omega
    have : 2 * u3 = 2 * (162 * k + 127) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have h2 : 2 ≤ 2 ^ W3 := two_le_two_pow (by omega)
  have hle : 2 * e3 ≤ 3 * u3 - 1 := by
    have hmul : 2 * e3 ≤ 2 ^ W3 * e3 := Nat.mul_le_mul_right e3 h2
    have : 2 ^ W3 * e3 = 3 * u3 - 1 := by omega
    omega
  have hnum : 3 * u3 - 1 = 2 * (243 * k + 190) := by
    rw [hu3]
    omega
  have hdrop : e3 < n := by
    have : 2 * e3 ≤ 2 * (243 * k + 190) := by omega
    have : e3 ≤ 243 * k + 190 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e3,
    ExChain.cons ⟨v, u, W, hex⟩
      (ExChain.cons ⟨v2, u2, W2, hex2⟩ (ExChain.one ⟨v3, u3, W3, hex3⟩)),
    hdrop⟩


/-! ## 5.  Three-step drop on `n ≡ 423 (mod 1024)` -/

/-- **Every `n ≡ 423 (mod 1024)` drops in three excursions.**  A subclass of
`n ≡ 167 (mod 256)` (the half of `39 (mod 128)` that does not drop in two
steps): two light landings produce a state `≡ 5 (mod 8)`, whose heavy `v = 1`
drop sits below the original start. -/
theorem lemmaX_of_four_twenty_three_mod_ten_twenty_four {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 423) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 3 := (v_eq_three_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two hex (by omega)
  have hk : n = 1024 * (n / 1024) + 423 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 8 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 128 * k + 53 := by
    have : 8 * u = 1024 * k + 424 := by omega
    have : 8 * u = 8 * (128 * k + 53) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 1728 * k + 715 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (1728 * k + 715) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he16 : e % 16 = 11 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  obtain ⟨hv2, hW2⟩ := (v_two_W_one_iff hex2).mpr he16
  have he2odd : e2 % 2 = 1 := hex2.2.2.1
  have hnu2 : e + 1 = 4 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak2 : 9 * u2 = 2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, hW2, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 432 * k + 179 := by
    have : 4 * u2 = 1728 * k + 716 := by omega
    have : 4 * u2 = 4 * (432 * k + 179) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he2 : e2 = 1944 * k + 805 := by
    have : 9 * u2 = 2 * e2 + 1 := hpeak2
    rw [hu2, mul_linear] at this
    have hA : 9 * 432 = 3888 := by decide
    have hB : 9 * 179 = 1611 := by decide
    rw [hA, hB] at this
    have h2e : 2 * e2 = 3888 * k + 1610 := by omega
    have hsplit : 3888 * k + 1610 = 2 * (1944 * k + 805) := by
      have hc : 3888 = 2 * 1944 := by decide
      have hd : 1610 = 2 * 805 := by decide
      rw [hc, hd, two_mul_linear]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) (h2e.trans hsplit)
  have he28 : e2 % 8 = 5 := by omega
  obtain ⟨v3, u3, W3, e3, hex3⟩ := exists_excursion he2odd
  have hv3 : v3 = 1 := (v_eq_one_iff hex3).mpr (by omega)
  have hW3 : 2 ≤ W3 := W_ge_two_of_five_mod_eight hex3 he28
  have hnu3 : e2 + 1 = 2 * u3 := by
    have := hex3.2.2.2.2.2.1
    rw [hv3, Nat.pow_one] at this
    exact this
  have hpeak3 : 3 * u3 = 2 ^ W3 * e3 + 1 := by
    have := hex3.2.2.2.2.2.2
    rw [hv3, Nat.pow_one] at this
    exact this
  have hu3 : u3 = 972 * k + 403 := by
    have h2u : 2 * u3 = 1944 * k + 806 := by omega
    have hsplit : 1944 * k + 806 = 2 * (972 * k + 403) := by
      have hc : 1944 = 2 * 972 := by decide
      have hd : 806 = 2 * 403 := by decide
      rw [hc, hd, two_mul_linear]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) (h2u.trans hsplit)
  have h4 := four_le_two_pow hW3
  have hle : 4 * e3 ≤ 3 * u3 - 1 := by
    have hmul : 4 * e3 ≤ 2 ^ W3 * e3 := Nat.mul_le_mul_right e3 h4
    have : 2 ^ W3 * e3 = 3 * u3 - 1 := by omega
    omega
  have hnum : 3 * u3 - 1 = 4 * (729 * k + 302) := by
    rw [hu3, mul_linear]
    have hA : 3 * 972 = 2916 := by decide
    have hB : 3 * 403 = 1209 := by decide
    have hC : 4 * 729 = 2916 := by decide
    have hD : 4 * 302 = 1208 := by decide
    rw [hA, hB, Nat.add_sub_assoc (by decide : 1 ≤ 1209)]
    have : 1209 - 1 = 1208 := by decide
    rw [this, ← hC, ← hD, four_mul_linear]
  have hdrop : e3 < n := by
    have : 4 * e3 ≤ 4 * (729 * k + 302) := by omega
    have : e3 ≤ 729 * k + 302 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e3,
    ExChain.cons ⟨v, u, W, hex⟩
      (ExChain.cons ⟨v2, u2, W2, hex2⟩ (ExChain.one ⟨v3, u3, W3, hex3⟩)),
    hdrop⟩


/-! ## 6.  Three-step drop on `n ≡ 583 (mod 1024)` -/

/-- **Every `n ≡ 583 (mod 1024)` drops in three excursions.**  A subclass of
`n ≡ 71 (mod 256)` (the half of `71 (mod 128)` that does not drop in three
on a 256-law): two light landings produce a state `≡ 3 (mod 16)`, whose
heavy `v = 2` drop sits below the original start. -/
theorem lemmaX_of_five_eighty_three_mod_ten_twenty_four {n : Nat}
    (_hn : 1 < n) (hmod : n % 1024 = 583) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have hv : v = 3 := (v_eq_three_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two hex (by omega)
  have hk : n = 1024 * (n / 1024) + 583 := by
    have := Nat.div_add_mod n 1024
    rw [hmod] at this
    exact this.symm
  let k := n / 1024
  have hnu : n + 1 = 8 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 128 * k + 73 := by
    have : 8 * u = 1024 * k + 584 := by omega
    have : 8 * u = 8 * (128 * k + 73) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 1728 * k + 985 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (1728 * k + 985) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he8 : e % 8 = 1 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 1 := (v_eq_one_iff hex2).mpr (by omega)
  have hW2 : W2 = 1 := W_eq_one_of_one_mod_eight hex2 he8
  have he2odd : e2 % 2 = 1 := hex2.2.2.1
  have hnu2 : e + 1 = 2 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, Nat.pow_one] at this
    exact this
  have hpeak2 : 3 * u2 = 2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, hW2, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 864 * k + 493 := by
    have h2u : 2 * u2 = 1728 * k + 986 := by omega
    have hsplit : 1728 * k + 986 = 2 * (864 * k + 493) := by
      have hc : 1728 = 2 * 864 := by decide
      have hd : 986 = 2 * 493 := by decide
      rw [hc, hd, two_mul_linear]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) (h2u.trans hsplit)
  have he2 : e2 = 1296 * k + 739 := by
    have : 3 * u2 = 2 * e2 + 1 := hpeak2
    rw [hu2, mul_linear] at this
    have hA : 3 * 864 = 2592 := by decide
    have hB : 3 * 493 = 1479 := by decide
    rw [hA, hB] at this
    have h2e : 2 * e2 = 2592 * k + 1478 := by omega
    have hsplit : 2592 * k + 1478 = 2 * (1296 * k + 739) := by
      have hc : 2592 = 2 * 1296 := by decide
      have hd : 1478 = 2 * 739 := by decide
      rw [hc, hd, two_mul_linear]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) (h2e.trans hsplit)
  have he216 : e2 % 16 = 3 := by omega
  obtain ⟨v3, u3, W3, e3, hex3⟩ := exists_excursion he2odd
  have hv3 : v3 = 2 := (v_eq_two_iff hex3).mpr (by omega)
  have hW3 : 2 ≤ W3 := ((v_two_W_ge_two_iff hex3).mpr he216).2
  have hnu3 : e2 + 1 = 4 * u3 := by
    have := hex3.2.2.2.2.2.1
    rw [hv3, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak3 : 9 * u3 = 2 ^ W3 * e3 + 1 := by
    have := hex3.2.2.2.2.2.2
    rw [hv3, show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have hu3 : u3 = 324 * k + 185 := by
    have h4u : 4 * u3 = 1296 * k + 740 := by omega
    have hsplit : 1296 * k + 740 = 4 * (324 * k + 185) := by
      have hc : 1296 = 4 * 324 := by decide
      have hd : 740 = 4 * 185 := by decide
      rw [hc, hd, four_mul_linear]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) (h4u.trans hsplit)
  have h4 := four_le_two_pow hW3
  have hle : 4 * e3 ≤ 9 * u3 - 1 := by
    have hmul : 4 * e3 ≤ 2 ^ W3 * e3 := Nat.mul_le_mul_right e3 h4
    have : 2 ^ W3 * e3 = 9 * u3 - 1 := by omega
    omega
  have hnum : 9 * u3 - 1 = 4 * (729 * k + 416) := by
    rw [hu3, mul_linear]
    have hA : 9 * 324 = 2916 := by decide
    have hB : 9 * 185 = 1665 := by decide
    have hC : 4 * 729 = 2916 := by decide
    have hD : 4 * 416 = 1664 := by decide
    rw [hA, hB, Nat.add_sub_assoc (by decide : 1 ≤ 1665)]
    have : 1665 - 1 = 1664 := by decide
    rw [this, ← hC, ← hD, four_mul_linear]
  have hdrop : e3 < n := by
    have : 4 * e3 ≤ 4 * (729 * k + 416) := by omega
    have : e3 ≤ 729 * k + 416 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e3,
    ExChain.cons ⟨v, u, W, hex⟩
      (ExChain.cons ⟨v2, u2, W2, hex2⟩ (ExChain.one ⟨v3, u3, W3, hex3⟩)),
    hdrop⟩


/-! ## 7.  Honesty: `71 (mod 128)` is not a two-step class -/

/-- **Every `n ≡ 71 (mod 128)` survives two excursions.**  The first landing
is `≡ 1 (mod 8)` so the second has `W = 1`, and the closed form `162 k + 91`
sits strictly above the start `128 k + 71`.  This is why there is no 2-step
law on all of `7 (mod 32)`. -/
theorem second_ge_of_seventy_one_mod_one_twenty_eight
    {n v u W e v2 u2 W2 e2 : Nat}
    (h : IsExcursion n v u W e) (h2 : IsExcursion e v2 u2 W2 e2)
    (hmod : n % 128 = 71) : n ≤ e2 := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two h (by omega)
  have hk : n = 128 * (n / 128) + 71 := by
    have := Nat.div_add_mod n 128
    rw [hmod] at this
    exact this.symm
  let k := n / 128
  have hnu : n + 1 = 8 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak : 27 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at this
    exact this
  have hu : u = 16 * k + 9 := by
    have : 8 * u = 128 * k + 72 := by omega
    have : 8 * u = 8 * (16 * k + 9) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he : e = 216 * k + 121 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (216 * k + 121) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he8 : e % 8 = 1 := by omega
  have hv2 : v2 = 1 := (v_eq_one_iff h2).mpr (by omega)
  have hW2 : W2 = 1 := W_eq_one_of_one_mod_eight h2 he8
  have hnu2 : e + 1 = 2 * u2 := by
    have := h2.2.2.2.2.2.1
    rw [hv2, Nat.pow_one] at this
    exact this
  have hpeak2 : 3 * u2 = 2 * e2 + 1 := by
    have := h2.2.2.2.2.2.2
    rw [hv2, hW2, Nat.pow_one] at this
    exact this
  have hu2 : u2 = 108 * k + 61 := by
    have : 2 * u2 = 216 * k + 122 := by omega
    have : 2 * u2 = 2 * (108 * k + 61) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he2 : e2 = 162 * k + 91 := by
    have : 3 * u2 = 2 * e2 + 1 := hpeak2
    rw [hu2] at this
    have : 2 * e2 = 2 * (162 * k + 91) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  omega


/-! ## 8.  Survivors -/

/-- `71 ≡ 71 (mod 128)` survives two *and* three: `71 → 121 → 91 → 103`.
Already the 2-step witness `seventy_one_survives_two`; recorded here as a
3-step witness that `71 (mod 256)` is not a uniform three-step class. -/
theorem seventy_one_survives_three :
    IsExcursion 71 3 9 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧
    IsExcursion 91 2 23 1 103 ∧
    71 ≤ 121 ∧ 71 ≤ 91 ∧ 71 ≤ 103 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩

/-- `103 ≡ 103 (mod 128)` survives three: `103 → 175 → 445 → 167`. -/
theorem one_hundred_three_survives_three :
    IsExcursion 103 3 13 1 175 ∧
    IsExcursion 175 4 11 1 445 ∧
    IsExcursion 445 1 223 2 167 ∧
    103 ≤ 175 ∧ 103 ≤ 445 ∧ 103 ≤ 167 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩

/-- `167 ≡ 39 (mod 128)` (and `167 ≡ 167 (mod 256)`) survives three:
`167 → 283 → 319 → 911`.  So `39 (mod 128)` is not a uniform two-step class,
and `167 (mod 256)` is not a uniform three-step class. -/
theorem one_sixty_seven_survives_three :
    IsExcursion 167 3 21 1 283 ∧
    IsExcursion 283 2 71 1 319 ∧
    IsExcursion 319 6 5 2 911 ∧
    167 ≤ 283 ∧ 167 ≤ 319 ∧ 167 ≤ 911 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩

/-- `935 ≡ 39 (mod 128)` survives three uniformly on its 1024-class:
`935 → 1579 → 1777 → 1333`. -/
theorem nine_thirty_five_survives_three :
    IsExcursion 935 3 117 1 1579 ∧
    IsExcursion 1579 2 395 1 1777 ∧
    IsExcursion 1777 1 889 1 1333 ∧
    935 ≤ 1579 ∧ 935 ≤ 1777 ∧ 935 ≤ 1333 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩


/-! ## 9.  The remaining input -/

/-- **What remains of Lemma X on `7 (mod 32)` after this file.**  The classes
`39 mod 256`, `199 mod 256`, `423 mod 1024`, `583 mod 1024`, and
`999 mod 1024` are closed, as is `7 mod 128` already.  Combined with the
even branch, `v = 1`, and the closed subclasses of `7 (mod 8)` and
`27 (mod 32)` already proved, Collatz follows from Lemma X on the
complement. -/
theorem collatz_of_open_classes
    (h39 : ∀ n : Nat, 1 < n → n % 128 = 39 → n % 256 ≠ 39 → n % 1024 ≠ 423 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h71 : ∀ n : Nat, 1 < n → n % 128 = 71 → n % 256 ≠ 199 → n % 1024 ≠ 583 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h103 : ∀ n : Nat, 1 < n → n % 128 = 103 → n % 1024 ≠ 999 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h15 : ∀ n : Nat, 1 < n → n % 16 = 15 → n % 128 ≠ 15 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h27 : ∀ n : Nat, 1 < n → n % 32 = 27 → n % 128 ≠ 59 →
      n % 256 ≠ 123 → n % 256 ≠ 219 →
      ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  ExcursionMod32.collatz_of_open_classes
    (fun n hn h7 hne =>
      if h39' : n % 256 = 39 then
        lemmaX_of_thirty_nine_mod_two_fifty_six hn h39'
      else if h199 : n % 256 = 199 then
        lemmaX_of_one_ninety_nine_mod_two_fifty_six hn h199
      else if h423 : n % 1024 = 423 then
        lemmaX_of_four_twenty_three_mod_ten_twenty_four hn h423
      else if h583 : n % 1024 = 583 then
        lemmaX_of_five_eighty_three_mod_ten_twenty_four hn h583
      else if h999 : n % 1024 = 999 then
        lemmaX_of_nine_ninety_nine_mod_ten_twenty_four hn h999
      else
        have h128 : n % 128 = 39 ∨ n % 128 = 71 ∨ n % 128 = 103 := by omega
        h128.elim (fun h => h39 n hn h h39' h423) fun rest =>
        rest.elim (fun h => h71 n hn h h199 h583)
          (fun h => h103 n hn h h999))
    h15 h27

end ExcursionSevenMod32
end Collatz

section AxiomAudit
open Collatz.ExcursionSevenMod32
#print axioms lemmaX_of_thirty_nine_mod_two_fifty_six
#print axioms lemmaX_of_nine_ninety_nine_mod_ten_twenty_four
#print axioms lemmaX_of_one_ninety_nine_mod_two_fifty_six
#print axioms lemmaX_of_four_twenty_three_mod_ten_twenty_four
#print axioms lemmaX_of_five_eighty_three_mod_ten_twenty_four
#print axioms second_ge_of_seventy_one_mod_one_twenty_eight
#print axioms collatz_of_open_classes
end AxiomAudit
