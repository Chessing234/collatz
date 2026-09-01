import Collatz.Strategy.ExcursionMod8

/-!
# Round XVI — Lemma X on `n ≡ 27 (mod 32)`

`ExcursionMap` closed `n ≡ 11 (mod 32)` by a two-step chain: the first landing
is `≡ 1 (mod 4)`, so the second excursion is a `v = 1` drop that already sits
below the original start.  The complementary subclass `n ≡ 27 (mod 32)` has
the same opening `(v, W) = (2, 1)` — first landing above the start — but that
landing is `≡ 3 (mod 4)`, so the second excursion is *not* a `v = 1` drop.

What *does* drop, on infinite arithmetic progressions:

* `n ≡ 59 (mod 128)` — first landing `≡ 3 (mod 16)`, so the second excursion
  is a heavy `v = 2` drop already below the original start.
* `n ≡ 219 (mod 256)` — first landing `≡ 23 (mod 32)`, so the second
  excursion is a heavy `v = 3` drop already below the original start.
* `n ≡ 123 (mod 256)` — two light `v = 2, W = 1` landings, then a `v = 1`
  drop below the original start (three-step `ExChain`).

`59 (mod 64)` is *not* a uniform two-step class (`123` survives two).  The
residues `27, 91, 155, 251 (mod 256)` do not drop uniformly in three
excursions; witnesses are recorded below.
-/

namespace Collatz
namespace ExcursionMod32

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionMod8 Collatz.NeverDrops


/-! ## 1.  Opening run on `n ≡ 27 (mod 32)` -/

/-- `n ≡ 27 (mod 32)` is the complementary `v = 2`, `W = 1` class. -/
theorem v_two_W_one_of_twenty_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 27) : v = 2 ∧ W = 1 :=
  (v_two_W_one_iff h).mpr (by omega)

/-- The first excursion of `n ≡ 27 (mod 32)` cannot drop. -/
theorem no_first_drop_of_twenty_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 27) : n ≤ e :=
  no_drop_of_eleven_mod_sixteen h (by omega)

/-- **Exact next odd state on `n ≡ 27 (mod 32)`.**  With `v = 2` and `W = 1`
the landing is the closed form `(9 n + 5) / 8`. -/
theorem next_odd_eq_of_twenty_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 27) :
    e = (9 * n + 5) / 8 := by
  obtain ⟨hv, hW⟩ := v_two_W_one_of_twenty_seven_mod_thirty_two h h32
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := h.2.2.2.2.2.2
  rw [hv] at hnu hpeak
  rw [hW] at hpeak
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  have h9 : (3 : Nat) ^ 2 = 9 := by decide
  rw [h4] at hnu
  rw [h9, Nat.pow_one] at hpeak
  have h8e : 8 * e = 9 * n + 5 := by
    have hmid : 9 * (n + 1) = 4 * (2 * e + 1) := by
      rw [hnu]
      have hassoc : 9 * (4 * u) = 4 * (9 * u) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [hassoc, hpeak]
    omega
  have : 9 * n + 5 = 8 * e := h8e.symm
  rw [this, Nat.mul_div_right e (by omega : 0 < 8)]

/-- The landing of `n ≡ 27 (mod 32)` is `≡ 3 (mod 4)`.  This is why the
`11 mod 32` two-step (`v = 1` on the landing) does not apply. -/
theorem landing_three_mod_four_of_twenty_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 27) : e % 4 = 3 := by
  obtain ⟨hv, hW⟩ := v_two_W_one_of_twenty_seven_mod_thirty_two h h32
  have hnu : n + 1 = 4 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have he : e % 2 = 1 := h.2.2.1
  omega

private theorem four_le_two_pow {W : Nat} (hW : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this


/-! ## 2.  Two-step drop on `n ≡ 59 (mod 128)` -/

/-- On `n ≡ 59 (mod 128)` the first landing is `≡ 3 (mod 16)`. -/
theorem landing_three_mod_sixteen_of_fifty_nine_mod_one_twenty_eight
    {n v u W e : Nat} (h : IsExcursion n v u W e) (hmod : n % 128 = 59) :
    e % 16 = 3 := by
  obtain ⟨hv, hW⟩ := v_two_W_one_of_twenty_seven_mod_thirty_two h (by omega)
  have hk : n = 128 * (n / 128) + 59 := by
    have := Nat.div_add_mod n 128
    rw [hmod] at this
    exact this.symm
  let k := n / 128
  have hnu : n + 1 = 4 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have hu : u = 32 * k + 15 := by
    have : 4 * u = 128 * k + 60 := by omega
    have : 4 * u = 4 * (32 * k + 15) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he : e = 144 * k + 67 := by
    have : 9 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (144 * k + 67) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  omega

/-- **Every `n ≡ 59 (mod 128)` drops in two excursions.**  The first landing
is `≡ 3 (mod 16)`, so the second excursion has `v = 2` and `W ≥ 2`, and the
closed form of that landing sits strictly below the original start. -/
theorem lemmaX_of_fifty_nine_mod_one_twenty_eight {n : Nat}
    (_hn : 1 < n) (hmod : n % 128 = 59) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  obtain ⟨hv, hW⟩ := v_two_W_one_of_twenty_seven_mod_thirty_two hex (by omega)
  have hk : n = 128 * (n / 128) + 59 := by
    have := Nat.div_add_mod n 128
    rw [hmod] at this
    exact this.symm
  let k := n / 128
  have hnu : n + 1 = 4 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 32 * k + 15 := by
    have : 4 * u = 128 * k + 60 := by omega
    have : 4 * u = 4 * (32 * k + 15) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he : e = 144 * k + 67 := by
    have : 9 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (144 * k + 67) := by omega
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
  have hu2 : u2 = 36 * k + 17 := by
    have : 4 * u2 = 144 * k + 68 := by omega
    have : 4 * u2 = 4 * (36 * k + 17) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have h4 := four_le_two_pow hW2
  have hle : 4 * e2 ≤ 9 * u2 - 1 := by
    have hmul : 4 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h4
    have : 2 ^ W2 * e2 = 9 * u2 - 1 := by omega
    omega
  have hnum : 9 * u2 - 1 = 4 * (81 * k + 38) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 4 * e2 ≤ 4 * (81 * k + 38) := by omega
    have : e2 ≤ 81 * k + 38 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩

theorem return_of_fifty_nine_mod_one_twenty_eight {n : Nat}
    (hn : 1 < n) (hmod : n % 128 = 59) :
    ∃ k : Nat, acceleratedOrbit k n < n := by
  obtain ⟨e, hchain, hlt⟩ := lemmaX_of_fifty_nine_mod_one_twenty_eight hn hmod
  obtain ⟨t, ht⟩ := chain_is_orbit hchain
  exact ⟨t, ht ▸ hlt⟩


/-! ## 3.  Two-step drop on `n ≡ 219 (mod 256)` -/

/-- On `n ≡ 219 (mod 256)` the first landing is `≡ 23 (mod 32)`. -/
theorem landing_twenty_three_mod_thirty_two_of_two_nineteen_mod_two_fifty_six
    {n v u W e : Nat} (h : IsExcursion n v u W e) (hmod : n % 256 = 219) :
    e % 32 = 23 := by
  obtain ⟨hv, hW⟩ := v_two_W_one_of_twenty_seven_mod_thirty_two h (by omega)
  have hk : n = 256 * (n / 256) + 219 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 4 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have hu : u = 64 * k + 55 := by
    have : 4 * u = 256 * k + 220 := by omega
    have : 4 * u = 4 * (64 * k + 55) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he : e = 288 * k + 247 := by
    have : 9 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (288 * k + 247) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  omega

/-- **Every `n ≡ 219 (mod 256)` drops in two excursions.**  The first landing
is `≡ 23 (mod 32)`, so the second excursion has `v = 3` and `W ≥ 2`, and that
landing sits strictly below the original start. -/
theorem lemmaX_of_two_nineteen_mod_two_fifty_six {n : Nat}
    (_hn : 1 < n) (hmod : n % 256 = 219) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  obtain ⟨hv, hW⟩ := v_two_W_one_of_twenty_seven_mod_thirty_two hex (by omega)
  have hk : n = 256 * (n / 256) + 219 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 4 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 64 * k + 55 := by
    have : 4 * u = 256 * k + 220 := by omega
    have : 4 * u = 4 * (64 * k + 55) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he : e = 288 * k + 247 := by
    have : 9 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (288 * k + 247) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he32 : e % 32 = 23 := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion heodd
  have hv2 : v2 = 3 := (v_eq_three_iff hex2).mpr (by omega)
  have hW2 : 2 ≤ W2 := W_ge_two_of_twenty_three_mod_thirty_two hex2 he32
  have hnu2 : e + 1 = 8 * u2 := by
    have := hex2.2.2.2.2.2.1
    rw [hv2, show (2 : Nat) ^ 3 = 8 by decide] at this
    exact this
  have hpeak2 : 27 * u2 = 2 ^ W2 * e2 + 1 := by
    have := hex2.2.2.2.2.2.2
    rw [hv2, show (3 : Nat) ^ 3 = 27 by decide] at this
    exact this
  have hu2 : u2 = 36 * k + 31 := by
    have : 8 * u2 = 288 * k + 248 := by omega
    have : 8 * u2 = 8 * (36 * k + 31) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have h4 := four_le_two_pow hW2
  have hle : 4 * e2 ≤ 27 * u2 - 1 := by
    have hmul : 4 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h4
    have : 2 ^ W2 * e2 = 27 * u2 - 1 := by omega
    omega
  have hnum : 27 * u2 - 1 = 4 * (243 * k + 209) := by
    rw [hu2]
    omega
  have hdrop : e2 < n := by
    have : 4 * e2 ≤ 4 * (243 * k + 209) := by omega
    have : e2 ≤ 243 * k + 209 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩


/-! ## 4.  Three-step drop on `n ≡ 123 (mod 256)` -/

/-- **Every `n ≡ 123 (mod 256)` drops in three excursions.**  Two light
`(v, W) = (2, 1)` landings produce a state `≡ 1 (mod 4)`, whose `v = 1`
landing sits below the original start. -/
theorem lemmaX_of_one_twenty_three_mod_two_fifty_six {n : Nat}
    (_hn : 1 < n) (hmod : n % 256 = 123) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  obtain ⟨hv, hW⟩ := v_two_W_one_of_twenty_seven_mod_thirty_two hex (by omega)
  have hk : n = 256 * (n / 256) + 123 := by
    have := Nat.div_add_mod n 256
    rw [hmod] at this
    exact this.symm
  let k := n / 256
  have hnu : n + 1 = 4 * u := by
    have := hex.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * u = 2 * e + 1 := by
    have := hex.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := hex.2.2.1
  have hu : u = 64 * k + 31 := by
    have : 4 * u = 256 * k + 124 := by omega
    have : 4 * u = 4 * (64 * k + 31) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he : e = 288 * k + 139 := by
    have : 9 * u = 2 * e + 1 := hpeak
    rw [hu] at this
    have : 2 * e = 2 * (288 * k + 139) := by omega
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
  have hu2 : u2 = 72 * k + 35 := by
    have : 4 * u2 = 288 * k + 140 := by omega
    have : 4 * u2 = 4 * (72 * k + 35) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) this
  have he2 : e2 = 324 * k + 157 := by
    have : 9 * u2 = 2 * e2 + 1 := hpeak2
    rw [hu2] at this
    have : 2 * e2 = 2 * (324 * k + 157) := by omega
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
  have hu3 : u3 = 162 * k + 79 := by
    have : 2 * u3 = 324 * k + 158 := by omega
    have : 2 * u3 = 2 * (162 * k + 79) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have h2 : 2 ≤ 2 ^ W3 := two_le_two_pow (by omega)
  have hle : 2 * e3 ≤ 3 * u3 - 1 := by
    have hmul : 2 * e3 ≤ 2 ^ W3 * e3 := Nat.mul_le_mul_right e3 h2
    have : 2 ^ W3 * e3 = 3 * u3 - 1 := by omega
    omega
  have hnum : 3 * u3 - 1 = 2 * (243 * k + 118) := by
    rw [hu3]
    omega
  have hdrop : e3 < n := by
    have : 2 * e3 ≤ 2 * (243 * k + 118) := by omega
    have : e3 ≤ 243 * k + 118 := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  exact ⟨e3,
    ExChain.cons ⟨v, u, W, hex⟩
      (ExChain.cons ⟨v2, u2, W2, hex2⟩ (ExChain.one ⟨v3, u3, W3, hex3⟩)),
    hdrop⟩


/-! ## 5.  Honesty: residues that do not drop uniformly -/

/-- `27 ≡ 27 (mod 32)` is the smallest start in the class.  Its orbit begins
`27 → 31 → 121 → 91`, all above the start. -/
theorem twenty_seven_survives_three :
    IsExcursion 27 2 7 1 31 ∧
    IsExcursion 31 5 1 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧
    27 ≤ 31 ∧ 27 ≤ 121 ∧ 27 ≤ 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩

/-- Witness that `n ≡ 59 (mod 64)` is not a uniform two-step class:
`123 ≡ 59 (mod 64)` lands `123 → 139 → 157`, both above `123`. -/
theorem one_twenty_three_survives_two :
    IsExcursion 123 2 31 1 139 ∧
    IsExcursion 139 2 35 1 157 ∧
    123 ≤ 139 ∧ 123 ≤ 157 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega⟩

/-- Witness that `n ≡ 91 (mod 256)` is not a uniform three-step class. -/
theorem ninety_one_survives_three :
    IsExcursion 91 2 23 1 103 ∧
    IsExcursion 103 3 13 1 175 ∧
    IsExcursion 175 4 11 1 445 ∧
    91 ≤ 103 ∧ 91 ≤ 175 ∧ 91 ≤ 445 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩

/-- Witness that `n ≡ 155 (mod 256)` is not a uniform three-step class. -/
theorem one_fifty_five_survives_three :
    IsExcursion 155 2 39 1 175 ∧
    IsExcursion 175 4 11 1 445 ∧
    IsExcursion 445 1 223 2 167 ∧
    155 ≤ 175 ∧ 155 ≤ 445 ∧ 155 ≤ 167 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩

/-- Witness that `n ≡ 251 (mod 256)` is not a uniform three-step class. -/
theorem two_fifty_one_survives_three :
    IsExcursion 251 2 63 1 283 ∧
    IsExcursion 283 2 71 1 319 ∧
    IsExcursion 319 6 5 2 911 ∧
    251 ≤ 283 ∧ 251 ≤ 319 ∧ 251 ≤ 911 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩


/-! ## 6.  The remaining input -/

/-- **What remains of Lemma X on `27 (mod 32)` after this file.**  The classes
`59 mod 128`, `123 mod 256`, and `219 mod 256` are closed. Combined with the
even branch, `v = 1`, `3 mod 16`, `11 mod 32`, and the closed subclasses of
`7 mod 8` already proved, Collatz follows from Lemma X on the complement. -/
theorem collatz_of_open_classes
    (h7 : ∀ n : Nat, 1 < n → n % 32 = 7 → n % 128 ≠ 7 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h15 : ∀ n : Nat, 1 < n → n % 16 = 15 → n % 128 ≠ 15 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h27 : ∀ n : Nat, 1 < n → n % 32 = 27 → n % 128 ≠ 59 →
      n % 256 ≠ 123 → n % 256 ≠ 219 →
      ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  ExcursionMod8.collatz_of_open_classes h7 h15 fun n hn h27mod =>
    if h59 : n % 128 = 59 then
      lemmaX_of_fifty_nine_mod_one_twenty_eight hn h59
    else if h123 : n % 256 = 123 then
      lemmaX_of_one_twenty_three_mod_two_fifty_six hn h123
    else if h219 : n % 256 = 219 then
      lemmaX_of_two_nineteen_mod_two_fifty_six hn h219
    else
      h27 n hn h27mod h59 h123 h219

end ExcursionMod32
end Collatz

section AxiomAudit
open Collatz.ExcursionMod32
#print axioms lemmaX_of_fifty_nine_mod_one_twenty_eight
#print axioms lemmaX_of_two_nineteen_mod_two_fifty_six
#print axioms lemmaX_of_one_twenty_three_mod_two_fifty_six
#print axioms collatz_of_open_classes
#print axioms twenty_seven_survives_three
end AxiomAudit
