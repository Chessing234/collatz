import Collatz.Strategy.ExcursionMap

/-!
# Round XVI — Lemma X on `n ≡ 7 (mod 8)`

ExcursionMap closed the even branch and the class `v = 1` (`n ≡ 1 (mod 4)`).
What remains of Lemma X is odd starts `≡ 3 (mod 4)`.  Those split by the
opening run: `n ≡ 3 (mod 8)` has `v = 2`, and `n ≡ 7 (mod 8)` has `v ≥ 3`.

This file attacks the second family.  The one-step criterion

  `e < n  ↔  3^v u + 2^W ≤ 2^{v+W} u`

does **not** fire uniformly on `v ≥ 3`.  For `W = 1` (the Mersenne case
`u = 1`, and more generally `n ≡ 7 (mod 32)`) one has `2^{v+1} ≤ 3^v` at
every `v ≥ 3`, so the first excursion is light.  The class `n ≡ 7 (mod 8)`
therefore does **not** drop in a bounded number of excursions uniformly:
the first residue that survives a 1-step law is `n = 7`, and the first that
survives a 2-step (and 3-step) law is `n = 31`.

What *does* drop, on infinite arithmetic progressions:

* `n ≡ 23 (mod 32)` — `v = 3`, `W ≥ 2`, one excursion.
* `n ≡ 15 (mod 128)` — `v = 4`, `W ≥ 3`, one excursion.
* `n ≡ 7 (mod 128)` — `v = 3`, `W = 1`, then a `v = 1` landing that drops
  below the original start (two-step `ExChain`).

`RunDescent.not_two_halvings` / `halvings_lt_run` do not contradict
`NeverDrops` on this class: the former is a `v = 2` statement, and `W = 1`
with `v ≥ 3` already satisfies `W < v`.  The contradiction, where it exists,
is the drop itself.

The surviving residues of a uniform 1-step law on `n ≡ 7 (mod 8)` begin at
`7, 31, 39, 47, 63, 71, 79, 95, 103, 111, 127 (mod 128)`.  Of those, only
`7 (mod 128)` is killed by a uniform 2-step law.
-/

namespace Collatz
namespace ExcursionMod8

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap Collatz.NeverDrops


/-! ## 1.  Valuation from residue -/

/-- `v = 3` is the residue `7 mod 16`. -/
theorem v_eq_three_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 3 ↔ n % 16 = 7 := by
  constructor
  · intro hv
    obtain ⟨_, hu, _, _, _, hnu, _⟩ := h
    rw [hv] at hnu
    have h8 : (2 : Nat) ^ 3 = 8 := by decide
    rw [h8] at hnu
    have h16 : (n + 1) % 16 = 8 := by
      have : (8 * u) % 16 = 8 := by omega
      omega
    omega
  · intro h16
    have hval : Val2 (n + 1) 3 := by
      refine Val2.of_mod ?_
      have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
      rw [hpow]
      have hadd : (n + 1) % 16 = (n % 16 + 1) % 16 := Nat.add_mod n 1 16
      rw [hadd, h16]
    exact Val2.unique (val2_succ_of h) hval

/-- `v = 4` is the residue `15 mod 32`. -/
theorem v_eq_four_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 4 ↔ n % 32 = 15 := by
  constructor
  · intro hv
    obtain ⟨_, hu, _, _, _, hnu, _⟩ := h
    rw [hv] at hnu
    have h16 : (2 : Nat) ^ 4 = 16 := by decide
    rw [h16] at hnu
    have : (n + 1) % 32 = 16 := by
      have : (16 * u) % 32 = 16 := by omega
      omega
    omega
  · intro h32
    have hval : Val2 (n + 1) 4 := by
      refine Val2.of_mod ?_
      have hpow : (2 : Nat) ^ (4 + 1) = 32 := by decide
      rw [hpow]
      have hadd : (n + 1) % 32 = (n % 32 + 1) % 32 := Nat.add_mod n 1 32
      rw [hadd, h32]
    exact Val2.unique (val2_succ_of h) hval

/-- On `n ≡ 7 (mod 8)` the opening run has length at least three. -/
theorem v_ge_three_of_seven_mod_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h8 : n % 8 = 7) : 3 ≤ v := by
  have hval := val2_succ_of h
  have hdvd : (2 : Nat) ^ 3 ∣ n + 1 := by
    have : (n + 1) % 8 = 0 := by omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hval).mp hdvd


/-! ## 2.  Extra halvings from a finer residue -/

private theorem eight_mul_mod (u : Nat) : (8 * u) % 32 = 8 * (u % 4) := by
  have hdecomp : u = 4 * (u / 4) + u % 4 := (Nat.div_add_mod u 4).symm
  have hex : 8 * u = 32 * (u / 4) + 8 * (u % 4) := by omega
  have hlt : 8 * (u % 4) < 32 := by
    have : u % 4 < 4 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem two_mul_mod_eight (u : Nat) : (2 * u) % 8 = 2 * (u % 4) := by
  have hdecomp : u = 4 * (u / 4) + u % 4 := (Nat.div_add_mod u 4).symm
  have hex : 2 * u = 8 * (u / 4) + 2 * (u % 4) := by omega
  have hlt : 2 * (u % 4) < 8 := by
    have : u % 4 < 4 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem sixteen_mul_mod (u : Nat) : (16 * u) % 128 = 16 * (u % 8) := by
  have hdecomp : u = 8 * (u / 8) + u % 8 := (Nat.div_add_mod u 8).symm
  have hex : 16 * u = 128 * (u / 8) + 16 * (u % 8) := by omega
  have hlt : 16 * (u % 8) < 128 := by
    have : u % 8 < 8 := Nat.mod_lt u (by omega)
    omega
  rw [hex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- On `n ≡ 7 (mod 32)` the first excursion has `v = 3` and `W = 1`. -/
theorem W_eq_one_of_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 7) : W = 1 := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu hpeakVal
  have h8 : (2 : Nat) ^ 3 = 8 := by decide
  rw [h8] at hnu
  have hu4 : u % 4 = 1 := by
    have : (8 * u) % 32 = 8 := by omega
    have := eight_mul_mod u
    omega
  have h27 : (3 : Nat) ^ 3 = 27 := by decide
  rw [h27] at hpeakVal
  have hpeak4 : (27 * u - 1) % 4 = 2 := by
    have hmul : (27 * u) % 4 = 3 := by
      have : 27 % 4 = 3 := by decide
      rw [Nat.mul_mod, this, hu4]
    omega
  have hval : Val2 (27 * u - 1) 1 := Val2.one_iff.mpr hpeak4
  exact Val2.unique hpeakVal hval

/-- On `n ≡ 23 (mod 32)` the first excursion has `v = 3` and `W ≥ 2`. -/
theorem W_ge_two_of_twenty_three_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 23) : 2 ≤ W := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu
  have h8 : (2 : Nat) ^ 3 = 8 := by decide
  rw [h8] at hnu
  have hu4 : u % 4 = 3 := by
    have : (8 * u) % 32 = 24 := by omega
    have := eight_mul_mod u
    omega
  have h27 : (3 : Nat) ^ 3 = 27 := by decide
  have h4dvd : (2 : Nat) ^ 2 ∣ 3 ^ v * u - 1 := by
    rw [hv, h27]
    have : (27 * u - 1) % 4 = 0 := by
      have hmul : (27 * u) % 4 = 1 := by
        have : 27 % 4 = 3 := by decide
        rw [Nat.mul_mod, this, hu4]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h4dvd

/-- On `n ≡ 5 (mod 8)` the first excursion has `v = 1` and `W ≥ 2`. -/
theorem W_ge_two_of_five_mod_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h8 : n % 8 = 5) : 2 ≤ W := by
  have hv : v = 1 := (v_eq_one_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv, Nat.pow_one] at hnu
  have hu4 : u % 4 = 3 := by
    have : (2 * u) % 8 = 6 := by omega
    have := two_mul_mod_eight u
    omega
  have h4dvd : (2 : Nat) ^ 2 ∣ 3 ^ v * u - 1 := by
    rw [hv, Nat.pow_one]
    have : (3 * u - 1) % 4 = 0 := by
      have hmul : (3 * u) % 4 = 1 := by
        rw [Nat.mul_mod, hu4]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h4dvd

/-- On `n ≡ 15 (mod 128)` the first excursion has `v = 4` and `W ≥ 3`. -/
theorem W_ge_three_of_fifteen_mod_one_twenty_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h128 : n % 128 = 15) : 3 ≤ W := by
  have hv : v = 4 := (v_eq_four_iff h).mpr (by omega)
  have hpeakVal := val2_peak_of h
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  rw [hv] at hnu
  have h16 : (2 : Nat) ^ 4 = 16 := by decide
  rw [h16] at hnu
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  have h8dvd : (2 : Nat) ^ 3 ∣ 3 ^ v * u - 1 := by
    rw [hv, h81]
    have : (81 * u - 1) % 8 = 0 := by
      have hu8 : u % 8 = 1 := by
        have : (16 * u) % 128 = 16 := by omega
        have := sixteen_mul_mod u
        omega
      have hmul : (81 * u) % 8 = 1 := by
        have : 81 % 8 = 1 := by decide
        rw [Nat.mul_mod, this, hu8]
      omega
    exact (pow_two_dvd_iff).mpr this
  exact (Val2.dvd_iff_le hpeakVal).mp h8dvd


/-! ## 3.  Drop inequalities at `v = 3` and `v = 4` -/

private theorem four_le_two_pow {W : Nat} (hW : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

private theorem eight_le_two_pow {W : Nat} (hW : 3 ≤ W) : 8 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 3 ≤ 2 ^ W := two_pow_le_two_pow hW
  simpa using this

/-- `27 u + 2^W ≤ 8 · 2^W · u` for `W ≥ 2`. -/
private theorem v_three_drop_ineq {u W : Nat} (hu : 1 ≤ u) (hW : 2 ≤ W) :
    27 * u + 2 ^ W ≤ 8 * 2 ^ W * u := by
  have h4 := four_le_two_pow hW
  have h28 : 28 ≤ 7 * 2 ^ W := by
    have : 7 * 4 ≤ 7 * 2 ^ W := Nat.mul_le_mul_left 7 h4
    omega
  have hsum : 28 + 2 ^ W ≤ 8 * 2 ^ W := by
    have : 28 + 2 ^ W ≤ 7 * 2 ^ W + 2 ^ W := Nat.add_le_add_right h28 _
    have h8 : 7 * 2 ^ W + 2 ^ W = 8 * 2 ^ W := by
      have : 7 * 2 ^ W + 1 * 2 ^ W = (7 + 1) * 2 ^ W := (Nat.add_mul 7 1 (2 ^ W)).symm
      simpa using this
    omega
  calc 27 * u + 2 ^ W
      ≤ 28 * u + 2 ^ W * u := by
          have hA : 27 * u ≤ 28 * u := Nat.mul_le_mul_right u (by omega)
          have hB : 2 ^ W ≤ 2 ^ W * u := Nat.le_mul_of_pos_right (2 ^ W) hu
          omega
    _ = (28 + 2 ^ W) * u := by rw [Nat.add_mul]
    _ ≤ (8 * 2 ^ W) * u := Nat.mul_le_mul_right u hsum
    _ = 8 * 2 ^ W * u := by simp [Nat.mul_assoc]

/-- `81 u + 2^W ≤ 16 · 2^W · u` for `W ≥ 3`. -/
private theorem v_four_drop_ineq {u W : Nat} (hu : 1 ≤ u) (hW : 3 ≤ W) :
    81 * u + 2 ^ W ≤ 16 * 2 ^ W * u := by
  have h8 := eight_le_two_pow hW
  have h120 : 120 ≤ 15 * 2 ^ W := by
    have : 15 * 8 ≤ 15 * 2 ^ W := Nat.mul_le_mul_left 15 h8
    omega
  have hsum : 120 + 2 ^ W ≤ 16 * 2 ^ W := by
    have : 120 + 2 ^ W ≤ 15 * 2 ^ W + 2 ^ W := Nat.add_le_add_right h120 _
    have h16 : 15 * 2 ^ W + 2 ^ W = 16 * 2 ^ W := by
      have : 15 * 2 ^ W + 1 * 2 ^ W = (15 + 1) * 2 ^ W :=
        (Nat.add_mul 15 1 (2 ^ W)).symm
      simpa using this
    omega
  calc 81 * u + 2 ^ W
      ≤ 120 * u + 2 ^ W * u := by
          have hA : 81 * u ≤ 120 * u := Nat.mul_le_mul_right u (by omega)
          have hB : 2 ^ W ≤ 2 ^ W * u := Nat.le_mul_of_pos_right (2 ^ W) hu
          omega
    _ = (120 + 2 ^ W) * u := by rw [Nat.add_mul]
    _ ≤ (16 * 2 ^ W) * u := Nat.mul_le_mul_right u hsum
    _ = 16 * 2 ^ W * u := by simp [Nat.mul_assoc]

/-- **Heavy `v = 3` drops.**  Two extra halvings beat `3^3 = 27`. -/
theorem drop_of_v_three_heavy {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 3) (hW : 2 ≤ W) : e < n := by
  subst hv
  refine (drop_iff h).mpr ?_
  have h27 : (3 : Nat) ^ 3 = 27 := by decide
  have hpow : (2 : Nat) ^ (3 + W) = 8 * 2 ^ W := by rw [Nat.pow_add]
  rw [h27, hpow]
  have hu : 1 ≤ u := by
    have := h.2.1
    omega
  exact v_three_drop_ineq hu hW

/-- **Heavy `v = 4` drops.**  Three extra halvings beat `3^4 = 81`. -/
theorem drop_of_v_four_heavy {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 4) (hW : 3 ≤ W) : e < n := by
  subst hv
  refine (drop_iff h).mpr ?_
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  have hpow : (2 : Nat) ^ (4 + W) = 16 * 2 ^ W := by rw [Nat.pow_add]
  rw [h81, hpow]
  have hu : 1 ≤ u := by
    have := h.2.1
    omega
  exact v_four_drop_ineq hu hW


/-! ## 4.  The class `n ≡ 7 (mod 32)`: no first drop, exact landing -/

/-- The first excursion of `n ≡ 7 (mod 32)` cannot drop: `W = 1` and
`2^{4} = 16 ≤ 27 = 3^3`. -/
theorem no_first_drop_of_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 7) : n ≤ e := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two h h32
  subst hv; subst hW
  exact no_drop_of_light h (by decide)

/-- **Exact next odd state on `n ≡ 7 (mod 32)`.**  With `v = 3` and `W = 1`
the landing is the closed form `(27 n + 19) / 16`. -/
theorem next_odd_eq_of_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 7) :
    e = (27 * n + 19) / 16 := by
  have hv : v = 3 := (v_eq_three_iff h).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two h h32
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := h.2.2.2.2.2.2
  rw [hv] at hnu hpeak
  rw [hW] at hpeak
  have h8 : (2 : Nat) ^ 3 = 8 := by decide
  have h27 : (3 : Nat) ^ 3 = 27 := by decide
  rw [h8] at hnu
  rw [h27, Nat.pow_one] at hpeak
  have h16e : 16 * e = 27 * n + 19 := by
    have hmid : 27 * (n + 1) = 8 * (2 * e + 1) := by
      rw [hnu]
      have hassoc : 27 * (8 * u) = 8 * (27 * u) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [hassoc, hpeak]
    omega
  have : 27 * n + 19 = 16 * e := h16e.symm
  rw [this, Nat.mul_div_right e (by omega : 0 < 16)]

/-- The landing of `n ≡ 7 (mod 32)` is `1 mod 4` precisely on `n ≡ 7 (mod 64)`,
and `3 mod 4` on `n ≡ 39 (mod 64)`. -/
theorem next_odd_mod_four_of_seven_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 7) :
    (n % 64 = 7 ∧ e % 4 = 1) ∨ (n % 64 = 39 ∧ e % 4 = 3) := by
  have heq := next_odd_eq_of_seven_mod_thirty_two h h32
  have h64 : n % 64 = 7 ∨ n % 64 = 39 := by omega
  rcases h64 with h7 | h39
  · left
    refine ⟨h7, ?_⟩
    have hdiv := Nat.div_add_mod n 64
    rw [h7] at hdiv
    have hn : n = 64 * (n / 64) + 7 := hdiv.symm
    have : 27 * n + 19 = 16 * (108 * (n / 64) + 13) := by
      rw [hn]
      omega
    have : (27 * n + 19) / 16 = 108 * (n / 64) + 13 := by
      rw [this, Nat.mul_div_right _ (by omega : 0 < 16)]
    omega
  · right
    refine ⟨h39, ?_⟩
    have hdiv := Nat.div_add_mod n 64
    rw [h39] at hdiv
    have hn : n = 64 * (n / 64) + 39 := hdiv.symm
    have : 27 * n + 19 = 16 * (108 * (n / 64) + 67) := by
      rw [hn]
      omega
    have : (27 * n + 19) / 16 = 108 * (n / 64) + 67 := by
      rw [this, Nat.mul_div_right _ (by omega : 0 < 16)]
    omega


/-! ## 5.  One-step drops on two arithmetic progressions -/

/-- **Every `n ≡ 23 (mod 32)` drops in one excursion.**  These are the
`v = 3` starts whose odd cofactor is `3 mod 4`, forcing `W ≥ 2`. -/
theorem drop_of_twenty_three_mod_thirty_two {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h32 : n % 32 = 23) : e < n :=
  drop_of_v_three_heavy h ((v_eq_three_iff h).mpr (by omega))
    (W_ge_two_of_twenty_three_mod_thirty_two h h32)

/-- **Every `n ≡ 15 (mod 128)` drops in one excursion.**  These are the
`v = 4` starts whose odd cofactor is `1 mod 8`, forcing `W ≥ 3`. -/
theorem drop_of_fifteen_mod_one_twenty_eight {n v u W e : Nat}
    (h : IsExcursion n v u W e) (h128 : n % 128 = 15) : e < n :=
  drop_of_v_four_heavy h ((v_eq_four_iff h).mpr (by omega))
    (W_ge_three_of_fifteen_mod_one_twenty_eight h h128)

theorem lemmaX_of_twenty_three_mod_thirty_two {n : Nat}
    (_hn : 1 < n) (hmod : n % 32 = 23) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  exact ⟨e, ExChain.one ⟨v, u, W, h⟩, drop_of_twenty_three_mod_thirty_two h hmod⟩

theorem lemmaX_of_fifteen_mod_one_twenty_eight {n : Nat}
    (_hn : 1 < n) (hmod : n % 128 = 15) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  exact ⟨e, ExChain.one ⟨v, u, W, h⟩, drop_of_fifteen_mod_one_twenty_eight h hmod⟩


/-! ## 6.  Two-step drop on `n ≡ 7 (mod 128)` -/

/-- **Every `n ≡ 7 (mod 128)` drops in two excursions.**  The first landing
is `≡ 5 (mod 8)`, so the second excursion has `v = 1` and `W ≥ 2`, and the
closed form of that landing sits strictly below the original start. -/
theorem lemmaX_of_seven_mod_one_twenty_eight {n : Nat}
    (hn : 1 < n) (hmod : n % 128 = 7) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, hex⟩ := exists_excursion hodd
  have h32 : n % 32 = 7 := by omega
  have hv : v = 3 := (v_eq_three_iff hex).mpr (by omega)
  have hW : W = 1 := W_eq_one_of_seven_mod_thirty_two hex h32
  have hk : n = 128 * (n / 128) + 7 := by
    have := Nat.div_add_mod n 128
    rw [hmod] at this
    exact this.symm
  let k := n / 128
  have hnu : n + 1 = 2 ^ v * u := hex.2.2.2.2.2.1
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := hex.2.2.2.2.2.2
  have he : e % 2 = 1 := hex.2.2.1
  rw [hv] at hnu hpeak
  rw [hW] at hpeak
  have h8 : (2 : Nat) ^ 3 = 8 := by decide
  have h27 : (3 : Nat) ^ 3 = 27 := by decide
  rw [h8] at hnu
  rw [h27, Nat.pow_one] at hpeak
  have hu' : u = 16 * k + 1 := by
    have : 8 * u = 128 * k + 8 := by omega
    have : 8 * u = 8 * (16 * k + 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) this
  have he' : e = 216 * k + 13 := by
    have : 27 * u = 2 * e + 1 := hpeak
    rw [hu'] at this
    have : 2 * e = 2 * (216 * k + 13) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) this
  have he8 : e % 8 = 5 := by omega
  have hegt : 1 < e := by omega
  obtain ⟨v2, u2, W2, e2, hex2⟩ := exists_excursion he
  have hv2 : v2 = 1 := (v_eq_one_iff hex2).mpr (by omega)
  have hW2 : 2 ≤ W2 := W_ge_two_of_five_mod_eight hex2 he8
  have hnu2 : e + 1 = 2 ^ v2 * u2 := hex2.2.2.2.2.2.1
  have hpeak2 : 3 ^ v2 * u2 = 2 ^ W2 * e2 + 1 := hex2.2.2.2.2.2.2
  rw [hv2, Nat.pow_one] at hnu2 hpeak2
  have h4 : 4 ≤ 2 ^ W2 := four_le_two_pow hW2
  have hlt : 4 * e2 < 3 * u2 := by
    have : 2 ^ W2 * e2 + 1 = 3 * u2 := hpeak2.symm
    have : 4 * e2 ≤ 2 ^ W2 * e2 := Nat.mul_le_mul_right e2 h4
    omega
  have hle : 3 * u2 ≤ 4 * n := by
    have : 3 * (e + 1) ≤ 8 * n := by
      rw [he', hk]
      omega
    have : 3 * (2 * u2) ≤ 8 * n := by
      rw [← hnu2]
      exact this
    omega
  have hdrop : e2 < n := by omega
  exact ⟨e2, ExChain.cons ⟨v, u, W, hex⟩ (ExChain.one ⟨v2, u2, W2, hex2⟩), hdrop⟩


/-! ## 7.  NeverDrops exclusions, and the remaining input -/

theorem not_neverDrops_of_twenty_three_mod_thirty_two {n : Nat}
    (_hn : 1 < n) (hmod : n % 32 = 23) : ¬ NeverDrops n := by
  intro hnd
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have hlt := drop_of_twenty_three_mod_thirty_two h hmod
  have hland := landing_eq h
  have := hnd (v + W)
  omega

theorem not_neverDrops_of_fifteen_mod_one_twenty_eight {n : Nat}
    (_hn : 1 < n) (hmod : n % 128 = 15) : ¬ NeverDrops n := by
  intro hnd
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have hlt := drop_of_fifteen_mod_one_twenty_eight h hmod
  have hland := landing_eq h
  have := hnd (v + W)
  omega

theorem not_neverDrops_of_seven_mod_one_twenty_eight {n : Nat}
    (hn : 1 < n) (hmod : n % 128 = 7) : ¬ NeverDrops n := by
  intro hnd
  obtain ⟨e, hchain, hlt⟩ := lemmaX_of_seven_mod_one_twenty_eight hn hmod
  obtain ⟨t, ht⟩ := chain_is_orbit hchain
  have := hnd t
  omega

/-- **What remains of Lemma X after this file.**  The classes `23 mod 32`,
`15 mod 128`, and `7 mod 128` are closed.  Combined with the even branch
and `v = 1`, Collatz follows from Lemma X on the complement. -/
theorem collatz_of_lemmaX_remaining
    (h : ∀ n : Nat, 1 < n → n % 4 = 3 → n % 32 ≠ 23 → n % 128 ≠ 7 →
      n % 128 ≠ 15 → ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  collatz_of_lemmaX_three_mod_four fun n hn h3 =>
    if h23 : n % 32 = 23 then
      lemmaX_of_twenty_three_mod_thirty_two hn h23
    else if h7 : n % 128 = 7 then
      lemmaX_of_seven_mod_one_twenty_eight hn h7
    else if h15 : n % 128 = 15 then
      lemmaX_of_fifteen_mod_one_twenty_eight hn h15
    else
      h n hn h3 h23 h7 h15


/-! ## 8.  Honesty: the class does not drop uniformly -/

/-- `31 ≡ 31 (mod 32)` is the smallest `n ≡ 7 (mod 8)` that does not drop
in one, two, or three excursions.  Its orbit begins `31 → 121 → 91 → 103`. -/
theorem thirty_one_survives_three :
    IsExcursion 31 5 1 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧
    IsExcursion 91 2 23 1 103 ∧
    31 ≤ 121 ∧ 31 ≤ 91 ∧ 31 ≤ 103 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega, by omega⟩

/-- Witness that `n ≡ 15 (mod 32)` is not a uniform one-step class:
`47` has `v = 4`, `W = 1`, and lands at `121 > 47`. -/
theorem forty_seven_no_first_drop : IsExcursion 47 4 3 1 121 ∧ 47 ≤ 121 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Witness that `n ≡ 7 (mod 32)` is not a uniform two-step class:
`71 ≡ 71 (mod 128)` lands `71 → 121 → 91`, both above `71`. -/
theorem seventy_one_survives_two :
    IsExcursion 71 3 9 1 121 ∧ IsExcursion 121 1 61 1 91 ∧ 71 ≤ 121 ∧ 71 ≤ 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    by omega, by omega⟩

/-- **The actual remaining input.**  Collatz follows from Lemma X on:

* `n ≡ 7 (mod 32)` except `n ≡ 7 (mod 128)` (already closed);
* `n ≡ 15 (mod 16)` except `n ≡ 15 (mod 128)` (already closed);
* `n ≡ 27 (mod 32)`.

Not a uniform finite-window drop: `31` survives three excursions, `47` does
not drop first, `71` survives two. -/
theorem collatz_of_open_classes
    (h7 : ∀ n : Nat, 1 < n → n % 32 = 7 → n % 128 ≠ 7 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h15 : ∀ n : Nat, 1 < n → n % 16 = 15 → n % 128 ≠ 15 →
      ∃ e : Nat, ExChain n e ∧ e < n)
    (h27 : ∀ n : Nat, 1 < n → n % 32 = 27 →
      ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  collatz_of_lemmaX_remaining fun n hn _h3 h23 h7mod h15mod =>
    have h16 : n % 16 = 3 ∨ n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by omega
    h16.elim (fun h3' => lemmaX_of_three_mod_sixteen hn h3') fun hrest =>
    hrest.elim (fun _h7' =>
      have h32 : n % 32 = 7 ∨ n % 32 = 23 := by omega
      h32.elim (fun h7'' => h7 n hn h7'' h7mod)
        (fun h23' => (h23 h23').elim)) fun hrest =>
    hrest.elim (fun _h11 =>
      have h32 : n % 32 = 11 ∨ n % 32 = 27 := by omega
      h32.elim (fun h11' => lemmaX_of_eleven_mod_thirtytwo hn h11')
        (fun h27' => h27 n hn h27'))
      (fun h15' => h15 n hn h15' h15mod)

end ExcursionMod8
end Collatz

section AxiomAudit
open Collatz.ExcursionMod8
#print axioms v_eq_three_iff
#print axioms drop_of_twenty_three_mod_thirty_two
#print axioms drop_of_fifteen_mod_one_twenty_eight
#print axioms lemmaX_of_seven_mod_one_twenty_eight
#print axioms collatz_of_lemmaX_remaining
#print axioms collatz_of_open_classes
end AxiomAudit
