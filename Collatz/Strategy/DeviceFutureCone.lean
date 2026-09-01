import Collatz.Core.Arith
import Collatz.Strategy.LiftExponent
import Collatz.Strategy.ExcursionMap

/-!
# Leftover-precision future cone of a *fixed* odd integer

`word_realizable` quantifies over starts.  The forward orbit of one `n` is a
function, so that future is a singleton.  This file keeps `n` fixed and
records two cones of symbolic states still compatible with that `n`.

1. **W-tail cone `WLift n k W'`.**  Unrevealed 2-adic digits of *this*
   cofactor `u`.  Nested in the budget `k`.  Not a singleton for `k ≤ W`,
   and never the full extra-halving alphabet.

2. **Reverse sibling cone `ReverseLetter n v W`.**  Odd parents of this
   landing.  Empty when `3 ∣ n`.  Rank exactly `3` at `n = 13`, `W = 1`.

The realization coordinate `Q` is the current odd integer after a reverse
prefix.  It is the entire constraint on the next reverse letter.

No statement about Collatz is made.
-/

namespace Collatz
namespace DeviceFutureCone

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap


/-! ## 0.  Small arithmetic -/

theorem three_pow_odd (k : Nat) : (3 : Nat) ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem two_pow_even_of_pos {k : Nat} (hk : 0 < k) : (2 : Nat) ^ k % 2 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [two_pow_succ]
  exact Nat.mul_mod_right 2 _

theorem odd_add_two_pow {u t k : Nat} (hu : u % 2 = 1) (hk : 0 < k) :
    (u + t * 2 ^ k) % 2 = 1 := by
  have he : (t * 2 ^ k) % 2 = 0 := by
    rw [Nat.mul_mod, two_pow_even_of_pos hk]
    simp
  omega

theorem lift_odd {v u t k : Nat} (hv : 0 < v) (hu : u % 2 = 1) (_hk : 0 < k) :
    (2 ^ v * (u + t * 2 ^ k) - 1) % 2 = 1 := by
  have hpos : 0 < 2 ^ v * (u + t * 2 ^ k) :=
    Nat.mul_pos (two_pow_pos v) (Nat.add_pos_left (by omega : 0 < u) _)
  have heven : (2 ^ v * (u + t * 2 ^ k)) % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, v = j + 1 := ⟨v - 1, by omega⟩
    rw [two_pow_succ, Nat.mul_assoc]
    exact Nat.mul_mod_right 2 _
  omega

theorem lift_succ {v u t k : Nat} (hu : u % 2 = 1) :
    (2 ^ v * (u + t * 2 ^ k) - 1) + 1 = 2 ^ v * (u + t * 2 ^ k) := by
  have : 0 < 2 ^ v * (u + t * 2 ^ k) :=
    Nat.mul_pos (two_pow_pos v) (Nat.add_pos_left (by omega : 0 < u) _)
  omega

theorem val2_two_pow (k : Nat) : Val2 (2 ^ k) k :=
  ⟨1, rfl, by rw [Nat.mul_one]⟩

theorem val2_three_pow_two_pow (v k : Nat) : Val2 (3 ^ v * 2 ^ k) k := by
  have h := Val2.mul (Val2.of_odd (three_pow_odd v)) (val2_two_pow k)
  simpa using h

theorem one_le_three_pow_mul {v u : Nat} (hu : 0 < u) : 1 ≤ 3 ^ v * u :=
  Nat.mul_pos (three_pow_pos v) hu


/-! ## 1.  The W-tail cone of a fixed start -/

/-- A value `W'` is in the leftover-precision cone of *this* `n` when some
2-adic tail of its cofactor realises extra-halving count `W'`, keeping the
same odd-run length `v`. -/
def WLift (n k W' : Nat) : Prop :=
  ∃ v u W e t e' : Nat,
    IsExcursion n v u W e ∧
      0 < k ∧
        IsExcursion (2 ^ v * (u + t * 2 ^ k) - 1) v (u + t * 2 ^ k) W' e'

/-- The zero lift is `n` itself, so the true `W` always sits in the cone. -/
theorem WLift_self {n v u W e k : Nat}
    (h : IsExcursion n v u W e) (hk : 0 < k) : WLift n k W := by
  refine ⟨v, u, W, e, 0, e, h, hk, ?_⟩
  have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hrewrite : 2 ^ v * (u + 0 * 2 ^ k) - 1 = n := by
    simp only [Nat.zero_mul, Nat.add_zero]
    omega
  have hurewrite : u + 0 * 2 ^ k = u := by simp
  rw [hrewrite, hurewrite]
  exact h

/-- **Nested.**  Revealing more digits of this `n` shrinks the cone. -/
theorem WLift_nested {n k k' W' : Nat} (hle : k ≤ k') (hk : 0 < k)
    (h : WLift n k' W') : WLift n k W' := by
  obtain ⟨v, u, W, e, t, e', hex, _, hlift⟩ := h
  refine ⟨v, u, W, e, t * 2 ^ (k' - k), e', hex, hk, ?_⟩
  have hpow : (2 : Nat) ^ k' = 2 ^ k * 2 ^ (k' - k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have heq : u + t * 2 ^ k' = u + (t * 2 ^ (k' - k)) * 2 ^ k := by
    have : t * 2 ^ k' = (t * 2 ^ (k' - k)) * 2 ^ k := by
      rw [hpow]
      simp [Nat.mul_comm, Nat.mul_left_comm]
    omega
  simpa [heq] using hlift

/-- Peak of a lift: `3^v (u + t 2^k) − 1 = 2^W e + t 3^v 2^k`. -/
theorem peak_of_lift {n v u W e t k : Nat} (h : IsExcursion n v u W e) :
    3 ^ v * (u + t * 2 ^ k) - 1 = 2 ^ W * e + t * (3 ^ v * 2 ^ k) := by
  have hodd : u % 2 = 1 := h.2.1
  have hu : 0 < u := by omega
  have h3u : 1 ≤ 3 ^ v * u := one_le_three_pow_mul hu
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := h.2.2.2.2.2.2
  rw [Nat.mul_add]
  have hassoc : 3 ^ v * (t * 2 ^ k) = t * (3 ^ v * 2 ^ k) := by
    simp [Nat.mul_assoc, Nat.mul_comm]
  rw [hassoc, Nat.sub_add_comm h3u]
  have : 3 ^ v * u - 1 = 2 ^ W * e := by
    rw [hpeak]
    exact Nat.add_sub_cancel (2 ^ W * e) 1
  rw [this]

/-- The lift `t = 1` at budget `k < W` has peak valuation exactly `k`. -/
theorem val2_peak_lift_one {n v u W e k : Nat}
    (h : IsExcursion n v u W e) (hlt : k < W) :
    Val2 (3 ^ v * (u + 1 * 2 ^ k) - 1) k := by
  have hP : Val2 (2 ^ W * e) W := ⟨e, h.2.2.1, rfl⟩
  have hT : Val2 (3 ^ v * 2 ^ k) k := val2_three_pow_two_pow v k
  have hadd := Val2.add_of_lt' hT hP hlt
  have hsum := peak_of_lift (t := 1) (k := k) h
  simp only [Nat.one_mul] at hsum ⊢
  rw [hsum]
  exact hadd

/-- Package an excursion from a `Val2` peak. -/
theorem excursion_of_lift {n v u W e t k e' : Nat}
    (h : IsExcursion n v u W e) (hk : 0 < k)
    (hpeak : 3 ^ v * (u + t * 2 ^ k) = 2 ^ k * e' + 1) (he' : e' % 2 = 1) :
    IsExcursion (2 ^ v * (u + t * 2 ^ k) - 1) v (u + t * 2 ^ k) k e' := by
  have hu : u % 2 = 1 := h.2.1
  have hv : 0 < v := h.2.2.2.1
  exact ⟨lift_odd hv hu hk, odd_add_two_pow hu hk, he', hv, hk,
    lift_succ hu, hpeak⟩

/-- **Budget `k < W`: the letter `k` is realised by the lift `t = 1`.** -/
theorem WLift_of_lt {n v u W e k : Nat}
    (h : IsExcursion n v u W e) (hk : 0 < k) (hlt : k < W) :
    WLift n k k := by
  have hVal := val2_peak_lift_one h hlt
  obtain ⟨e', he', hsub⟩ := hVal
  have hodd : u % 2 = 1 := h.2.1
  have hu : 0 < u := by omega
  have hge : 1 ≤ 3 ^ v * (u + 1 * 2 ^ k) :=
    one_le_three_pow_mul (Nat.add_pos_left hu _)
  have hpeak : 3 ^ v * (u + 1 * 2 ^ k) = 2 ^ k * e' + 1 :=
    (Nat.sub_eq_iff_eq_add hge).mp hsub
  exact ⟨v, u, W, e, 1, e', h, hk, excursion_of_lift h hk hpeak he'⟩

/-- The `t = 1` lift at budget `k = W` has peak valuation *strictly above* `W`. -/
theorem peak_lift_one_at_W {n v u W e : Nat} (h : IsExcursion n v u W e) :
    2 ^ (W + 1) ∣ 3 ^ v * (u + 1 * 2 ^ W) - 1 := by
  have hp := peak_of_lift (t := 1) (k := W) h
  simp only [Nat.one_mul] at hp
  have hdist : 2 ^ W * e + 3 ^ v * 2 ^ W = 2 ^ W * (e + 3 ^ v) := by
    have : 3 ^ v * 2 ^ W = 2 ^ W * 3 ^ v := Nat.mul_comm _ _
    rw [this, ← Nat.mul_add]
  have hsum : 3 ^ v * (u + 1 * 2 ^ W) - 1 = 2 ^ W * (e + 3 ^ v) := by
    simp only [Nat.one_mul]
    rw [hp, hdist]
  have heven : (e + 3 ^ v) % 2 = 0 := by
    have h3 : (3 : Nat) ^ v % 2 = 1 := three_pow_odd v
    have he : e % 2 = 1 := h.2.2.1
    omega
  obtain ⟨q, hq⟩ : ∃ q, e + 3 ^ v = 2 * q := ⟨(e + 3 ^ v) / 2, by omega⟩
  refine ⟨q, ?_⟩
  have hsucc : (2 : Nat) ^ (W + 1) = 2 * 2 ^ W := two_pow_succ W
  rw [hsum, hq, hsucc]
  simp [Nat.mul_assoc, Nat.mul_comm]

/-- **Not a singleton** whenever the budget has not overrun the true `W`. -/
theorem WLift_not_singleton {n v u W e k : Nat}
    (h : IsExcursion n v u W e) (hk : 0 < k) (hle : k ≤ W) :
    ∃ W₁ W₂ : Nat, WLift n k W₁ ∧ WLift n k W₂ ∧ W₁ ≠ W₂ := by
  rcases Nat.eq_or_lt_of_le hle with hEq | hlt
  · -- `k = W`: zero lift vs `t = 1` (strictly heavier peak).
    have hu : u % 2 = 1 := h.2.1
    have hv : 0 < v := h.2.2.2.1
    have hnk : 0 < k := hk
    let u' := u + 1 * 2 ^ k
    let n' := 2 ^ v * u' - 1
    have hn' : n' % 2 = 1 := lift_odd (t := 1) hv hu hnk
    obtain ⟨v₂, u₂, W₂, e₂, hex⟩ := exists_excursion hn'
    have hnu' : n' + 1 = 2 ^ v * u' := lift_succ (t := 1) hu
    have hu'odd : u' % 2 = 1 := odd_add_two_pow (t := 1) hu hnk
    have hvEq : v₂ = v :=
      Val2.unique (val2_succ_of hex) ⟨u', hu'odd, hnu'⟩
    have huEq : u₂ = u' := by
      have : 2 ^ v₂ * u₂ = 2 ^ v * u' :=
        (hex.2.2.2.2.2.1).symm.trans hnu'
      rw [hvEq] at this
      exact Nat.eq_of_mul_eq_mul_left (two_pow_pos v) this
    have hex' : IsExcursion n' v u' W₂ e₂ := hvEq ▸ huEq ▸ hex
    have hne : W₂ ≠ k := by
      intro hWeq
      have hexW : IsExcursion n' v u' k e₂ := hWeq ▸ hex'
      have hdiv : 2 ^ (k + 1) ∣ 3 ^ v * (u + 1 * 2 ^ k) - 1 := by
        have := peak_lift_one_at_W (hEq ▸ h)
        simpa [hEq] using this
      have hdiv' : 2 ^ (k + 1) ∣ 3 ^ v * u' - 1 := hdiv
      exact (Val2.not_dvd_succ (val2_peak_of hexW)) hdiv'
    have hliftW : WLift n k W₂ :=
      ⟨v, u, W, e, 1, e₂, h, hk, hex'⟩
    refine ⟨W, W₂, WLift_self h hk, hliftW, ?_⟩
    rw [← hEq]
    exact Ne.symm hne
  · exact ⟨k, W, WLift_of_lt h hk hlt, WLift_self h hk, Nat.ne_of_lt hlt⟩

/-- Every lift at budget `k ≤ W` has peak divisible by `2 ^ k`. -/
theorem peak_dvd_two_pow_k {n v u W e t k : Nat}
    (h : IsExcursion n v u W e) (hle : k ≤ W) :
    2 ^ k ∣ 3 ^ v * (u + t * 2 ^ k) - 1 := by
  have hp := peak_of_lift (t := t) (k := k) h
  have hW : 2 ^ k ∣ 2 ^ W * e :=
    Nat.dvd_trans (two_pow_dvd_two_pow hle) ⟨e, rfl⟩
  have hT : 2 ^ k ∣ t * (3 ^ v * 2 ^ k) :=
    ⟨t * 3 ^ v, by simp [Nat.mul_comm, Nat.mul_left_comm]⟩
  have : 2 ^ k ∣ 2 ^ W * e + t * (3 ^ v * 2 ^ k) := Nat.dvd_add hW hT
  rwa [← hp] at this

/-- **Not the free shift:** letters strictly below the budget never occur
once `k ≤ W`. -/
theorem WLift_ge_of_le {n v u W e k W' : Nat}
    (h : IsExcursion n v u W e) (hle : k ≤ W)
    (hlift : WLift n k W') : k ≤ W' := by
  obtain ⟨v₁, u₁, W₁, e₁, t, e', hex, _, hex'⟩ := hlift
  have hv : v₁ = v := excursion_v_unique hex h
  have hexv : IsExcursion n v u₁ W₁ e₁ := hv ▸ hex
  have hu : u₁ = u := excursion_u_unique hexv h
  have hexvu : IsExcursion n v u W₁ e₁ := hu ▸ hexv
  have hWeq : W₁ = W := Val2.unique (val2_peak_of hexvu) (val2_peak_of h)
  have hexW : IsExcursion n v u W e₁ := hWeq ▸ hexvu
  have he : e₁ = e := excursion_e_unique hexW h
  have hexe : IsExcursion n v u W e := he ▸ hexW
  have heq : 3 ^ v * (u + t * 2 ^ k) = 2 ^ W' * e' + 1 := by
    have : v₁ = v := hv
    have : u₁ = u := hu
    simpa [this, hv] using hex'.2.2.2.2.2.2
  have hodd : u % 2 = 1 := h.2.1
  have hupos : 0 < u := by omega
  have hge : 1 ≤ 3 ^ v * (u + t * 2 ^ k) :=
    one_le_three_pow_mul (Nat.add_pos_left hupos _)
  have hsub : 3 ^ v * (u + t * 2 ^ k) - 1 = 2 ^ W' * e' := by
    rw [heq]
    exact Nat.add_sub_cancel (2 ^ W' * e') 1
  have hdvd : 2 ^ k ∣ 2 ^ W' * e' := by
    have hdiv := peak_dvd_two_pow_k (t := t) hexe hle
    rwa [hsub] at hdiv
  have hVal : Val2 (2 ^ W' * e') W' := ⟨e', hex'.2.2.1, rfl⟩
  exact (Val2.dvd_iff_le hVal).mp hdvd

/-- **Collapse past the true `W`:** if the budget overruns `W`, every lift
has extra-halving count exactly `W`. -/
theorem WLift_unique_of_gt {n v u W e k W' : Nat}
    (h : IsExcursion n v u W e) (hgt : W < k)
    (hlift : WLift n k W') : W' = W := by
  obtain ⟨v₁, u₁, W₁, e₁, t, e', hex, hk, hex'⟩ := hlift
  have hv : v₁ = v := excursion_v_unique hex h
  have hexv : IsExcursion n v u₁ W₁ e₁ := hv ▸ hex
  have hu : u₁ = u := excursion_u_unique hexv h
  have hexvu : IsExcursion n v u W₁ e₁ := hu ▸ hexv
  have hWeq : W₁ = W := Val2.unique (val2_peak_of hexvu) (val2_peak_of h)
  have hexW : IsExcursion n v u W e₁ := hWeq ▸ hexvu
  have he : e₁ = e := excursion_e_unique hexW h
  have hexe : IsExcursion n v u W e := he ▸ hexW
  have hP : Val2 (2 ^ W * e) W := ⟨e, h.2.2.1, rfl⟩
  have hp := peak_of_lift (t := t) (k := k) hexe
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0
    have hVal : Val2 (3 ^ v * (u + 0 * 2 ^ k) - 1) W := by
      have : 3 ^ v * (u + 0 * 2 ^ k) - 1 = 2 ^ W * e := by
        simp only [Nat.zero_mul, Nat.add_zero]
        have heq : 3 ^ v * u = 2 ^ W * e + 1 := h.2.2.2.2.2.2
        rw [heq]
        exact Nat.add_sub_cancel (2 ^ W * e) 1
      rw [this]
      exact hP
    have hex't : IsExcursion (2 ^ v * (u + 0 * 2 ^ k) - 1) v
        (u + 0 * 2 ^ k) W' e' := by
      simpa [hv, hu] using hex'
    exact Val2.unique (val2_peak_of hex't) hVal
  · obtain ⟨r, hr⟩ := Val2.exists_of_pos htpos
    have hmul := Val2.mul hr (val2_three_pow_two_pow v k)
    have hrs : W < r + k := by omega
    have hadd := Val2.add_of_lt hP hmul hrs
    have hVal : Val2 (3 ^ v * (u + t * 2 ^ k) - 1) W := by
      have hsum : 2 ^ W * e + t * (3 ^ v * 2 ^ k)
          = 3 ^ v * (u + t * 2 ^ k) - 1 := hp.symm
      simpa [hsum] using hadd
    have hex't : IsExcursion (2 ^ v * (u + t * 2 ^ k) - 1) v
        (u + t * 2 ^ k) W' e' := by
      simpa [hv, hu] using hex'
    exact Val2.unique (val2_peak_of hex't) hVal


/-! ## 2.  Reverse-tree siblings of a fixed landing -/

/-- A reverse letter of the fixed landing `e`: some parent excursion-lands
on `e` with data `(v, W)`. -/
def ReverseLetter (e v W : Nat) : Prop :=
  ∃ n u : Nat, IsExcursion n v u W e

/-- **Not the free shift.**  `(1, 1)` is not a reverse letter of `5`. -/
theorem five_blocks_one_one : ¬ ReverseLetter 5 1 1 := by
  intro ⟨_, u, h⟩
  have : 3 * u = 2 * 5 + 1 := h.2.2.2.2.2.2
  omega

theorem thirteen_v_one : ReverseLetter 13 1 1 :=
  ⟨17, 9, ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩⟩

theorem thirteen_v_two : ReverseLetter 13 2 1 :=
  ⟨11, 3, ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩⟩

theorem thirteen_v_three : ReverseLetter 13 3 1 :=
  ⟨7, 1, seven_first_excursion⟩

/-- **Not a singleton:** three `v`-lifts at one node of one landing. -/
theorem thirteen_rank_ge_three :
    ReverseLetter 13 1 1 ∧ ReverseLetter 13 2 1 ∧ ReverseLetter 13 3 1 :=
  ⟨thirteen_v_one, thirteen_v_two, thirteen_v_three⟩

/-- A reverse letter forces `3 ^ v ≤ 2 ^ W e + 1`, so rank at a fixed `W`
is finite. -/
theorem v_bounded_of_letter {e v W : Nat} (h : ReverseLetter e v W) :
    3 ^ v ≤ 2 ^ W * e + 1 := by
  obtain ⟨_, u, hex⟩ := h
  have hodd : u % 2 = 1 := hex.2.1
  have hu : 1 ≤ u := by omega
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := hex.2.2.2.2.2.2
  have : 3 ^ v * 1 ≤ 3 ^ v * u := Nat.mul_le_mul_left _ hu
  have hle : 3 ^ v ≤ 3 ^ v * u := by simpa using this
  rw [hpeak] at hle
  exact hle

/-- At `n = 13`, `W = 1` the three `v`-lifts are the only ones. -/
theorem thirteen_rank_eq_three {v : Nat} (h : ReverseLetter 13 v 1) :
    v = 1 ∨ v = 2 ∨ v = 3 := by
  have hb := v_bounded_of_letter h
  have h27 : (3 : Nat) ^ v ≤ 27 := by simpa using hb
  have hpos : 0 < v := by
    obtain ⟨_, _, hex⟩ := h
    exact hex.2.2.2.1
  have hlt : v < 4 := by
    rcases Nat.lt_or_ge v 4 with hlt | hge
    · exact hlt
    · have hpow := three_pow_le_three_pow hge
      have h4 : (3 : Nat) ^ 4 = 81 := by decide
      omega
  omega

/-- A multiple of three has no odd reverse letter. -/
theorem no_letter_of_three_dvd {e v W : Nat} (h3 : e % 3 = 0) :
    ¬ ReverseLetter e v W := by
  intro ⟨_, u, hex⟩
  have hv : 0 < v := hex.2.2.2.1
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := hex.2.2.2.2.2.2
  have hL : (3 ^ v * u) % 3 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, v = j + 1 := ⟨v - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ j), Nat.mul_assoc]
    simp
  have hR : (2 ^ W * e + 1) % 3 = 1 := by
    have : (2 ^ W * e) % 3 = 0 := by
      rw [Nat.mul_mod, h3]
      simp
    omega
  omega

/-- Reverse paths from a fixed landing, nested by prefix. -/
inductive ReversePath : Nat → List (Nat × Nat) → Nat → Prop where
  | nil (n : Nat) : ReversePath n [] n
  | cons {e v u W n : Nat} {ws : List (Nat × Nat)} {m : Nat} :
      IsExcursion n v u W e →
        ReversePath n ws m →
          ReversePath e ((v, W) :: ws) m

def ReverseCone (n k : Nat) (ws : List (Nat × Nat)) : Prop :=
  ws.length = k ∧ ∃ m : Nat, ReversePath n ws m

/-- Concatenation of reverse paths. -/
theorem ReversePath_concat {n m p : Nat} {ws ws' : List (Nat × Nat)}
    (h : ReversePath n ws m) (h' : ReversePath m ws' p) :
    ReversePath n (ws ++ ws') p := by
  induction h with
  | nil n => simpa using h'
  | @cons e v u W n₀ ws₀ m₀ hex hp ih =>
    exact ReversePath.cons hex (ih h')

/-- Split off a last reverse letter. -/
theorem ReversePath_of_snoc {n p v W : Nat} {ws : List (Nat × Nat)}
    (h : ReversePath n (ws ++ [(v, W)]) p) :
    ∃ m u : Nat, ReversePath n ws m ∧ IsExcursion p v u W m := by
  induction ws generalizing n with
  | nil =>
    simp only [List.nil_append] at h
    cases h with
    | cons hex hp =>
      cases hp
      exact ⟨n, _, ReversePath.nil n, hex⟩
  | cons letter rest ih =>
    simp only [List.cons_append] at h
    cases h with
    | cons hex hp =>
      obtain ⟨anc, u₀, hm, hex'⟩ := ih hp
      exact ⟨anc, u₀, ReversePath.cons hex hm, hex'⟩

/-- **Nested by prefix.** -/
theorem ReverseCone_nested {n v W k : Nat} {ws : List (Nat × Nat)}
    (h : ReverseCone n (k + 1) ((v, W) :: ws)) :
    ∃ n' : Nat, ReverseCone n 1 [(v, W)] ∧ ReverseCone n' k ws := by
  obtain ⟨hlen, m, hp⟩ := h
  cases hp with
  | cons hex hp' =>
    have hlenws : ws.length = k := by
      simp at hlen
      exact hlen
    refine ⟨_, ⟨rfl, _, ReversePath.cons hex (ReversePath.nil _)⟩,
      hlenws, m, hp'⟩

/-- Depth-one cone membership is a reverse letter. -/
theorem ReverseCone_one_iff {n v W : Nat} :
    ReverseCone n 1 [(v, W)] ↔ ReverseLetter n v W := by
  constructor
  · intro ⟨_, m, hp⟩
    cases hp with
    | cons hex _ =>
      exact ⟨_, _, hex⟩
  · intro ⟨n', u, hex⟩
    exact ⟨rfl, n', ReversePath.cons hex (ReversePath.nil n')⟩


/-! ## 3.  Realization coordinate `Q` -/

/-- After a reverse prefix from the fixed landing `n`, the current ancestor
is `m`. -/
def Q (n : Nat) (pref : List (Nat × Nat)) (m : Nat) : Prop :=
  ReversePath n pref m

/-- Same reverse letter, same parent. -/
theorem parent_eq_of_letter {n n' v u u' W e : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion n' v u' W e) : n = n' := by
  have hu : u' = u := by
    have h1 := h.2.2.2.2.2.2
    have h2 := h'.2.2.2.2.2.2
    exact Nat.eq_of_mul_eq_mul_left (three_pow_pos v) (h2.trans h1.symm)
  have hsucc : n' + 1 = n + 1 := by
    have h1 := h.2.2.2.2.2.1
    have h2 := h'.2.2.2.2.2.1
    rw [hu] at h2
    exact h2.trans h1.symm
  omega

theorem Q_unique {n m m' : Nat} {pref : List (Nat × Nat)}
    (h : Q n pref m) (h' : Q n pref m') : m = m' := by
  induction h generalizing m' with
  | nil n =>
    cases h'
    rfl
  | cons hex hp ih =>
    cases h' with
    | cons hex₂ hp₂ =>
      have hpar := parent_eq_of_letter hex hex₂
      exact ih (hpar ▸ hp₂)

/-- **`Q` records the constraint on the next reverse letter.** -/
theorem Q_constrains_future {n m v W : Nat} {pref : List (Nat × Nat)}
    (hQ : Q n pref m) :
    ReverseLetter m v W ↔
      ∃ n' : Nat, ReversePath n (pref ++ [(v, W)]) n' := by
  constructor
  · intro ⟨p, u, hex⟩
    exact ⟨p, ReversePath_concat hQ (ReversePath.cons hex (ReversePath.nil p))⟩
  · intro ⟨n', hp⟩
    obtain ⟨m', u, hm, hex⟩ := ReversePath_of_snoc hp
    have : m' = m := Q_unique hm hQ
    subst this
    exact ⟨n', u, hex⟩

end DeviceFutureCone
end Collatz

section AxiomAudit
open Collatz.DeviceFutureCone
#print axioms WLift_nested
#print axioms WLift_not_singleton
#print axioms WLift_ge_of_le
#print axioms WLift_unique_of_gt
#print axioms five_blocks_one_one
#print axioms thirteen_rank_eq_three
#print axioms no_letter_of_three_dvd
#print axioms Q_constrains_future
end AxiomAudit
