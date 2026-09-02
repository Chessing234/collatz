import Collatz.Strategy.RunLengthUnbounded
import Collatz.Strategy.LiftExponentThree

/-!
# Toward every run length: the arithmetic the general family needs

`Strategy.RunLengthUnbounded` shows no tail depending only on the run length can
work, by exhibiting arbitrarily slow descents at run length exactly `2`.  The
same construction should run at every `j ≥ 2`:

take `n = 2^j·d − 1` with `d` odd, so `v₂(n+1) = j`; `ScaleLadder.climb` gives
`T^j(n) = 3^j·d − 1`; and choosing `d` with `3^j·d = 2^(k+1) − 1` makes that
`2(2^k − 1)`, so one further halving lands exactly on `2^k − 1`, which climbs to
`3^k − 1`.

This file collects the arithmetic that construction needs.  Each piece is
independently useful; the assembly is not yet done.

* `three_pow_dvd` — `3^(i+1) ∣ 2^(2·3^i·m) − 1` for **every** `m`, which is what
  makes `k` unbounded and hence the descent time unbounded.  It combines
  `LiftExponentThree.two_pow_three_pow` with `pow_congr_one`.
* `two_pow_lt_three_pow` — `2^(j+1) < 3^j` for `j ≥ 2`.  This is exactly the
  inequality `n < 2^k − 1` reduces to, and it is why the construction starts at
  `j = 2`: at `j = 1` it fails, matching the genuine exception there
  (`σ = 2` always, `Structure.CycleMinClass.two_step_descent`).
* `climb_gen` — the climb with a general odd multiplier, giving every
  intermediate value `3^t·2^(j−t)·d − 1`, each of which is at least the start.
-/

namespace Collatz
namespace RunLengthAny

open LiftExponentThree RunLengthUnbounded

/-- Congruence to `1` survives powering: if `A ≡ 1 (mod M)` then `A^m ≡ 1`. -/
theorem pow_congr_one (M c : Nat) : ∀ m : Nat, ∃ d : Nat, (M * c + 1) ^ m = M * d + 1 := by
  intro m
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨M * d * c + d + c, ?_⟩
    rw [Nat.pow_succ, hd]
    simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    omega

/-- **`3^(i+1)` divides `2^(2·3^i·m) − 1` for every `m`.**  The free parameter
`m` is what makes the peak exponent — and so the descent time — unbounded. -/
theorem three_pow_dvd (i m : Nat) : ∃ d : Nat, 2 ^ (2 * 3 ^ i * m) = 3 ^ (i + 1) * d + 1 := by
  obtain ⟨c, hc⟩ := two_pow_three_pow i
  rw [show (2:Nat) ^ (2 * 3 ^ i * m) = (2 ^ (2 * 3 ^ i)) ^ m from by rw [← Nat.pow_mul], hc]
  exact pow_congr_one _ c m

/-- **`2^(j+1) < 3^j` for `j ≥ 2`.**  The construction's one inequality reduces
to this, which is why it begins at `j = 2`. -/
theorem two_pow_lt_three_pow : ∀ i : Nat, 2 ^ (i + 2 + 1) < 3 ^ (i + 2) := by
  intro i
  induction i with
  | zero => decide
  | succ i ih =>
    have h2 : (2 : Nat) ^ (i + 1 + 2 + 1) = 2 ^ (i + 2 + 1) * 2 := by
      rw [show i + 1 + 2 + 1 = (i + 2 + 1) + 1 from by omega]
      exact Nat.pow_succ _ _
    have h3 : (3 : Nat) ^ (i + 1 + 2) = 3 ^ (i + 2) * 3 := by
      rw [show i + 1 + 2 = (i + 2) + 1 from by omega]
      exact Nat.pow_succ _ _
    omega

/-- The climb with a general odd multiplier: every intermediate value of the
opening run from `2^j·d − 1`. -/
theorem climb_gen (j t d : Nat) (htj : t ≤ j) (hd : 0 < d) :
    acceleratedOrbit t (2 ^ j * d - 1) = 3 ^ t * (2 ^ (j - t) * d) - 1 := by
  have hsplit : (2:Nat) ^ j * d = 2 ^ t * (2 ^ (j - t) * d) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [hsplit]
  exact ScaleLadder.climb t (2 ^ (j - t) * d) (Nat.mul_pos (Nat.pow_pos (by omega)) hd)

/-- Each intermediate value of that run is at least the start. -/
theorem climb_gen_ge (j t d : Nat) (htj : t ≤ j) (hd : 0 < d) :
    2 ^ j * d - 1 ≤ acceleratedOrbit t (2 ^ j * d - 1) := by
  rw [climb_gen j t d htj hd]
  have hmono : (2:Nat) ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by omega) _
  have hsplit : (2:Nat) ^ j = 2 ^ t * 2 ^ (j - t) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hstep : (2:Nat) ^ t * (2 ^ (j - t) * d) ≤ 3 ^ t * (2 ^ (j - t) * d) :=
    Nat.mul_le_mul_right _ hmono
  have hrw : (2:Nat) ^ j * d = 2 ^ t * (2 ^ (j - t) * d) := by
    rw [← Nat.mul_assoc, ← hsplit]
  omega

/-! ## The general family

Everything above assembles into the statement that the tail fails at every run
length `j ≥ 2`, not merely at `j = 2`. -/

/-- The start `2^j·d − 1` lies below the landing point `2^k − 1`.  Stated in
plain variables: `omega`'s special handling of `2 ^ ·` interferes badly once
several powers are in scope. -/
theorem start_lt_landing {P Q X d : Nat} (hQ : Q * d = X * 2 - 1)
    (hlt : 2 * P < Q) (hX : 0 < X) (hQpos : 0 < Q) : P * d < X := by
  have e1 : Q * (P * d) = P * X * 2 - P := by
    rw [Nat.mul_left_comm, hQ, Nat.mul_sub, Nat.mul_one, ← Nat.mul_assoc]
  have h6 : P * X * 2 = 2 * (P * X) := by rw [Nat.mul_comm (P * X) 2]
  have h4 : 2 * (P * X) ≤ Q * X - X := by
    calc 2 * (P * X) = 2 * P * X := by rw [Nat.mul_assoc]
      _ ≤ (Q - 1) * X := Nat.mul_le_mul_right _ (by omega)
      _ = Q * X - X := by rw [Nat.sub_mul, Nat.one_mul]
  have hQX : X ≤ Q * X := Nat.le_mul_of_pos_left _ hQpos
  have h7 : Q * (P * d) < Q * X := by rw [e1]; omega
  exact Nat.lt_of_mul_lt_mul_left h7

/-- **No tail suffices at any run length `j ≥ 2`.**  For every `j = i + 2` and
every bound `B` there is an `n` with `v₂(n+1) = j` exactly — so run length `j` —
whose orbit has still not descended after `B` steps.

With `Structure.CycleMinClass.two_step_descent` covering `j = 1` positively
(`σ = 2` always), this settles the question completely: the run length controls
the descent time only at `j = 1`. -/
theorem no_tail_at_any_run_length (i B : Nat) :
    ∃ n d : Nat, d % 2 = 1 ∧ n + 1 = 2 ^ (i + 2) * d ∧ n ≤ acceleratedOrbit B n := by
  obtain ⟨d, hd⟩ := three_pow_dvd (i + 1) (B + 1)
  have h3pos : 1 ≤ (3:Nat) ^ (i + 1) := Nat.one_le_pow _ _ (by omega)
  have h3ge : 3 ≤ (3:Nat) ^ (i + 1) := by
    calc (3:Nat) = 3 ^ 1 := by decide
      _ ≤ 3 ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, 2 * 3 ^ (i + 1) * (B + 1) = k + 1 := by
    refine ⟨2 * 3 ^ (i + 1) * (B + 1) - 1, ?_⟩
    have : 6 ≤ 2 * 3 ^ (i + 1) * (B + 1) := by
      have := Nat.mul_le_mul_left 2 h3ge
      have h2 : 2 * 3 ^ (i + 1) * 1 ≤ 2 * 3 ^ (i + 1) * (B + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  rw [hk] at hd
  have hkB : B ≤ k := by
    have h2 : 2 * 3 ^ (i + 1) * (B + 1) ≥ 6 * (B + 1) := by
      have : 6 * (B + 1) = 2 * 3 * (B + 1) := by omega
      rw [this]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h3ge)
    omega
  have hpow : (2:Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ _ _
  have hXpos : 0 < (2:Nat) ^ k := Nat.pow_pos (by omega)
  have hQpos : 0 < (3:Nat) ^ (i + 2) := Nat.pow_pos (by omega)
  rw [hpow] at hd
  have hQd : 3 ^ (i + 2) * d = 2 ^ k * 2 - 1 := Nat.eq_sub_of_add_eq hd.symm
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · rw [Nat.mul_zero] at hQd; omega
    · exact h
  have hdodd : d % 2 = 1 := by
    rcases Nat.eq_zero_or_pos (d % 2) with he | ho
    · exfalso
      obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
      have hmul : 3 ^ (i + 2) * (2 * e) = 2 * (3 ^ (i + 2) * e) := by
        rw [Nat.mul_left_comm]
      omega
    · omega
  have hnpos : 0 < 2 ^ (i + 2) * d := Nat.mul_pos (Nat.pow_pos (by omega)) hdpos
  have hlow : 2 ^ (i + 2) * d - 1 < 2 ^ k - 1 := by
    have hlt2 : 2 * 2 ^ (i + 2) < 3 ^ (i + 2) := by
      have h := two_pow_lt_three_pow i
      have he : (2:Nat) ^ (i + 2 + 1) = 2 ^ (i + 2) * 2 := Nat.pow_succ _ _
      omega
    have := start_lt_landing (P := 2 ^ (i + 2)) (Q := 3 ^ (i + 2)) (X := 2 ^ k) (d := d)
      hQd hlt2 hXpos hQpos
    omega
  refine ⟨2 ^ (i + 2) * d - 1, d, hdodd, by omega, ?_⟩
  -- the peak arrives at time (i+2)+1+k; B is at most that
  have hstep3 : acceleratedOrbit (i + 2) (2 ^ (i + 2) * d - 1) = 3 ^ (i + 2) * d - 1 := by
    have := climb_gen (i + 2) (i + 2) d (by omega) hdpos
    simpa using this
  have hland : acceleratedOrbit (i + 2 + 1) (2 ^ (i + 2) * d - 1) = 2 ^ k - 1 := by
    rw [show i + 2 + 1 = 1 + (i + 2) from by omega, ← acceleratedOrbit_add, hstep3, hQd]
    show acceleratedStep (2 ^ k * 2 - 1 - 1) = 2 ^ k - 1
    rw [acceleratedStep, if_pos (by omega)]
    omega
  rcases Nat.lt_or_ge B (i + 2 + 1) with hsmall | hbig
  · exact climb_gen_ge (i + 2) B d (by omega) hdpos
  · obtain ⟨s, rfl⟩ : ∃ s, B = i + 2 + 1 + s := ⟨B - (i + 2 + 1), by omega⟩
    rw [show i + 2 + 1 + s = s + (i + 2 + 1) from by omega, ← acceleratedOrbit_add, hland,
        climb_mid k s (by omega)]
    have hmono : (2:Nat) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by omega) _
    have hsplit : (2:Nat) ^ k = 2 ^ s * 2 ^ (k - s) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hge : (2:Nat) ^ k ≤ 3 ^ s * 2 ^ (k - s) := by
      calc (2:Nat) ^ k = 2 ^ s * 2 ^ (k - s) := hsplit
        _ ≤ 3 ^ s * 2 ^ (k - s) := Nat.mul_le_mul_right _ hmono
    omega

end RunLengthAny
end Collatz
