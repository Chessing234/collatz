import Collatz.Strategy.HeavyState

/-!
# No ranking function on a finite quotient can decrease

A recurring proposal is to prove termination by exhibiting a rank: a function of
`x` that is constant on residue classes modulo some fixed modulus and strictly
decreases every `L` steps.  Linear-programming searches over such ranks — with
`log x`, `v₂(x)`, `v₂(x+1)`, `v₂(3x+1)` and the classes modulo `2 ^ 8` and `3 ^ 3`
all thrown in — return an optimal margin of exactly zero, at every window length
`L = 1 … 8` and at every modulus tried up to `2 ^ 14 · 3 ^ 4`.

Zero, rather than something small, is the signature of an exact obstruction, and
there is one.  This file proves it.

## The returning family

Take any moduli `2 ^ k` and `3 ^ l`, any window length `L ≥ 1`, and set

`n + 1 = 2 ^ (k + L) · 3 ^ l · s`.

Then `2 ^ L ∣ n + 1`, so the next `L` steps are all odd (`OddRuns.oddRun_iff`),
and the run identity `2 ^ L (T^L(n) + 1) = 3 ^ L (n + 1)` evaluates exactly:

**`T^L(n) + 1 = 3 ^ L · 2 ^ k · 3 ^ l · s`**   (`heavy_return_value`).

Compare the two endpoints.  Both `n + 1` and `T^L(n) + 1` are divisible by
`2 ^ k` and by `3 ^ l`, so `n` and `T^L(n)` lie in the *same* class modulo each
(`heavy_return_congr`) — both are `−1`.  But `3 ^ L > 2 ^ L`, so

`T^L(n) > n`   (`heavy_return_grows`).

The state returns; the value grows.  That is a positive-weight cycle in the
quotient, and it exists at every resolution because `−1` is a fixed point of the
2-adic and 3-adic dynamics alike.  Raising the modulus does not remove it, it
only raises the smallest witness `s`.

## The consequence

Any `φ` constant on classes modulo `2 ^ k` and `3 ^ l` takes the same value at
`n` and at `T^L(n)`, so it cannot strictly decrease
(`no_class_ranking`).  The obstruction is not a resolution problem to be beaten
with a larger modulus: it is permanent.

This is the combinatorial face of the result recorded analytically in `Mirror`.
There the point was that every elementary tool is blind to the sign of the
orbit; here it is that every finite quotient retains the negative fixed point.
`HeavyState.full_density_size` is the only thing in the development that
separates them, and it does so by size — `2 ^ k ≤ x + 1` — not by congruence.
-/

namespace Collatz
namespace NoFiniteRanking

open Reach Congruence NeverDrops OddRuns

/-! ## Being `−1` modulo `d` -/

/-- If `d` divides `x + 1` then `x` is `−1` modulo `d`. -/
theorem pred_mod_of_dvd {d x : Nat} (hd : 0 < d) (h : d ∣ (x + 1)) :
    x % d = d - 1 := by
  obtain ⟨c, hc⟩ := h
  have hpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.mul_zero] at hc; omega
    · exact h0
  obtain ⟨e, he⟩ : ∃ e : Nat, c = e + 1 := ⟨c - 1, by omega⟩
  have hx : x = d - 1 + d * e := by
    rw [he, Nat.mul_add, Nat.mul_one] at hc
    omega
  rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-! ## The returning family -/

/-- **The exact value after the run.**  If `n + 1 = 2 ^ (k+L) · M` then the next
`L` steps are all odd and `T^L(n) + 1 = 3 ^ L · 2 ^ k · M`. -/
theorem heavy_return_value {k L M n : Nat} (hn : n + 1 = 2 ^ (k + L) * M) :
    acceleratedOrbit L n + 1 = 3 ^ L * (2 ^ k * M) := by
  have hsplit : (2:Nat) ^ (k + L) * M = 2 ^ L * (2 ^ k * M) := by
    rw [Nat.pow_add, Nat.mul_comm ((2:Nat) ^ k) ((2:Nat) ^ L), Nat.mul_assoc]
  have hdvd : 2 ^ L ∣ (n + 1) := ⟨2 ^ k * M, by rw [hn, hsplit]⟩
  have hrun : OddRun n L := (oddRun_iff L n).mpr hdvd
  have hval : 2 ^ L * (acceleratedOrbit L n + 1) = 3 ^ L * (n + 1) :=
    RunValue.oddRun_value L n hrun
  rw [hn, hsplit, ← Nat.mul_assoc, Nat.mul_comm ((3:Nat) ^ L) ((2:Nat) ^ L),
    Nat.mul_assoc] at hval
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hval

/-- **The state returns.**  Both endpoints are `−1` modulo `2 ^ k` and modulo
`3 ^ l`, so no finite quotient at those moduli can tell them apart. -/
theorem heavy_return_congr {k L l s n : Nat} (hs : 0 < s)
    (hn : n + 1 = 2 ^ (k + L) * (3 ^ l * s)) :
    n % 2 ^ k = acceleratedOrbit L n % 2 ^ k ∧
    n % 3 ^ l = acceleratedOrbit L n % 3 ^ l := by
  have hval := heavy_return_value hn
  have h2 : (0:Nat) < 2 ^ k := Nat.pow_pos (by omega)
  have h3 : (0:Nat) < 3 ^ l := Nat.pow_pos (by omega)
  have hn2 : 2 ^ k ∣ (n + 1) := ⟨2 ^ L * (3 ^ l * s), by
    rw [hn, Nat.pow_add, Nat.mul_assoc]⟩
  have hn3 : 3 ^ l ∣ (n + 1) := ⟨2 ^ (k + L) * s, by
    rw [hn]; simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]⟩
  have hv2 : 2 ^ k ∣ (acceleratedOrbit L n + 1) := ⟨3 ^ L * (3 ^ l * s), by
    rw [hval]; simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]⟩
  have hv3 : 3 ^ l ∣ (acceleratedOrbit L n + 1) := ⟨3 ^ L * (2 ^ k * s), by
    rw [hval]; simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]⟩
  exact ⟨by rw [pred_mod_of_dvd h2 hn2, pred_mod_of_dvd h2 hv2],
         by rw [pred_mod_of_dvd h3 hn3, pred_mod_of_dvd h3 hv3]⟩

/-- **The value grows.**  `3 ^ L > 2 ^ L`, so the return happens strictly higher
up. -/
theorem heavy_return_grows {k L M n : Nat} (hL : 0 < L) (hM : 0 < M)
    (hn : n + 1 = 2 ^ (k + L) * M) : n < acceleratedOrbit L n := by
  have hval := heavy_return_value hn
  have hlt : (2:Nat) ^ L < 3 ^ L := RunValue.two_pow_lt_three_pow L hL
  have hk : (0:Nat) < 2 ^ k := Nat.pow_pos (by omega)
  have hsplit : (2:Nat) ^ (k + L) * M = 2 ^ L * (2 ^ k * M) := by
    rw [Nat.pow_add, Nat.mul_comm ((2:Nat) ^ k) ((2:Nat) ^ L), Nat.mul_assoc]
  have hmono : (2:Nat) ^ L * (2 ^ k * M) < 3 ^ L * (2 ^ k * M) :=
    Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_refl _) (Nat.mul_pos hk hM)
  rw [hsplit] at hn
  omega

/-! ## The impossibility -/

/-- **No rank constant on a finite quotient can decrease.**  For every pair of
moduli `2 ^ k`, `3 ^ l` and every window length `L ≥ 1`, a function determined by
those two residues takes equal values at `n` and `T^L(n)` for the returning
family, so it cannot strictly decrease along windows. -/
theorem no_class_ranking (k l L : Nat) (hL : 0 < L) (φ : Nat → Nat)
    (hclass : ∀ x y : Nat, x % 2 ^ k = y % 2 ^ k → x % 3 ^ l = y % 3 ^ l → φ x = φ y) :
    ¬ (∀ x : Nat, 0 < x → φ (acceleratedOrbit L x) < φ x) := by
  intro hdec
  obtain ⟨n, hn⟩ : ∃ n : Nat, n + 1 = 2 ^ (k + L) * (3 ^ l * 1) :=
    ⟨2 ^ (k + L) * (3 ^ l * 1) - 1, by
      have h1 : (1:Nat) ≤ 2 ^ (k + L) := Nat.one_le_two_pow
      have h2 : (1:Nat) ≤ 3 ^ l * 1 := by
        have := Nat.pow_pos (n := l) (show 0 < 3 by omega); omega
      have : (1:Nat) ≤ 2 ^ (k + L) * (3 ^ l * 1) := Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        rcases Nat.mul_eq_zero.mp hz with h | h <;> omega)
      omega⟩
  obtain ⟨hc2, hc3⟩ := heavy_return_congr (s := 1) (by omega) hn
  have hgrow : n < acceleratedOrbit L n :=
    heavy_return_grows hL (by
      have := Nat.pow_pos (n := l) (show 0 < 3 by omega); omega) hn
  have hpos : 0 < n := by
    have hL2 : (2:Nat) ^ (k + L) = 2 ^ k * 2 ^ L := Nat.pow_add 2 k L
    have h2L : (2:Nat) ^ 1 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hL
    have hk1 : (1:Nat) ≤ 2 ^ k := Nat.one_le_two_pow
    have h3 : (1:Nat) ≤ 3 ^ l * 1 := by
      have := Nat.pow_pos (n := l) (show 0 < 3 by omega); omega
    have hbig : (2:Nat) ≤ 2 ^ (k + L) := by
      rw [hL2]
      calc (2:Nat) = 1 * 2 ^ 1 := by decide
        _ ≤ 2 ^ k * 2 ^ L := Nat.mul_le_mul hk1 h2L
    have : (2:Nat) ≤ 2 ^ (k + L) * (3 ^ l * 1) :=
      Nat.le_trans hbig (Nat.le_mul_of_pos_right _ (by omega))
    omega
  have heq : φ (acceleratedOrbit L n) = φ n := hclass _ _ hc2.symm hc3.symm
  have := hdec n hpos
  omega

end NoFiniteRanking
end Collatz
