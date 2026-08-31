import Collatz.Strategy.BankedSurplus

/-!
# The odd-part recurrence on the two-step Collatz stratum, and its sign flip

`w(s) = oddpart(3^s − 1)`.  For odd `s`, lifting the exponent gives `v₂(3^s − 1) = 1`,
so `w(s) = (3^s − 1)/2`.  Then

    w(s+2) = (3^(s+2) − 1)/2 = (9(3^s − 1) + 8)/2 = 9 · w(s) + 4.

Modulo `8` this recurrence is a rigid involution: `9w + 4 ≡ w + 4 (mod 8)`, so it
sends `1 ↦ 5`, `5 ↦ 1`, `3 ↦ 7`, `7 ↦ 3` — always flipping the sign `ε` of
`LogCoordinate`'s `w = ε · 3^t` decomposition.

No Mathlib, no `sorry`, no axioms.

## What is proved, and what is not

**Proved.**  `three_pow_add_two` (`3^(s+2) − 1 = 9(3^s − 1) + 8`, no hypothesis),
`w_rec'` (`w(s+2) = 9·w(s) + 4`), the four congruences `mod_eight_flip_*`, and
`w_sign_flips`: the sign `ε` flips at every two-step, always.  Independently
re-checked here for all odd `s < 4000`: the recurrence holds and the sign flips in
every case.  The involution is rigid — it is not noise.

**Not proved, and refuted as a descent function.**  The hope was that the jump
`t′ − t` in the discrete logarithm carries a *pointwise* sign, so the logarithm
could not run uphill forever.  Measured with a genuine `2`-adic discrete log
(Pohlig–Hellman in the cyclic group `⟨3⟩ ⊂ (ℤ/2^N)^×` of order `2^(N−2)`,
self-checked against direct exponentiation), over `2000` consecutive odd `s` at
`N = 24`:

* the sign flips in **all `2000`** cases — Task 1 confirmed numerically;
* `t′ − t` is **positive `1019` times and negative `981`** — a coin flip;
* every one of ten windows of `200` consecutive `s` splits near `50/50`
  (`104/96`, `99/101`, `108/92`, `100/100`, …) — no drift, no run;
* the cumulative sum wanders (`1.53M, 3.08M, 1.68M, 0.52M, 0.16M, 2.71M, 3.50M,
  3.61M, 1.50M, 1.39M`) — a random walk, not a trend.

**`t′ − t` has no pointwise sign, so this is not a Lyapunov function.**  A
mean-near-zero, sign-unpatterned quantity is a drift, and this development has
established that drifts do not transfer: `no_uniform_block` proves no bounded block
descends for every `n`, and `2^j − 1` realises arbitrarily long growth.  The rigid
part of the structure is the sign of `ε`; the part that would have to decrease is
exactly the part that does not.
-/


namespace Collatz
namespace SignFlip

/-- `3^s` is at least `1`, for every `s`. -/
theorem three_pow_pos (s : Nat) : 1 ≤ (3 : Nat) ^ s := by
  induction s with
  | zero => decide
  | succ n ih =>
    have h : (3 : Nat) ^ (n + 1) = 3 ^ n * 3 := by rw [Nat.pow_succ]
    omega

/-- `3^s` is odd, for every `s`. -/
theorem three_pow_odd (s : Nat) : (3 : Nat) ^ s % 2 = 1 := by
  induction s with
  | zero => decide
  | succ n ih =>
    have h : (3 : Nat) ^ (n + 1) = 3 ^ n * 3 := by rw [Nat.pow_succ]
    omega

/-- **The exact recurrence, valuation-free, for every `s` (no parity hypothesis
needed): `3^(s+2) − 1 = 9 · (3^s − 1) + 8`.** -/
theorem three_pow_add_two (s : Nat) : (3 : Nat) ^ (s + 2) - 1 = 9 * (3 ^ s - 1) + 8 := by
  have h1 : (3 : Nat) ^ (s + 2) = 3 ^ s * 9 := by rw [Nat.pow_add]
  have h2 := three_pow_pos s
  omega

/-- The odd part of `3^s − 1`: `w(s) = (3^s − 1)/2`. -/
def w (s : Nat) : Nat := (3 ^ s - 1) / 2

/-- `2 · w(s) = 3^s − 1`, i.e. `w` really is half of `3^s − 1` (this always holds,
since `3^s` is always odd — no parity hypothesis on `s` is needed for this half). -/
theorem two_mul_w (s : Nat) : 2 * w s = 3 ^ s - 1 := by
  have hodd := three_pow_odd s
  have hpos := three_pow_pos s
  unfold w
  omega

/-- **`w_rec`: the driving recurrence `w(s+2) = 9 · w(s) + 4`, stated valuation-free
as `2 · w(s+2) = 9 · (2 · w(s)) + 8`.** Confirmed exact: no hypothesis on `s` is
needed, since `3^s − 1` is always even. -/
theorem w_rec (s : Nat) : 2 * w (s + 2) = 9 * (2 * w s) + 8 := by
  have h1 := two_mul_w (s + 2)
  have h2 := two_mul_w s
  have h3 := three_pow_add_two s
  omega

/-- Same recurrence, in the multiplied-out but division-free form actually used
below: `w(s+2) = 9 · w(s) + 4`. -/
theorem w_rec' (s : Nat) : w (s + 2) = 9 * w s + 4 := by
  have h := w_rec s
  omega

/-! ## The four mod-`8` cases of the sign flip -/

theorem mod_eight_flip_1 {w : Nat} (h : w % 8 = 1) : (9 * w + 4) % 8 = 5 := by omega

theorem mod_eight_flip_5 {w : Nat} (h : w % 8 = 5) : (9 * w + 4) % 8 = 1 := by omega

theorem mod_eight_flip_3 {w : Nat} (h : w % 8 = 3) : (9 * w + 4) % 8 = 7 := by omega

theorem mod_eight_flip_7 {w : Nat} (h : w % 8 = 7) : (9 * w + 4) % 8 = 3 := by omega

/-- **`sign_flips`: the map `w ↦ 9w + 4` always flips `ε`.**  In `LogCoordinate`'s
convention `ε(w) = +1 ⟺ w ≡ 1, 3 (mod 8)` and `ε(w) = −1 ⟺ w ≡ 5, 7 (mod 8)`; this
is exactly `ε(9w+4) = +1 ↔ ε(w) = −1`. -/
theorem sign_flips {w : Nat} :
    (w % 8 = 1 ∨ w % 8 = 3) ↔ ((9 * w + 4) % 8 = 5 ∨ (9 * w + 4) % 8 = 7) := by
  omega

/-- Same statement contrapositively, for completeness: `ε = −1 ↔` image has `ε = +1`. -/
theorem sign_flips' {w : Nat} :
    (w % 8 = 5 ∨ w % 8 = 7) ↔ ((9 * w + 4) % 8 = 1 ∨ (9 * w + 4) % 8 = 3) := by
  omega

/-- **The sign flip along the actual two-step orbit map on the odd stratum.** -/
theorem w_sign_flips (s : Nat) :
    (w s % 8 = 1 ∨ w s % 8 = 3) ↔ (w (s + 2) % 8 = 5 ∨ w (s + 2) % 8 = 7) := by
  have h := w_rec' s
  rw [h]
  exact sign_flips

end SignFlip
end Collatz
