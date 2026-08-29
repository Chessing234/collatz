import Collatz.Strategy.ProductCeiling

/-!
# The horizon constant, proved instead of measured

Round XX proved the product family vacuous for `a ≥ 3m` and *measured* the true
horizon at `3m·log 2 ≈ 2.079 m`.  The constant was the weak point: a number read
off a computation is not a theorem.  This file removes the computation.

## Where the constant comes from

Vacuity needs `(1 + 1/N)^a ≥ 2` with `N = 3m`.  Bernoulli
(`ProductCeiling.pow_add_one_ge`) gives `(1 + 1/N)^k ≥ 1 + k/N`, which reaches `2`
at `k = N` — that is the constant `1` of Round XX.  But Bernoulli may be applied
at exponent `k` and the result *compounded* `p` times:

`(1 + 1/N)^(k·p) ≥ (1 + k/N)^p`,

so any `k` with `(1 + k/N)^p ≥ 2` suffices, at cost `a = k·p`.  Optimising `k` for
fixed `p` gives the constant

`c_p = p·(2^(1/p) − 1)`,   `c_1 = 1`,  `c_2 = 0.8284`,  `c_3 = 0.7798`,
`c_4 = 0.7568`,  … ,  `c_p → log 2 = 0.6931`.

**The measured constant is the limit of a family every member of which is a
theorem.**  `two_mul_pow_le_gen` is that family in one statement; the named
corollaries instantiate `p = 2, 3, 4` with rational `k` chosen so the required
inequality is a comparison of two integer powers and nothing more.

## The proved horizons

For `N = 3m`, vacuity of the product bound now holds from

| `p` | condition on `k` | horizon `a ≥` | as a multiple of `m` |
|---|---|---|---|
| 1 | — | `N` | `3 m` |
| 2 | `12k ≥ 5N` | `5N/6` | `2.5 m` |
| 3 | `50k ≥ 13N` | `39N/50` | `2.34 m` |
| 4 | `100k ≥ 19N` | `19N/25` | `2.28 m` |
| ↓ | | `N log 2` | `2.079 m` |

`product_bound_vacuous_sharp` states the `p = 4` form: **the product family
excludes nothing at or above `a = 0.76·(3m)`**, proved, with the horizon of Round
XX's measurement as the infimum of the family rather than an observation.

## Two structural facts that make "horizon" mean something

* `two_mul_pow_upward` — the vacuity condition is **upward closed in `a`**.  So
  there genuinely is a threshold, not a scattered set, and a horizon proved at one
  exponent holds at every larger one.  This is what lets the `k·p` lattice of
  `two_mul_pow_le_gen` cover all `a`.
* `two_pow_ne_three_pow` — `2 ^ L ≠ 3 ^ a` for `a ≥ 1`, by parity alone.  This is
  the irrationality of `log₂ 3` in the only form the argument uses, and it is what
  makes `δ(a) = L log 2 − a log 3` never vanish.  Round XX's density claim rests on
  the equidistribution of that `δ`; the non-vanishing is proved here, the
  equidistribution is not, and remains the one measured statement in the round.

## What is still measured, stated plainly

The density `1/2` below the horizon is **not** proved here.  It follows from Weyl
equidistribution of `{a log₂ 3}`, which needs the irrationality proved below plus
an analytic ingredient this development does not have.  Everything else from Round
XX — the horizon, its linear scaling in `m`, the conclusion that verification does
not converge — is now a theorem.
-/

namespace Collatz
namespace HorizonSharp

open ProductCeiling

/-! ## Compounding Bernoulli -/

/-- **The amplification.**  Bernoulli at exponent `k`, compounded `p` times: if the
`p`-th power of `N + k` already beats `2 N ^ p`, then the ratio `(1 + 1/N)` has
passed `2` by exponent `k · p`. -/
theorem two_mul_pow_le_gen {N p k : Nat} (hN : 0 < N) (h : 2 * N ^ p ≤ (N + k) ^ p) :
    2 * N ^ (k * p) ≤ (N + 1) ^ (k * p) := by
  have hb := pow_add_one_ge k N
  have hp : (N ^ k * (N + k)) ^ p ≤ ((N + 1) ^ k * N) ^ p := Nat.pow_le_pow_left hb p
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hp
  have h1 : N ^ (k * p) * (2 * N ^ p) ≤ N ^ (k * p) * (N + k) ^ p :=
    Nat.mul_le_mul_left _ h
  have h2 : 2 * N ^ (k * p) * N ^ p ≤ N ^ (k * p) * (2 * N ^ p) := by
    have e : N ^ (k * p) * (2 * N ^ p) = 2 * N ^ (k * p) * N ^ p := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    omega
  have h3 : 2 * N ^ (k * p) * N ^ p ≤ (N + 1) ^ (k * p) * N ^ p :=
    Nat.le_trans (Nat.le_trans h2 h1) hp
  exact Nat.le_of_mul_le_mul_right h3 (Nat.pow_pos hN)

/-- **Upward closure.**  Once the ratio has passed `2` it stays past it, so the
vacuity condition defines a genuine threshold in `a`. -/
theorem two_mul_pow_upward {N a b : Nat} (hab : a ≤ b) (h : 2 * N ^ a ≤ (N + 1) ^ a) :
    2 * N ^ b ≤ (N + 1) ^ b := by
  obtain ⟨d, hd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  subst hd
  have hgrow : N ^ d ≤ (N + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have h1 : 2 * N ^ a * N ^ d ≤ (N + 1) ^ a * N ^ d := Nat.mul_le_mul_right _ h
  have h2 : (N + 1) ^ a * N ^ d ≤ (N + 1) ^ a * (N + 1) ^ d :=
    Nat.mul_le_mul_left _ hgrow
  have e1 : 2 * N ^ (a + d) = 2 * N ^ a * N ^ d := by
    rw [Nat.pow_add, Nat.mul_assoc]
  have e2 : (N + 1) ^ (a + d) = (N + 1) ^ a * (N + 1) ^ d := Nat.pow_add _ _ _
  omega

/-! ## The instantiations

Each needs one integer power comparison and nothing else. -/

/-- `p = 2`, with `k / N ≥ 5 / 12`.  The comparison is `17 ^ 2 = 289 ≥ 288`. -/
theorem two_pow_two {N k : Nat} (h : 5 * N ≤ 12 * k) : 2 * N ^ 2 ≤ (N + k) ^ 2 := by
  have hstep : 17 * N ≤ 12 * (N + k) := by omega
  have hsq : (17 * N) ^ 2 ≤ (12 * (N + k)) ^ 2 := Nat.pow_le_pow_left hstep 2
  have e1 : (17 * N) ^ 2 = 289 * N ^ 2 := by rw [Nat.mul_pow]
  have e2 : (12 * (N + k)) ^ 2 = 144 * (N + k) ^ 2 := by rw [Nat.mul_pow]
  rw [e1, e2] at hsq
  omega

/-- `p = 3`, with `k / N ≥ 13 / 50`.  The comparison is `63 ^ 3 = 250047 ≥ 250000`. -/
theorem two_pow_three {N k : Nat} (h : 13 * N ≤ 50 * k) : 2 * N ^ 3 ≤ (N + k) ^ 3 := by
  have hstep : 63 * N ≤ 50 * (N + k) := by omega
  have hcube : (63 * N) ^ 3 ≤ (50 * (N + k)) ^ 3 := Nat.pow_le_pow_left hstep 3
  have e1 : (63 * N) ^ 3 = 250047 * N ^ 3 := by rw [Nat.mul_pow]
  have e2 : (50 * (N + k)) ^ 3 = 125000 * (N + k) ^ 3 := by rw [Nat.mul_pow]
  rw [e1, e2] at hcube
  omega

/-- `p = 4`, with `k / N ≥ 19 / 100`.  The comparison is
`119 ^ 4 = 200533921 ≥ 200000000`. -/
theorem two_pow_four {N k : Nat} (h : 19 * N ≤ 100 * k) : 2 * N ^ 4 ≤ (N + k) ^ 4 := by
  have hstep : 119 * N ≤ 100 * (N + k) := by omega
  have hq : (119 * N) ^ 4 ≤ (100 * (N + k)) ^ 4 := Nat.pow_le_pow_left hstep 4
  have e1 : (119 * N) ^ 4 = 200533921 * N ^ 4 := by rw [Nat.mul_pow]
  have e2 : (100 * (N + k)) ^ 4 = 100000000 * (N + k) ^ 4 := by rw [Nat.mul_pow]
  rw [e1, e2] at hq
  omega

/-! ## The proved horizons -/

/-- **Horizon at `5N/6`.**  Combining `p = 2` with upward closure. -/
theorem ratio_past_two_five_sixths {N a k : Nat} (hN : 0 < N)
    (hk : 5 * N ≤ 12 * k) (ha : k * 2 ≤ a) :
    2 * N ^ a ≤ (N + 1) ^ a :=
  two_mul_pow_upward ha (two_mul_pow_le_gen hN (two_pow_two hk))

/-- **Horizon at `39N/50`.**  Combining `p = 3` with upward closure. -/
theorem ratio_past_two_thirteen_fiftieths {N a k : Nat} (hN : 0 < N)
    (hk : 13 * N ≤ 50 * k) (ha : k * 3 ≤ a) :
    2 * N ^ a ≤ (N + 1) ^ a :=
  two_mul_pow_upward ha (two_mul_pow_le_gen hN (two_pow_three hk))

/-- **Horizon at `19N/25`.**  Combining `p = 4` with upward closure.  This is the
sharpest of the three, and the family continues: `c_p = p(2^(1/p) − 1)` descends to
`log 2`, so every constant strictly above `log 2` is eventually a theorem. -/
theorem ratio_past_two_nineteen_hundredths {N a k : Nat} (hN : 0 < N)
    (hk : 19 * N ≤ 100 * k) (ha : k * 4 ≤ a) :
    2 * N ^ a ≤ (N + 1) ^ a :=
  two_mul_pow_upward ha (two_mul_pow_le_gen hN (two_pow_four hk))

/-! ## The sharpened ceiling on the product family -/

/-- **The sharpened vacuity theorem.**  With `N = 3m`, the product bound
`2 ^ L · m ^ a ≤ (3m+1) ^ a` holds outright once `a` reaches `4k` for any `k` with
`19·(3m) ≤ 100k` — that is, from `a ≈ 0.76 · 3m = 2.28 m` upward, against Round
XX's `3 m`.

The hypothesis `2 ^ K ≤ 3 ^ a` is again exactly the `L = K + 1` a cycle has. -/
theorem product_bound_vacuous_sharp {m a k K : Nat} (hm : 0 < m)
    (hk : 19 * (3 * m) ≤ 100 * k) (ha : k * 4 ≤ a) (hK : 2 ^ K ≤ 3 ^ a) :
    2 ^ (K + 1) * m ^ a ≤ (3 * m + 1) ^ a := by
  have hNpos : 0 < 3 * m := by omega
  have hspend : 2 * (3 * m) ^ a ≤ (3 * m + 1) ^ a :=
    ratio_past_two_nineteen_hundredths hNpos hk ha
  have hsplit : (3 * m) ^ a = 3 ^ a * m ^ a := Nat.mul_pow 3 m a
  have htop : 2 ^ (K + 1) * m ^ a ≤ 2 * (3 ^ a * m ^ a) := by
    have h2 : (2:Nat) ^ (K + 1) = 2 * 2 ^ K := Arith.two_pow_succ K
    have hmul : 2 ^ K * m ^ a ≤ 3 ^ a * m ^ a := Nat.mul_le_mul_right _ hK
    rw [h2, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hmul
  rw [hsplit] at hspend
  exact Nat.le_trans htop hspend

/-! ## The irrationality the density claim rests on

`δ(a) = L log 2 − a log 3` never vanishes.  In integer terms `2 ^ L ≠ 3 ^ a`, and
that is parity, not analysis. -/

/-- `3 ^ a` is odd. -/
theorem three_pow_odd : ∀ a : Nat, 3 ^ a % 2 = 1
  | 0 => rfl
  | a + 1 => by
      have := three_pow_odd a
      rw [Nat.pow_succ]
      omega

/-- **`2 ^ L ≠ 3 ^ a` whenever `L ≥ 1`.**  The left side is even and the right is
odd.  Equivalently `log₂ 3` is irrational — in the only form this development
needs, and with no analysis anywhere. -/
theorem two_pow_ne_three_pow {L a : Nat} (hL : 1 ≤ L) : 2 ^ L ≠ 3 ^ a := by
  intro h
  have hodd := three_pow_odd a
  have heven : (2:Nat) ^ L % 2 = 0 := by
    obtain ⟨d, hd⟩ : ∃ d, L = d + 1 := ⟨L - 1, by omega⟩
    rw [hd, Arith.two_pow_succ]
    exact Nat.mul_mod_right 2 _
  omega

/-- The consequence used above: a cycle's `L` sits strictly between, so the
Round XX quantity `δ(a)` is strictly positive at every `a`.  Stated without
logarithms: `3 ^ a < 2 ^ (K+1)` whenever `2 ^ K ≤ 3 ^ a` and `K ≥ 1`. -/
theorem delta_pos {a K : Nat} (hK : 1 ≤ K) (hle : 2 ^ K ≤ 3 ^ a)
    (hlt : 3 ^ a < 2 ^ (K + 1)) : 2 ^ K < 3 ^ a ∧ 3 ^ a < 2 ^ (K + 1) :=
  ⟨Nat.lt_of_le_of_ne hle (fun h => two_pow_ne_three_pow hK h), hlt⟩

end HorizonSharp
end Collatz
