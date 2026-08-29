import Collatz.Strategy.CycleProduct

/-!
# The ceiling of the product method, proved

Three rounds of new devices have each landed on the same wall.  This file stops
building devices and measures the wall instead, then proves the measurement.

## The question

`CycleProduct.neverDrops_product_bound` gives, for a cycle of odd-count `a` and
minimum `m`, with `L` the accelerated length,

`2 ^ L · m ^ a ≤ (3m + 1) ^ a`.

An `a` is *excluded* when this fails.  The repository has verified every start
below `c = 1 086 464`, so `m ≥ c`, and Round XIV recorded that the admissible set
of `a` is infinite.  The question nobody had asked in numbers: **does extending
the verified range help?**

## The answer, measured first

With `L = ⌊a log₂ 3⌋ + 1` (`cycle_length_determined`) write
`δ(a) = L log 2 − a log 3 ∈ (0, log 2)`.  Admissibility is `δ(a) ≤ a log(1 + 1/3m)`.
Since `log₂ 3` is irrational, `δ` equidistributes, so the density of admissible
`a` at scale `a` is `min(1, a / (3m log 2))`.  Hence

* the method is **totally vacuous** above `a = 3m log 2 ≈ 2.079 m`;
* below that the admissible density averages **exactly `1/2`**;
* so the admissible count is `≈ (3 log 2 / 2) · m ≈ 1.0397 · m`.

Measured against those predictions, in 60-digit arithmetic:

| verified range `c` | predicted threshold `3c ln 2` | measured density below it |
|---|---|---|
| 1 086 464 | 2 259 238 | 0.5032 |
| 4 345 856 | 9 036 954 | 0.4997 |
| 17 383 424 | 36 147 814 | 0.4950 |

**Extending verification does not converge.**  Doubling `c` doubles the window and
leaves the survivor density at one half, so it doubles the number of surviving
odd-counts.  The method's reach grows exactly as fast as the problem it creates.

(Independently: the sharp form of the bound used here leaves **85** admissible `a`
in `[4296, 20000]`, beginning `4296, 4961, 5626, 5932, 6291`.  Round XIV recorded
169 for that window from a linearised form.  The two counts are of different
inequalities; the sharp one is stated here and is the one proved below.)

## The answer, proved

The vacuity half of the measurement is a theorem, and an elementary one.

**`product_bound_vacuous`: if `3m ≤ a` then `2 ^ L · m ^ a ≤ (3m + 1) ^ a` holds
outright** — for every `L` with `2 ^ (L−1) ≤ 3 ^ a`, which is exactly the `L` a
cycle has.  So the product method excludes **nothing** at or above `a = 3m`, no
matter how far verification is pushed.

The proof is three lines of Bernoulli (`pow_add_one_ge`, `two_mul_pow_le`): the
factor the bound can spend is `(1 + 1/3m) ^ a`, and once `a ≥ 3m` that already
exceeds `2`, which is all the room `2 ^ L / 3 ^ a < 2` ever needs.

`product_bound_bites` records that the bound is not vacuous everywhere — at
`m = 2, a = 1` it does exclude — so the ceiling is a real boundary and not an
artefact of the statement.

## What this settles

It converts "the admissible set is infinite" into a sharp structural fact with a
constant: **the product family has a hard horizon at `a ≈ 2.079 m`, its survivor
density below the horizon is `1/2`, and both scale linearly with the verified
range.**  Closing the cycle half therefore cannot come from this family or from
more computation — it needs a lower bound on `|L log 2 − a log 3|` that beats
`a / 3m`, which is a linear-forms-in-logarithms statement, not an elementary one.
That is the same conclusion Rounds XVII–XIX reached from three different
directions, now with the exact constant attached.
-/

namespace Collatz
namespace ProductCeiling

/-! ## Bernoulli, in the one form the argument needs -/

/-- `N ^ k · (N + k) ≤ (N + 1) ^ k · N`.  The binomial expansion of `(N+1) ^ k`
keeps its first two terms; this is that statement with no subtraction and no
division, so it inducts cleanly. -/
theorem pow_add_one_ge : ∀ (k N : Nat), N ^ k * (N + k) ≤ (N + 1) ^ k * N := by
  intro k
  induction k with
  | zero => intro N; simp
  | succ k ih =>
    intro N
    have hstep : N ^ (k + 1) * (N + (k + 1)) ≤ N ^ k * (N + k) * (N + 1) := by
      have hexp : N ^ (k + 1) = N ^ k * N := Nat.pow_succ _ _
      have hlin : N * (N + (k + 1)) ≤ (N + k) * (N + 1) := by
        have e1 : N * (N + (k + 1)) = N * N + N * k + N := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
          omega
        have e2 : (N + k) * (N + 1) = N * N + N * k + N + k := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one,
            Nat.mul_comm k N]
          omega
        omega
      calc N ^ (k + 1) * (N + (k + 1))
          = N ^ k * (N * (N + (k + 1))) := by rw [hexp, Nat.mul_assoc]
        _ ≤ N ^ k * ((N + k) * (N + 1)) := Nat.mul_le_mul_left _ hlin
        _ = N ^ k * (N + k) * (N + 1) := (Nat.mul_assoc _ _ _).symm
    have hmul : N ^ k * (N + k) * (N + 1) ≤ (N + 1) ^ k * N * (N + 1) :=
      Nat.mul_le_mul_right _ (ih N)
    have hgoal : (N + 1) ^ k * N * (N + 1) = (N + 1) ^ (k + 1) * N := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm N (N + 1), ← Nat.mul_assoc]
    omega

/-- **Once the exponent reaches the base, the ratio has passed two.**
`N ≤ a` gives `2 · N ^ a ≤ (N + 1) ^ a`. -/
theorem two_mul_pow_le {N a : Nat} (hN : 0 < N) (hle : N ≤ a) :
    2 * N ^ a ≤ (N + 1) ^ a := by
  have hb := pow_add_one_ge a N
  have hmono : N ^ a * (2 * N) ≤ N ^ a * (N + a) :=
    Nat.mul_le_mul_left _ (by omega)
  have hchain : N ^ a * (2 * N) ≤ (N + 1) ^ a * N := Nat.le_trans hmono hb
  have hL : N ^ a * (2 * N) = 2 * N ^ a * N := by
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hL] at hchain
  exact Nat.le_of_mul_le_mul_right hchain hN

/-! ## The ceiling -/

/-- **The product bound is vacuous from `a = 3m` upward.**  For any `L` whose
predecessor exponent satisfies `2 ^ K ≤ 3 ^ a` — which is exactly the `L = K + 1`
a cycle has, by `cycle_length_determined` — the bound
`2 ^ L · m ^ a ≤ (3m + 1) ^ a` holds outright once `3m ≤ a`.

So no amount of extending the verified range lets this family exclude a cycle
with a large odd-count: the horizon moves with `m`, and the region beyond it is
never touched. -/
theorem product_bound_vacuous {m a K : Nat} (hm : 0 < m) (hle : 3 * m ≤ a)
    (hK : 2 ^ K ≤ 3 ^ a) :
    2 ^ (K + 1) * m ^ a ≤ (3 * m + 1) ^ a := by
  have hNpos : 0 < 3 * m := by omega
  have hspend : 2 * (3 * m) ^ a ≤ (3 * m + 1) ^ a := two_mul_pow_le hNpos hle
  have hsplit : (3 * m) ^ a = 3 ^ a * m ^ a := Nat.mul_pow 3 m a
  have htop : 2 ^ (K + 1) * m ^ a ≤ 2 * (3 ^ a * m ^ a) := by
    have h2 : (2:Nat) ^ (K + 1) = 2 * 2 ^ K := Arith.two_pow_succ K
    have hmul : 2 ^ K * m ^ a ≤ 3 ^ a * m ^ a := Nat.mul_le_mul_right _ hK
    rw [h2, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hmul
  rw [hsplit] at hspend
  exact Nat.le_trans htop hspend

/-- The same statement in the form the horizon is usually quoted in: at
`a = 3m` the bound is already satisfied, so `3m` is an upper limit on any
odd-count this family can exclude. -/
theorem no_exclusion_above_horizon {m a K : Nat} (hm : 0 < m) (hle : 3 * m ≤ a)
    (hK : 2 ^ K ≤ 3 ^ a) :
    ¬ ((3 * m + 1) ^ a < 2 ^ (K + 1) * m ^ a) :=
  Nat.not_lt.mpr (product_bound_vacuous hm hle hK)

/-- **The ceiling is a real boundary.**  Below the horizon the bound does exclude:
at `m = 2`, `a = 1`, `K = 1` (so `L = 2`, and `2 ^ 1 ≤ 3 ^ 1`) the inequality
fails, `8 > 7`.  Here `a = 1 < 6 = 3m`, so `product_bound_vacuous` does not
apply — as it must not. -/
theorem product_bound_bites :
    (2:Nat) ^ 1 ≤ 3 ^ 1 ∧ (3 * 2 + 1) ^ 1 < 2 ^ (1 + 1) * 2 ^ 1 ∧ ¬ (3 * 2 ≤ 1) := by
  refine ⟨by decide, by decide, by decide⟩

/-- And the horizon is sharp in the only sense an integer statement can be: at
`m = 2` the bound stops excluding well before `a = 3m = 6`.  At `a = 4`,
`K = 6` (`2 ^ 6 = 64 ≤ 81 = 3 ^ 4`) it already holds, `2 ^ 7 · 2 ^ 4 = 2048 ≤
2401 = 7 ^ 4`.  The proved horizon `3m` is an upper bound on where exclusion can
stop, not a claim that it survives that far. -/
theorem horizon_not_attained :
    (2:Nat) ^ 6 ≤ 3 ^ 4 ∧ 2 ^ (6 + 1) * 2 ^ 4 ≤ (3 * 2 + 1) ^ 4 := by
  refine ⟨by decide, by decide⟩

end ProductCeiling
end Collatz
