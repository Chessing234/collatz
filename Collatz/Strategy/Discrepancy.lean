import Collatz.Strategy.CycleAccumulator
import Collatz.Strategy.AccumulatorArith

/-!
# The spread of a cycle *is* the discrepancy of its word, to within one bit

Round V asked for the **spread** `M / n` of a hypothetical cycle (largest orbit
element over smallest).  Round VII localised the whole problem in the **ordering**
of the odd-step times `0 ≤ t₁ < … < t_a < L`.  This file is the bridge: the two
are the same quantity.

## The statement in logarithmic gloss

Write `A j = oddCount n j` for the number of odd steps strictly before time `j`,
`a = A L`, `ρ = a / L`, and

`D j = A j − ρ · j`     (the **discrepancy** of the word at time `j`),
`E = L − a · log₂ 3 = log₂ (2 ^ L / 3 ^ a)`   (the **ledge slack**).

The exact affine law `2 ^ j · x_j = 3 ^ (A j) · n + C_j` gives
`log₂ (x_j / n) = A j · log₂ 3 − j + ε_j` with `ε_j = log₂ (1 + C_j / (3 ^ (A j) n))`,
and substituting `A j = ρ j + D j` and `ρ · log₂ 3 − 1 = −E / L`:

> `log₂ (x_j / n) = log₂ 3 · D j − j · E / L + ε_j`.

The two error terms are each confined to `[0, E]` — the first trivially, the
second by `orbit_upper` below, whose proof is the cocycle plus the cycle
criterion, so

> **`|log₂ (x_j / n) − log₂ 3 · D j| ≤ E < 1`** on the ledge `2 ^ L < 2 · 3 ^ a`.

Taking the maximum over `j` gives the headline:

> **`|log₂ (M / n) − log₂ 3 · Dwidth| ≤ 2 E < 2`**, `Dwidth = max_j D j − min_j D j`.

Two labels, both corrections to earlier drafts of this header.

*The `2 E` form is `PROVED-on-paper`, not what Lean proves.*  What is kernel-checked
is `dwidth_lt_disc_argmax`, whose slack is `4` in `D`-units, i.e. `4·log₂ 3 = 6.34`
bits rather than `2 E < 2` bits.  The `2 E` form is exact numerically (over every
cycle of `3x+d`, `d` odd, `1 ≤ d < 200`, minima `≤ 600`, on the ledge, the excess
over `2 E` is exactly `0`), and it is what the two-sided bound gives on paper, but
the Lean statement is the weaker one.  Do not cite `2 E` as `LEAN_PROVED`.

*An earlier draft justified `min_j D j ≥ −E / log₂ 3 > −0.64` by "`D 0 = D L = 0`".
That is a non-sequitur* and the bound is false without more.  Vanishing at both
endpoints says nothing about the interior: the word `0^(L−a) 1^a` has `D 0 = D L =
0` and `min D = −a(L−a)/L`, linear in `L`.  Even on a genuine cycle the claim fails
when `n` is not the minimum — the trivial `d = 1` cycle read from `n = 2` has
`D 1 = −0.5 < −0.2618 = −E / log₂ 3`.  The bound needs `n` to be the *orbit
minimum*, which is exactly the `hmin` hypothesis of `disc_min_near_zero` below.

## Why the file is stated without logarithms

There are none available here.  Every logarithm above is a gloss on an exact
statement between naturals, and it is the exact statements that are proved:

* `orbit_lower`  : `3 ^ (A j) · n ≤ 2 ^ j · x_j`                (unconditional);
* `orbit_upper`  : `3 ^ a · (2 ^ j · x_j) ≤ 2 ^ L · (3 ^ (A j) · n)`  (on a cycle).

Together they are `x_j / n ∈ [3 ^ (A j) / 2 ^ j , (2 ^ L / 3 ^ a) · 3 ^ (A j) / 2 ^ j]`
— an interval of multiplicative width exactly `2 ^ E`, i.e. **less than one bit**.
That is the bridge; `bridge_two_sided` states it as one theorem.

## The consequence that is not a tautology

`disc_forces_order_any`: if the scaled discrepancies satisfy `L · D j ≥ L · D k +
2 L` — that is, `D j ≥ D k + 2`, a gap of two in a quantity whose whole range is
`[−0.64, Dwidth]` — then `x_k < x_j` outright, for *any* two times `j, k ≤ L`.  So
the discrepancy profile **totally orders the orbit up to a slack of two units**,
with no reference to `n`, to the magnitude of anything, or to `d`.  The proof
needs nothing but the two halves of the ledge inequality `3 ^ a < 2 ^ L ≤ 2 · 3 ^ a`
and `9 ^ L > 4 ^ L`; the two directions `k ≤ j` (`pow_gap`, raise to the `L`-th
power) and `j ≤ k` (`pow_gap_rev`, raise to the `a`-th power) are separate
arguments.

`dwidth_lt_disc_argmax` closes the loop: at the time `J` where the orbit is
maximal, `Dwidth < D J + 4`, so the width and the peak coincide up to a constant.

## Numerical confirmation (exact rational arithmetic, not proof)

Measured on the genuine cycles of the neighbouring maps, `θ_j = log₂(x_j/n) −
log₂ 3 · D j`, against the predicted envelope `|θ_j| ≤ |E|`:

| cycle | `L` | `a` | `E` | `Dwidth` | `log₂ 3 · Dwidth` | `log₂(M/n)` | `θ` range |
|---|---|---|---|---|---|---|---|
| `3x−1`, min 17 | 11 | 7 | −0.0947 | 1.9091 | 3.0258 | 3.0000 | `[−0.0353, 0]` |
| `3x+5`, min 187 | 27 | 17 | +0.0556 | 2.8148 | 4.4614 | 4.4762 | `[0, +0.0228]` |
| `3x+5`, min 347 | 27 | 17 | +0.0556 | 2.4444 | 3.8744 | 3.8769 | `[−0.0097, +0.0084]` |
| `3x+5`, min 19 | 5 | 3 | +0.2451 | 1.2000 | 1.9020 | 2.0000 | `[0, +0.0988]` |
| `3x+1`, min 1 | 2 | 1 | +0.4150 | 0.5000 | 0.7925 | 1.0000 | `[0, +0.2075]` |

and on heavy words at ledge pairs, where `ε_j = 0` and the relation is exact:

| `(L, a)` | word | `Dwidth` | `log₂ 3 · Dwidth` | true spread |
|---|---|---|---|---|
| `(27, 17)` | Beatty | 0.9630 | 1.5263 | 1.5654 |
| `(27, 17)` | `1^a 0^*` | 6.2963 | 9.9794 | 10.0000 |
| `(4701, 2966)` | Beatty | 0.99977 | 1.58460 | 1.58489 |
| `(4701, 2966)` | `1^a 0^*` | 1094.6628 | 1734.9995 | 1735.0000 |

**How sharp is the slack `2`?**  Over 180 genuine cycles of `3x + d`, `d` odd and
`1 ≤ d < 200`, minima below 600, that satisfy the ledge hypothesis
`3 ^ a < 2 ^ L ≤ 2 · 3 ^ a`, the largest discrepancy gap occurring in an
*inversion* (a pair with `D j > D k` but `x_j ≤ x_k`) is **0.1034** — so `2` is
conservative by a factor of about twenty, and on the five cycles tabulated above
there are no inversions at all: the discrepancy order *is* the orbit order.  The
ledge hypothesis is load-bearing, not decorative: dropping it and sweeping
`−99 ≤ d ≤ 99` over 283 cycles (most of them off the ledge, including every `d < 0`
one, where `3 ^ a > 2 ^ L`) produces inversions with discrepancy gaps up to
**2.92**, which would falsify the theorem were the hypothesis not there.

Both of Round V's endpoints are recovered: the minimum spread `≈ log₂ 3` is
`Dwidth ≈ 1` (the Sturmian bound on Beatty discrepancy), and the maximum spread
`0.585 · a` is `Dwidth = a(1 − a/L) = 0.369 a`, since `log₂ 3 · 0.369 = 0.585`.

## Soundness verdict — read this before building on the file

Everything here is a function of the parity word alone, and `C(w, d) = d · C(w,1)`
makes `M / n` invariant under `d`, so by the Round III filter **this bridge can
obstruct nothing by itself**.  It is a change of coordinates, and the tables above
are its confirmation, not evidence for a mechanism: the `3x+5` cycles satisfy it
exactly as the `3x+1` one does.  What it buys is a language — the spread question
of Round V and the ordering question of Round VII are literally the same question,
so any bound on either transfers to the other with an additive constant `2`.  What
it does not buy is a new constraint.
-/

namespace Collatz
namespace Discrepancy

open AffineExact AccumulatorArith AccCycle

/-! ## The discrepancy, scaled by `L` to stay in `Int` -/

/-- `disc n L j = L · D(j)`, where `D(j) = A(j) − (a/L)·j` is the discrepancy of
the parity word of `n` at time `j`.  Scaling by `L` clears the only denominator,
so the whole theory is integral. -/
def disc (n L j : Nat) : Int :=
  (L : Int) * (oddCount n j : Int) - (oddCount n L : Int) * (j : Int)

@[simp] theorem disc_zero (n L : Nat) : disc n L 0 = 0 := by
  simp [disc]

@[simp] theorem disc_end (n L : Nat) : disc n L L = 0 := by
  unfold disc
  rw [Int.mul_comm]
  omega

/-- The discrepancy in the shape the ordering theorem consumes. -/
theorem disc_le_iff (n L j k : Nat) :
    disc n L k + 2 * (L : Int) ≤ disc n L j ↔
      (L : Int) * (oddCount n k : Int) + (oddCount n L : Int) * (j : Int)
          + 2 * (L : Int)
        ≤ (L : Int) * (oddCount n j : Int) + (oddCount n L : Int) * (k : Int) := by
  unfold disc
  omega

/-! ### The width of the discrepancy

`Dwidth = max_j D j − min_j D j`, scaled by `L` like `disc` itself.  The maxima
are plain folds — there is no `Finset` here — and the only facts needed are that
they dominate/are dominated by every value in range. -/

/-- `discMax n L J = L · max_{j ≤ J} D j`. -/
def discMax (n L : Nat) : Nat → Int
  | 0 => disc n L 0
  | J + 1 => max (discMax n L J) (disc n L (J + 1))

/-- `discMin n L J = L · min_{j ≤ J} D j`. -/
def discMin (n L : Nat) : Nat → Int
  | 0 => disc n L 0
  | J + 1 => min (discMin n L J) (disc n L (J + 1))

/-- `dwidth n L = L · Dwidth`, the scaled width of the discrepancy over the whole
window `[0, L]`. -/
def dwidth (n L : Nat) : Int := discMax n L L - discMin n L L

theorem disc_le_discMax (n L : Nat) : ∀ J j : Nat, j ≤ J → disc n L j ≤ discMax n L J := by
  intro J
  induction J with
  | zero => intro j hj; have : j = 0 := by omega
            rw [this]; exact Int.le_refl _
  | succ J ih =>
    intro j hj
    rcases Nat.lt_or_ge j (J + 1) with h | h
    · exact Int.le_trans (ih j (by omega)) (Int.le_max_left _ _)
    · have hj' : j = J + 1 := by omega
      rw [hj']
      exact Int.le_max_right _ _

theorem discMin_le_disc (n L : Nat) : ∀ J j : Nat, j ≤ J → discMin n L J ≤ disc n L j := by
  intro J
  induction J with
  | zero => intro j hj; have : j = 0 := by omega
            rw [this]; exact Int.le_refl _
  | succ J ih =>
    intro j hj
    rcases Nat.lt_or_ge j (J + 1) with h | h
    · exact Int.le_trans (Int.min_le_left _ _) (ih j (by omega))
    · have hj' : j = J + 1 := by omega
      rw [hj']
      exact Int.min_le_right _ _

/-- The width is nonnegative, and at least as large as any single discrepancy
value (since `D 0 = 0` is always in the range). -/
theorem disc_le_dwidth {n L j : Nat} (hj : j ≤ L) : disc n L j ≤ dwidth n L := by
  have h1 : disc n L j ≤ discMax n L L := disc_le_discMax n L L j hj
  have h2 : discMin n L L ≤ disc n L 0 := discMin_le_disc n L L 0 (Nat.zero_le L)
  have h3 : disc n L 0 = 0 := disc_zero n L
  unfold dwidth
  omega

theorem dwidth_nonneg (n L : Nat) : 0 ≤ dwidth n L := by
  have h1 : disc n L 0 ≤ discMax n L L := disc_le_discMax n L L 0 (Nat.zero_le L)
  have h2 : discMin n L L ≤ disc n L 0 := discMin_le_disc n L L 0 (Nat.zero_le L)
  unfold dwidth
  omega

/-! ## The two-sided sandwich

The lower bound is the affine law with the accumulator thrown away; the upper
bound is the affine law with the accumulator bounded *by the cycle equation
itself*, through the cocycle. -/

/-- **Lower bound, unconditional.**  Dropping the (nonnegative) accumulator from
the exact affine law. -/
theorem orbit_lower (n j : Nat) :
    3 ^ oddCount n j * n ≤ 2 ^ j * acceleratedOrbit j n := by
  have h := affine_exact n j
  omega

/-- The accumulator of a prefix, promoted by the odd steps that follow it, is at
most the accumulator of the whole window.  This is the cocycle with the second
summand discarded. -/
theorem affineC_prefix_le {n L j : Nat} (hj : j ≤ L) :
    3 ^ oddCount (acceleratedOrbit j n) (L - j) * affineC j n ≤ affineC L n := by
  have hsplit : j + (L - j) = L := by omega
  have h := affineC_add n j (L - j)
  rw [hsplit] at h
  omega

/-- The odd steps split at `j`: `a = A j + b`, with `b` the odd count of the tail. -/
theorem oddCount_split {n L j : Nat} (hj : j ≤ L) :
    oddCount n L = oddCount n j + oddCount (acceleratedOrbit j n) (L - j) := by
  have hsplit : j + (L - j) = L := by omega
  have h := oddCount_add n j (L - j)
  rw [hsplit] at h
  exact h

/-- **Upper bound, on a cycle.**  `3 ^ a · (2 ^ j · x_j) ≤ 2 ^ L · (3 ^ (A j) · n)`.

In logarithms: `log₂(x_j/n) ≤ A j · log₂ 3 − j + (L − a log₂ 3)`.  Combined with
`orbit_lower` the orbit ratio is pinned to a multiplicative interval of width
`2 ^ L / 3 ^ a`, i.e. **less than one bit on the ledge**. -/
theorem orbit_upper {n L j : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L) (hj : j ≤ L) :
    3 ^ oddCount n L * (2 ^ j * acceleratedOrbit j n)
      ≤ 2 ^ L * (3 ^ oddCount n j * n) := by
  have hgap := CycleAccumulator.cycle_gap_mul hn hc
  have hlt : 3 ^ oddCount n L < 2 ^ L := (accCycle_bounds hn hc).2.2
  have hsplit := oddCount_split (n := n) (L := L) (j := j) hj
  have hpre := affineC_prefix_le (n := n) (L := L) (j := j) hj
  have haff := affine_exact n j
  -- abbreviations
  have hpow : (3:Nat) ^ oddCount n L
      = 3 ^ oddCount n j * 3 ^ oddCount (acceleratedOrbit j n) (L - j) := by
    rw [← Nat.pow_add, ← hsplit]
  have hkey : 3 ^ oddCount n L * affineC j n ≤ 3 ^ oddCount n j * affineC L n := by
    rw [hpow, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hpre
  -- expand
  have hexp : 3 ^ oddCount n L * (2 ^ j * acceleratedOrbit j n)
      = 3 ^ oddCount n L * (3 ^ oddCount n j * n) + 3 ^ oddCount n L * affineC j n := by
    rw [haff, Nat.mul_add]
  have hgap' : 3 ^ oddCount n j * affineC L n
      = 3 ^ oddCount n j * ((2 ^ L - 3 ^ oddCount n L) * n) := by
    rw [hgap]
  have hfill : 3 ^ oddCount n L * (3 ^ oddCount n j * n)
      + 3 ^ oddCount n j * ((2 ^ L - 3 ^ oddCount n L) * n)
      = 2 ^ L * (3 ^ oddCount n j * n) := by
    have h1 : (2 ^ L - 3 ^ oddCount n L) * n = 2 ^ L * n - 3 ^ oddCount n L * n := by
      rw [Nat.sub_mul]
    have h2 : 3 ^ oddCount n L * n ≤ 2 ^ L * n := Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
    have h3 : 3 ^ oddCount n j * (2 ^ L * n - 3 ^ oddCount n L * n)
        = 3 ^ oddCount n j * (2 ^ L * n) - 3 ^ oddCount n j * (3 ^ oddCount n L * n) := by
      rw [Nat.mul_sub]
    have h4 : 3 ^ oddCount n j * (3 ^ oddCount n L * n) ≤ 3 ^ oddCount n j * (2 ^ L * n) :=
      Nat.mul_le_mul_left _ h2
    rw [h1, h3]
    have h5 : 3 ^ oddCount n L * (3 ^ oddCount n j * n)
        = 3 ^ oddCount n j * (3 ^ oddCount n L * n) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (3 ^ oddCount n L)]
    have h6 : 3 ^ oddCount n j * (2 ^ L * n) = 2 ^ L * (3 ^ oddCount n j * n) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (3 ^ oddCount n j)]
    omega
  omega

/-- **The bridge, as one statement.**  On a cycle, every orbit element is pinned
between `3 ^ (A j) / 2 ^ j` and `(2 ^ L / 3 ^ a)` times that, relative to `n`. -/
theorem bridge_two_sided {n L j : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L) (hj : j ≤ L) :
    3 ^ oddCount n j * n ≤ 2 ^ j * acceleratedOrbit j n ∧
      3 ^ oddCount n L * (2 ^ j * acceleratedOrbit j n)
        ≤ 2 ^ L * (3 ^ oddCount n j * n) :=
  ⟨orbit_lower n j, orbit_upper hn hc hj⟩

/-! ## The discrepancy orders the orbit

The arithmetic core: on the ledge, a discrepancy advantage of `2` beats the
whole one-bit slack of the sandwich. -/

/-- `4 ^ L < 9 ^ L` for `L ≥ 1`. -/
theorem four_pow_lt_nine_pow {L : Nat} (hL : 0 < L) : 4 ^ L < 9 ^ L := by
  obtain ⟨m, hm⟩ : ∃ m : Nat, L = m + 1 := ⟨L - 1, by omega⟩
  subst hm
  have hle : (4:Nat) ^ m ≤ 9 ^ m := Nat.pow_le_pow_left (by omega) m
  have hpos : 0 < (9:Nat) ^ m := Nat.pow_pos (by omega)
  have e1 : (4:Nat) ^ (m + 1) = 4 ^ m * 4 := Nat.pow_succ 4 m
  have e2 : (9:Nat) ^ (m + 1) = 9 ^ m * 9 := Nat.pow_succ 9 m
  omega

/-- `9 ^ L` beats `2 ^ (L + q)` whenever `q ≤ L` and `L ≥ 1`.  This is the only
place the constant `2` in the discrepancy slack is spent. -/
theorem two_pow_lt_nine_pow {L q : Nat} (hL : 0 < L) (hq : q ≤ L) :
    2 ^ (L + q) < 9 ^ L := by
  have h1 : (2:Nat) ^ (L + q) ≤ 2 ^ (2 * L) := Arith.two_pow_le_two_pow (by omega)
  have h22 : (2:Nat) ^ 2 = 4 := by decide
  have h2 : (2:Nat) ^ (2 * L) = 4 ^ L := by rw [Nat.pow_mul, h22]
  have h3 : (4:Nat) ^ L < 9 ^ L := four_pow_lt_nine_pow hL
  omega

/-- **The ledge inequality promotes a discrepancy gap of `2` to a strict power
comparison.**  If `L · p ≥ 2 L + a · q` with `q ≤ L`, and the pair `(L, a)` is on
the ledge (`2 ^ L ≤ 2 · 3 ^ a`), then `3 ^ (p + a) > 2 ^ (L + q)`.

The proof raises both sides to the `L`-th power, which is where the hypothesis
becomes usable:
`3 ^ (L(p+a)) ≥ 9 ^ L · (3 ^ a) ^ (L+q) > 2 ^ (L+q) · (3 ^ a) ^ (L+q) ≥ 2 ^ (L(L+q))`. -/
theorem pow_gap {L a p q : Nat} (hL : 0 < L) (hq : q ≤ L)
    (hledge : 2 ^ L ≤ 2 * 3 ^ a) (hp : 2 * L + a * q ≤ L * p) :
    2 ^ (L + q) < 3 ^ (p + a) := by
  -- `(2 ^ L) ^ (L+q) ≤ (2 · 3 ^ a) ^ (L+q)`
  have hstep1 : (2:Nat) ^ (L * (L + q)) ≤ 2 ^ (L + q) * (3 ^ a) ^ (L + q) := by
    have h0 : ((2:Nat) ^ L) ^ (L + q) ≤ (2 * 3 ^ a) ^ (L + q) :=
      Nat.pow_le_pow_left hledge _
    have h1 : (2:Nat) ^ (L * (L + q)) = ((2:Nat) ^ L) ^ (L + q) := Nat.pow_mul 2 L (L + q)
    have h2 : ((2:Nat) * 3 ^ a) ^ (L + q) = 2 ^ (L + q) * (3 ^ a) ^ (L + q) :=
      Nat.mul_pow 2 (3 ^ a) (L + q)
    rw [h1, ← h2]
    exact h0
  have hpos : 0 < ((3:Nat) ^ a) ^ (L + q) := Nat.pow_pos (Arith.three_pow_pos a)
  have hstep2 : 2 ^ (L + q) * (3 ^ a) ^ (L + q) < 9 ^ L * (3 ^ a) ^ (L + q) :=
    Nat.mul_lt_mul_of_lt_of_le (two_pow_lt_nine_pow hL hq) (Nat.le_refl _) hpos
  have hexp : 2 * L + a * (L + q) ≤ L * (p + a) := by
    have hd : L * (p + a) = L * p + a * L := by
      rw [Nat.mul_add, Nat.mul_comm L a]
    have hd2 : a * (L + q) = a * L + a * q := Nat.mul_add a L q
    omega
  have hstep3 : 9 ^ L * (3 ^ a) ^ (L + q) ≤ 3 ^ (L * (p + a)) := by
    have h32 : (3:Nat) ^ 2 = 9 := by decide
    have h9 : (3:Nat) ^ (2 * L) = 9 ^ L := by rw [Nat.pow_mul, h32]
    have h3a : (3:Nat) ^ (a * (L + q)) = ((3:Nat) ^ a) ^ (L + q) := Nat.pow_mul 3 a (L + q)
    have hsum : (3:Nat) ^ (2 * L + a * (L + q)) = 9 ^ L * (3 ^ a) ^ (L + q) := by
      rw [Nat.pow_add 3 (2 * L) (a * (L + q)), h9, h3a]
    rw [← hsum]
    exact Arith.three_pow_le_three_pow hexp
  have hchain : (2:Nat) ^ (L * (L + q)) < 3 ^ (L * (p + a)) :=
    Nat.lt_of_le_of_lt hstep1 (Nat.lt_of_lt_of_le hstep2 hstep3)
  -- descend from the `L`-th powers
  have hc1 : (L + q) * L = L * (L + q) := Nat.mul_comm _ _
  have hc2 : (p + a) * L = L * (p + a) := Nat.mul_comm _ _
  have e1 : ((2:Nat) ^ (L + q)) ^ L = 2 ^ (L * (L + q)) := by
    rw [← Nat.pow_mul, hc1]
  have e2 : ((3:Nat) ^ (p + a)) ^ L = 3 ^ (L * (p + a)) := by
    rw [← Nat.pow_mul, hc2]
  have hbig : ((2:Nat) ^ (L + q)) ^ L < ((3:Nat) ^ (p + a)) ^ L := by
    rw [e1, e2]; exact hchain
  rcases Nat.lt_or_ge (2 ^ (L + q)) (3 ^ (p + a)) with h | h
  · exact h
  · exact absurd hbig (Nat.not_lt.2 (Nat.pow_le_pow_left h L))

/-! ### The word-level gap

Purely arithmetic: a scaled-discrepancy advantage of `2 L` at time `j` over time
`k` becomes a strict inequality between the two products the sandwich compares. -/

/-- The discrepancy hypothesis, unwound into the power comparison. -/
theorem word_pow_gap {L a Aj Ak j k : Nat} (hL : 0 < L) (hkj : k ≤ j) (hjL : j ≤ L)
    (hledge : 2 ^ L ≤ 2 * 3 ^ a)
    (hgap : L * Ak + a * j + 2 * L ≤ L * Aj + a * k) :
    2 ^ (L + j) * 3 ^ Ak < 3 ^ (Aj + a) * 2 ^ k := by
  obtain ⟨q, hq⟩ : ∃ q : Nat, j = k + q := ⟨j - k, by omega⟩
  have hqL : q ≤ L := by omega
  have hmul : a * j = a * k + a * q := by rw [hq, Nat.mul_add]
  have hAkAj : Ak ≤ Aj := by
    have h : L * Ak ≤ L * Aj := by omega
    exact Nat.le_of_mul_le_mul_left h hL
  obtain ⟨p, hp⟩ : ∃ p : Nat, Aj = Ak + p := ⟨Aj - Ak, by omega⟩
  have hLp : 2 * L + a * q ≤ L * p := by
    have h : L * Aj = L * Ak + L * p := by rw [hp, Nat.mul_add]
    omega
  have hpow := pow_gap (L := L) (a := a) (p := p) (q := q) hL hqL hledge hLp
  have hposk : 0 < (2:Nat) ^ k * 3 ^ Ak :=
    Nat.mul_pos (Arith.two_pow_pos k) (Arith.three_pow_pos Ak)
  have hkey : 2 ^ (L + q) * (2 ^ k * 3 ^ Ak) < 3 ^ (p + a) * (2 ^ k * 3 ^ Ak) :=
    Nat.mul_lt_mul_of_lt_of_le hpow (Nat.le_refl _) hposk
  have eL : L + j = (L + q) + k := by omega
  have eA : Aj + a = (p + a) + Ak := by omega
  have r1 : (2:Nat) ^ (L + j) * 3 ^ Ak = 2 ^ (L + q) * (2 ^ k * 3 ^ Ak) := by
    rw [eL, Nat.pow_add, Nat.mul_assoc]
  have r2 : (3:Nat) ^ (Aj + a) * 2 ^ k = 3 ^ (p + a) * (2 ^ k * 3 ^ Ak) := by
    rw [eA, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm (3 ^ Ak) (2 ^ k)]
  rw [r1, r2]
  exact hkey

/-- **From the power comparison to the orbit order.**  This is where the sandwich
is consumed: the lower bound at `j`, the upper bound at `k`, and the strict
inequality between them. -/
theorem order_of_pow_gap {n L j k : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hkL : k ≤ L)
    (hmain : 2 ^ (L + j) * 3 ^ oddCount n k
              < 3 ^ (oddCount n j + oddCount n L) * 2 ^ k) :
    acceleratedOrbit k n < acceleratedOrbit j n := by
  have hlow : 3 ^ oddCount n j * n ≤ 2 ^ j * acceleratedOrbit j n := orbit_lower n j
  have hup : 3 ^ oddCount n L * (2 ^ k * acceleratedOrbit k n)
      ≤ 2 ^ L * (3 ^ oddCount n k * n) := orbit_upper hn hc hkL
  have hA : 2 ^ j * (3 ^ oddCount n L * (2 ^ k * acceleratedOrbit k n))
      ≤ 2 ^ j * (2 ^ L * (3 ^ oddCount n k * n)) := Nat.mul_le_mul_left _ hup
  have hB : 3 ^ oddCount n L * 2 ^ k * (3 ^ oddCount n j * n)
      ≤ 3 ^ oddCount n L * 2 ^ k * (2 ^ j * acceleratedOrbit j n) :=
    Nat.mul_le_mul_left _ hlow
  have hmid : 2 ^ (L + j) * 3 ^ oddCount n k * n
      < 3 ^ (oddCount n j + oddCount n L) * 2 ^ k * n :=
    Nat.mul_lt_mul_of_lt_of_le hmain (Nat.le_refl n) hn
  have eA : 2 ^ j * (3 ^ oddCount n L * (2 ^ k * acceleratedOrbit k n))
      = 3 ^ oddCount n L * 2 ^ k * 2 ^ j * acceleratedOrbit k n := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have eB : 2 ^ j * (2 ^ L * (3 ^ oddCount n k * n))
      = 2 ^ (L + j) * 3 ^ oddCount n k * n := by
    rw [Nat.pow_add]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have eC : 3 ^ oddCount n L * 2 ^ k * (3 ^ oddCount n j * n)
      = 3 ^ (oddCount n j + oddCount n L) * 2 ^ k * n := by
    rw [Nat.pow_add]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have eD : 3 ^ oddCount n L * 2 ^ k * (2 ^ j * acceleratedOrbit j n)
      = 3 ^ oddCount n L * 2 ^ k * 2 ^ j * acceleratedOrbit j n :=
    (Nat.mul_assoc (3 ^ oddCount n L * 2 ^ k) (2 ^ j) (acceleratedOrbit j n)).symm
  rw [eA, eB] at hA
  rw [eC, eD] at hB
  have hfinal : 3 ^ oddCount n L * 2 ^ k * 2 ^ j * acceleratedOrbit k n
      < 3 ^ oddCount n L * 2 ^ k * 2 ^ j * acceleratedOrbit j n := by omega
  exact Nat.lt_of_mul_lt_mul_left hfinal

/-- **The discrepancy totally orders the orbit, up to a slack of two.**

If `k ≤ j ≤ L` and the scaled discrepancy at `j` exceeds that at `k` by `2 L`
(that is, `D j ≥ D k + 2`), then `x_k < x_j` — no magnitude hypothesis anywhere.

It does, however, use soundness asset (c), `sign d = +1`, and an earlier draft of
this docstring wrongly said it used nothing.  The route is `orbit_lower`, which is
the affine law with the accumulator dropped, and that step is false when `affineC`
is negative.  Witness, on the ledge, with every other hypothesis met: `d = −45`,
cycle of minimum `−37458`, `L = 27`, `a = 17` (so `3^17 < 2^27 ≤ 2·3^17`), and
`j = 13`, `k = 0` give a discrepancy gap of `2.81` with `x_j = −37458 < −1683 =
x_k` — the conclusion inverted.  It does not typecheck here only because `Nat`
enforces (c) silently.  So: nothing distinguishes `d = 1` *among positive `d`*.

The ledge hypothesis is also genuinely load-bearing, and the sharp witness is
stronger than the one first reported.  Sweeping `1 ≤ d < 200`, minima `≤ 600`, all
rotations: on the ledge the worst inversion gap is `0.1186`; off it, `6.0`, attained
at `d = 107`, the cycle through `1`, `L = 106`, `a = 53`, `j = 99`, `k = 43` —
`A_j = 53`, `A_k = 19`, so `hgap` reads `7473 ≤ 7897` and holds, `2^106 > 2·3^53`
so `hledge` fails, and `x_j = 128 > 133 = x_k` inverts the conclusion.

Non-vacuity, in the theorem's favour: `hledge` is *automatic* for the cycles that
matter, since `GapSandwich.cycle_length_determined` forces `L = fexp a + 1`, hence
`2^(L−1) ≤ 3^a`, hence `2^L ≤ 2·3^a`.  The hypothesis class is not empty.

The hypothesis is stated in `Nat` to keep `omega` in range; `disc_forces_order'`
restates it with `disc`. -/
theorem disc_forces_order {n L j k : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hkj : k ≤ j) (hjL : j ≤ L)
    (hledge : 2 ^ L ≤ 2 * 3 ^ oddCount n L)
    (hgap : L * oddCount n k + oddCount n L * j + 2 * L
              ≤ L * oddCount n j + oddCount n L * k) :
    acceleratedOrbit k n < acceleratedOrbit j n :=
  order_of_pow_gap hn hc (Nat.le_trans hkj hjL)
    (word_pow_gap hc.1 hkj hjL hledge hgap)

/-- The same statement with the hypothesis written in the discrepancy itself:
`D j ≥ D k + 2` forces `x_k < x_j`. -/
theorem disc_forces_order' {n L j k : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hkj : k ≤ j) (hjL : j ≤ L)
    (hledge : 2 ^ L ≤ 2 * 3 ^ oddCount n L)
    (hgap : disc n L k + 2 * (L : Int) ≤ disc n L j) :
    acceleratedOrbit k n < acceleratedOrbit j n := by
  refine disc_forces_order hn hc hkj hjL hledge ?_
  have h := (disc_le_iff n L j k).1 hgap
  omega

/-! ## The other direction: the earlier time may carry the larger discrepancy

`disc_forces_order` needs `k ≤ j` because it clears `2 ^ (j−k)`.  The mirrored
case `j ≤ k` is a different (and easier) inequality, and it needs the *upper* half
of the ledge as well as the lower: from `L(s+2) ≤ a·r` with `s = A k − A j` and
`r = k − j`, and `2 ^ (L−1) ≤ 3 ^ a < 2 ^ L`, one gets `2 ^ L · 3 ^ s < 3 ^ a · 2 ^ r`
by raising to the `a`-th power. -/

/-- The mirrored power gap. -/
theorem pow_gap_rev {L a s r : Nat} (ha : 0 < a) (haL : a < L)
    (hlt : 3 ^ a < 2 ^ L) (hledge : 2 ^ L ≤ 2 * 3 ^ a)
    (hp : L * (s + 2) ≤ a * r) :
    2 ^ L * 3 ^ s < 3 ^ a * 2 ^ r := by
  have hposA : 0 < ((3:Nat) ^ a) ^ a := Nat.pow_pos (Arith.three_pow_pos a)
  -- `(2 ^ L) ^ a ≤ 2 ^ a * (3 ^ a) ^ a`
  have hb1 : ((2:Nat) ^ L) ^ a ≤ 2 ^ a * (3 ^ a) ^ a := by
    have h0 : ((2:Nat) ^ L) ^ a ≤ (2 * 3 ^ a) ^ a := Nat.pow_le_pow_left hledge _
    have h1 : ((2:Nat) * 3 ^ a) ^ a = 2 ^ a * (3 ^ a) ^ a := Nat.mul_pow 2 (3 ^ a) a
    omega
  -- `(3 ^ s) ^ a = (3 ^ a) ^ s ≤ 2 ^ (L * s)`
  have hb2 : ((3:Nat) ^ s) ^ a ≤ 2 ^ (L * s) := by
    have e1 : ((3:Nat) ^ s) ^ a = 3 ^ (s * a) := (Nat.pow_mul 3 s a).symm
    have e2 : ((3:Nat) ^ a) ^ s = 3 ^ (a * s) := (Nat.pow_mul 3 a s).symm
    have ecomm : s * a = a * s := Nat.mul_comm s a
    have e3 : ((2:Nat) ^ L) ^ s = 2 ^ (L * s) := (Nat.pow_mul 2 L s).symm
    have h0 : ((3:Nat) ^ a) ^ s ≤ ((2:Nat) ^ L) ^ s := Nat.pow_le_pow_left (Nat.le_of_lt hlt) _
    have e4 : (3:Nat) ^ (s * a) = 3 ^ (a * s) := by rw [ecomm]
    omega
  -- assemble the left-hand side
  have hL1 : ((2:Nat) ^ L * 3 ^ s) ^ a = ((2:Nat) ^ L) ^ a * ((3:Nat) ^ s) ^ a :=
    Nat.mul_pow _ _ a
  have hR1 : ((3:Nat) ^ a * 2 ^ r) ^ a = ((3:Nat) ^ a) ^ a * ((2:Nat) ^ r) ^ a :=
    Nat.mul_pow _ _ a
  have hstep : ((2:Nat) ^ L) ^ a * ((3:Nat) ^ s) ^ a
      ≤ (2 ^ a * (3 ^ a) ^ a) * 2 ^ (L * s) := Nat.mul_le_mul hb1 hb2
  -- the strict step: `2 ^ (a + L*s) < 2 ^ (2L + L*s) = 2 ^ (L*(s+2)) ≤ 2 ^ (a*r)`
  have hexp : a + L * s < L * (s + 2) := by
    have e : L * (s + 2) = L * s + 2 * L := by rw [Nat.mul_add]; omega
    omega
  have hstrict : (2:Nat) ^ (a + L * s) < 2 ^ (a * r) := by
    have h1 : (2:Nat) ^ (a + L * s) < 2 ^ (L * (s + 2)) :=
      Nat.pow_lt_pow_right (by omega) hexp
    have h2 : (2:Nat) ^ (L * (s + 2)) ≤ 2 ^ (a * r) := Arith.two_pow_le_two_pow hp
    omega
  have hsplit : (2:Nat) ^ a * 2 ^ (L * s) = 2 ^ (a + L * s) := (Nat.pow_add 2 a (L * s)).symm
  have har : ((2:Nat) ^ r) ^ a = 2 ^ (a * r) := by
    have e1 : ((2:Nat) ^ r) ^ a = 2 ^ (r * a) := (Nat.pow_mul 2 r a).symm
    have e2 : r * a = a * r := Nat.mul_comm r a
    rw [e1, e2]
  have hfinal : ((2:Nat) ^ L * 3 ^ s) ^ a < ((3:Nat) ^ a * 2 ^ r) ^ a := by
    have hrew : ((2:Nat) ^ a * (3 ^ a) ^ a) * 2 ^ (L * s)
        = ((2:Nat) ^ a * 2 ^ (L * s)) * (3 ^ a) ^ a := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hmul : (2:Nat) ^ (a + L * s) * ((3:Nat) ^ a) ^ a
        < 2 ^ (a * r) * ((3:Nat) ^ a) ^ a :=
      Nat.mul_lt_mul_of_lt_of_le hstrict (Nat.le_refl _) hposA
    have hcm : ((3:Nat) ^ a) ^ a * 2 ^ (a * r) = 2 ^ (a * r) * ((3:Nat) ^ a) ^ a :=
      Nat.mul_comm _ _
    rw [hL1, hR1, har]
    rw [hrew, hsplit] at hstep
    omega
  rcases Nat.lt_or_ge (2 ^ L * 3 ^ s) (3 ^ a * 2 ^ r) with h | h
  · exact h
  · exact absurd hfinal (Nat.not_lt.2 (Nat.pow_le_pow_left h a))

/-- The mirrored word-level gap: `j ≤ k`, and the discrepancy at `j` still exceeds
the one at `k` by `2`. -/
theorem word_pow_gap_rev {L a Aj Ak j k : Nat} (ha : 0 < a) (haL : a < L)
    (hjk : j ≤ k) (hAjk : Aj ≤ Ak)
    (hlt : 3 ^ a < 2 ^ L) (hledge : 2 ^ L ≤ 2 * 3 ^ a)
    (hgap : L * Ak + a * j + 2 * L ≤ L * Aj + a * k) :
    2 ^ (L + j) * 3 ^ Ak < 3 ^ (Aj + a) * 2 ^ k := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, k = j + r := ⟨k - j, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : Nat, Ak = Aj + s := ⟨Ak - Aj, by omega⟩
  have hmulk : a * k = a * j + a * r := by rw [hr, Nat.mul_add]
  have hmuls : L * Ak = L * Aj + L * s := by rw [hs, Nat.mul_add]
  have hp : L * (s + 2) ≤ a * r := by
    have e : L * (s + 2) = L * s + 2 * L := by rw [Nat.mul_add]; omega
    omega
  have hcore := pow_gap_rev (L := L) (a := a) (s := s) (r := r) ha haL hlt hledge hp
  have hposc : 0 < (2:Nat) ^ j * 3 ^ Aj :=
    Nat.mul_pos (Arith.two_pow_pos j) (Arith.three_pow_pos Aj)
  have hmul : (2 ^ L * 3 ^ s) * (2 ^ j * 3 ^ Aj) < (3 ^ a * 2 ^ r) * (2 ^ j * 3 ^ Aj) :=
    Nat.mul_lt_mul_of_lt_of_le hcore (Nat.le_refl _) hposc
  have e1 : (2:Nat) ^ (L + j) * 3 ^ Ak = (2 ^ L * 3 ^ s) * (2 ^ j * 3 ^ Aj) := by
    rw [hs, Nat.pow_add, Nat.pow_add]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have e2 : (3:Nat) ^ (Aj + a) * 2 ^ k = (3 ^ a * 2 ^ r) * (2 ^ j * 3 ^ Aj) := by
    rw [hr, Nat.pow_add, Nat.pow_add]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [e1, e2]
  exact hmul

/-- **The discrepancy orders the orbit, both directions.**  For any two times
`j, k ≤ L` of a cycle, a scaled-discrepancy advantage of `2 L` at `j` forces
`x_k < x_j`.  No hypothesis on the relative order of `j` and `k`. -/
theorem disc_forces_order_any {n L j k : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hjL : j ≤ L) (hkL : k ≤ L)
    (hledge : 2 ^ L ≤ 2 * 3 ^ oddCount n L)
    (hgap : L * oddCount n k + oddCount n L * j + 2 * L
              ≤ L * oddCount n j + oddCount n L * k) :
    acceleratedOrbit k n < acceleratedOrbit j n := by
  obtain ⟨ha, haL, hlt⟩ := accCycle_bounds hn hc
  rcases Nat.lt_or_ge k j with h | h
  · exact order_of_pow_gap hn hc hkL
      (word_pow_gap hc.1 (Nat.le_of_lt h) hjL hledge hgap)
  · have hmono : oddCount n j ≤ oddCount n k := by
      have hsp := oddCount_split (n := n) (L := k) (j := j) h
      omega
    exact order_of_pow_gap hn hc hkL
      (word_pow_gap_rev (by omega) haL h hmono hlt hledge hgap)

/-- The both-directions statement in the discrepancy itself. -/
theorem disc_forces_order_any' {n L j k : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hjL : j ≤ L) (hkL : k ≤ L)
    (hledge : 2 ^ L ≤ 2 * 3 ^ oddCount n L)
    (hgap : disc n L k + 2 * (L : Int) ≤ disc n L j) :
    acceleratedOrbit k n < acceleratedOrbit j n := by
  refine disc_forces_order_any hn hc hjL hkL hledge ?_
  have h := (disc_le_iff n L j k).1 hgap
  omega

/-! ## Corollaries: the endpoints of the discrepancy are the endpoints of the orbit -/

/-- **The minimum of a cycle sits at discrepancy essentially zero.**  If `n` is the
orbit minimum then no time has scaled discrepancy `2 L` below the start, i.e.
`min_j D j > −2`; with `disc_zero` this says the discrepancy of a cycle word is
one-sided up to the slack, so `Dwidth` and `max_j D j` differ by less than `2`. -/
theorem disc_min_near_zero {n L k : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hkL : k ≤ L) (hmin : ∀ i : Nat, n ≤ acceleratedOrbit i n)
    (hledge : 2 ^ L ≤ 2 * 3 ^ oddCount n L) :
    ¬ (disc n L k + 2 * (L : Int) ≤ disc n L 0) := by
  intro h
  have h0 : disc n L 0 = disc n L L := by rw [disc_zero, disc_end]
  have h' : disc n L k + 2 * (L : Int) ≤ disc n L L := by rw [← h0]; exact h
  have hlt : acceleratedOrbit k n < acceleratedOrbit L n :=
    disc_forces_order_any' hn hc (Nat.le_refl L) hkL hledge h'
  have hcyc : acceleratedOrbit L n = n := hc.2
  have := hmin k
  omega

/-- **The maximum of a cycle sits at essentially maximal discrepancy.**  If `x_J`
is the orbit maximum then no time has scaled discrepancy `2 L` above `J`. -/
theorem disc_max_near_top {n L J k : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hJL : J ≤ L) (hkL : k ≤ L)
    (hmax : ∀ i : Nat, acceleratedOrbit i n ≤ acceleratedOrbit J n)
    (hledge : 2 ^ L ≤ 2 * 3 ^ oddCount n L) :
    ¬ (disc n L J + 2 * (L : Int) ≤ disc n L k) := by
  intro h
  have hlt : acceleratedOrbit J n < acceleratedOrbit k n :=
    disc_forces_order_any' hn hc hkL hJL hledge h
  have := hmax k
  omega

/-- **The width is the maximum, up to `4`.**  On a cycle whose minimum is `n` and
whose maximum is at time `J`, `Dwidth < D J + 4`.  Together with
`bridge_two_sided` this is the headline: `log₂(M/n)` and `log₂ 3 · Dwidth` differ
by a bounded amount, with no dependence on `n`, `L` or `d`. -/
theorem dwidth_lt_disc_argmax {n L J : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hJL : J ≤ L) (hmin : ∀ i : Nat, n ≤ acceleratedOrbit i n)
    (hmax : ∀ i : Nat, acceleratedOrbit i n ≤ acceleratedOrbit J n)
    (hledge : 2 ^ L ≤ 2 * 3 ^ oddCount n L) :
    dwidth n L < disc n L J + 4 * (L : Int) := by
  have hpt : ∀ k : Nat, k ≤ L → disc n L k < disc n L J + 2 * (L : Int) := by
    intro k hk
    have := disc_max_near_top hn hc hJL hk hmax hledge
    omega
  have hptmin : ∀ k : Nat, k ≤ L → -(2 * (L : Int)) < disc n L k := by
    intro k hk
    have := disc_min_near_zero hn hc hk hmin hledge
    have h0 : disc n L 0 = 0 := disc_zero n L
    omega
  have hup : ∀ J' : Nat, J' ≤ L → discMax n L J' < disc n L J + 2 * (L : Int) := by
    intro J'
    induction J' with
    | zero => intro _; exact hpt 0 (Nat.zero_le L)
    | succ J' ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hpt (J' + 1) h
      have h3 : discMax n L (J' + 1) = max (discMax n L J') (disc n L (J' + 1)) := rfl
      omega
  have hlow : ∀ J' : Nat, J' ≤ L → -(2 * (L : Int)) < discMin n L J' := by
    intro J'
    induction J' with
    | zero => intro _; exact hptmin 0 (Nat.zero_le L)
    | succ J' ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hptmin (J' + 1) h
      have h3 : discMin n L (J' + 1) = min (discMin n L J') (disc n L (J' + 1)) := rfl
      omega
  have hA := hup L (Nat.le_refl L)
  have hB := hlow L (Nat.le_refl L)
  unfold dwidth
  omega

end Discrepancy
end Collatz

/-! ## Kernel audit -/

section Audit
#print axioms Collatz.Discrepancy.bridge_two_sided
#print axioms Collatz.Discrepancy.disc_forces_order_any
#print axioms Collatz.Discrepancy.dwidth_lt_disc_argmax
end Audit
