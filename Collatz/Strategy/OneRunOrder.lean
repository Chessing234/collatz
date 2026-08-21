import Collatz.Strategy.OneRunCycle
import Collatz.Strategy.CycleAccumulator

/-!
# The one-run order obstruction

`OneRunCycle` solves the single-odd-run cycle exactly: `a` odd steps up from the
least point `m`, then nothing but halvings back down, forces

`3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a`,  equivalently  `m * (2 ^ L - 3 ^ a) = 3 ^ a - 2 ^ a`.

From there that file takes the *archimedean* route: `3 ^ a - 2 ^ a < 2 ^ L` gives
`m + 2 ^ a ≤ 3 ^ a`, and the verified range `m ≥ 307 200` then forces `a ≥ 12`.
That is a size argument, and size arguments in this business are weak: to push
past `a ≥ 12` one needs the defect `δ = (2 ^ L - 3 ^ a) / 2 ^ L` to be at least
`1 / m`, and the continued fraction of `log₂ 3` supplies defects far smaller than
that as soon as `a` is in the tens of thousands.  Every gain costs a proportional
gain in the verified range.

This file takes the *arithmetic* route instead, and it is incomparably stronger.
Write `d = 2 ^ L - 3 ^ a` for the gap.  Then `2 ^ L ≡ 3 ^ a (mod d)`, so modulo
`d` the right-hand side `3 ^ a - 2 ^ a` becomes `2 ^ L - 2 ^ a = 2 ^ a (2 ^ (L-a) - 1)`,
while the left-hand side `m * d` is `0`.  The gap is odd — `2 ^ L` is even and
`3 ^ a` is odd — so it is coprime to `2 ^ a` and the factor drops:

**`(2 ^ L - 3 ^ a) ∣ (2 ^ (L - a) - 1)`**  (`one_run_order_dvd`).

A divisor of a positive number is at most that number, so `d ≤ 2 ^ (L-a) - 1`,
i.e. `δ ≤ 2 ^ (-a)`.  Compare the two demands: the size route needs
`δ ≥ 1 / m ≈ 3 · 10 ^ (-6)`; the order route needs only `δ ≥ 2 ^ (-a)`, weaker by
hundreds of orders of magnitude once `a` is large, **and it uses the verified
range not at all** — only `m ≥ 1`.  That is the whole point of the file: an
order obstruction is a statement about the multiplicative group mod `d`, and it
does not care how big the cycle point is.

## Subtraction-free bookkeeping

Nat subtraction truncates, so the argument is carried on the additive side.  The
gap appears as a witness `d` with `2 ^ L = 3 ^ a + d` (`one_run_gap`), the
equation becomes `d * m + 2 ^ a = 3 ^ a`, and writing `L = a + e`, `2 ^ e = u + 1`
the whole congruence argument collapses to a single identity with no subtraction
anywhere:

`2 ^ a * u = d * (m + 1)`   (`one_run_order`).

The coprimality descent is `odd_dvd_of_dvd_two_pow_mul`: an odd divisor of
`2 ^ k * x` divides `x`, proved by induction from the one-step case.  The
classical form `(2 ^ L - 3 ^ a) ∣ (2 ^ (L - a) - 1)` is then recovered by `omega`
for readers who prefer it.

## What is actually excluded

Multiplying `d + 1 ≤ 2 ^ e` by `2 ^ a` and using `2 ^ a * 3 ^ a = 6 ^ a` turns the
divisibility into a clean Nat inequality with no subtraction and no division:

* `no_one_run_of_gap` — if `2 ^ L + 6 ^ a < 2 ^ (L + a) + 2 ^ a` there is no
  one-run cycle with those parameters;
* `no_one_run_of_gap'` — the same under the tidier `2 ^ L + 6 ^ a ≤ 2 ^ (L + a)`.

The hypothesis is monotone in `L` (`gap_mono`), so it need only be tested at the
minimal admissible length `minLen a` — the least `L` with `3 ^ a < 2 ^ L`,
defined here by a two-line recursion and proved minimal (`minLen_le`).  That
makes the whole exclusion a decidable predicate `gapOK a`, and the kernel checks

* `gapOK_sweep` — `gapOK a = true` for every `2 ≤ a < 2048`,

hence `no_one_run_of_run_lt`: **no one-run cycle with `2 ≤ a < 2048`, for any
`L`, any `m ≥ 1`.**  The remaining case `a = 1` is not an oversight, it is the
trivial cycle: `d * m = 1` forces `m = 1`, `d = 1`, `L = 2`
(`one_run_run_one`).  Assembled, `one_run_trivial`: for `0 < a < 2048` the only
one-run solution at all is `m = 1, a = 1, L = 2`.

Against `OneRunCycle.twelve_le_run_of_one_run` (`a ≥ 12`, and only for
`m ≥ 307 200`) this is an improvement of a factor of about `170` in the run
length and, more importantly, a change of kind: it is unconditional in `m`.

## What is *not* proved

The tail `a ≥ 2048` is open here.  Outside the kernel the inequality
`2 ^ L + 6 ^ a ≤ 2 ^ (L + a)` was checked to hold at the minimal `L` for every
`2 ≤ a ≤ 20 000` (and reportedly to `200 000`), with `a = 1` the sole exception,
so `2048` is a budget for kernel arithmetic and nothing else — raising it costs
compile time and no new mathematics.  But it cannot be raised to infinity by this
method: an unconditional finish needs `2 ^ L - 3 ^ a > 2 ^ (L - a)`, i.e.
`|L log 2 - a log 3| ≳ 2 ^ (-a)`, and elementary arguments give only
`2 ^ L - 3 ^ a ≥ 1`.  With `a ≈ 0.631 · L` the shortfall is a factor of about
`2 ^ (0.369 · L)` — exponential in the cycle length, not a constant — and closing
it is exactly the linear-forms-in-logarithms gap.  That is Baker's theorem, and
it is out of reach of a Mathlib-free development.

Nor does the obstruction generalise as it stands.  For a cycle with `k ≥ 2` odd
runs the accumulator is `Σ 3 ^ (a - B i) * 2 ^ (t i) * (3 ^ (b i) - 2 ^ (b i))`,
and reducing modulo `d` via `2 ^ L ≡ 3 ^ a` does not collapse it: the run starts
`t i` and the partial odd counts `B i` are independent, so no single `2 ^ r - 1`
survives.  A `k = 2` analogue would be a Baker-free two-run theorem; none is
proved here.

## Bridges

`oneRun_affineC` identifies the accumulator of a one-run cycle exactly:
`affineC L m + 2 ^ a = 3 ^ a`, via `CycleAccumulator.cycle_gap_mul` and
`AccCycle.accCycle_bounds`.  So the three arithmetic facts about `C` now read
together: it is a `3`-adic unit, its `2`-adic valuation is the timestamp of the
first odd step, and — when the cycle is a single run — it is `3 ^ a - 2 ^ a`, a
number whose divisor `d` is pinned by an order condition.
`accCycle_gap_dvd_order` and `accCycle_one_run_trivial` state the obstruction
directly for `AccCycle.AccIsCycleOf`.
-/

namespace Collatz
namespace OneRunOrder

open Reach Congruence AffineExact AccCycle

/-! ## Coprimality descent -/

/-- An odd divisor of `2 * x` divides `x`. -/
theorem odd_dvd_of_dvd_two_mul {d x : Nat} (hd : d % 2 = 1) (h : d ∣ 2 * x) : d ∣ x := by
  obtain ⟨t, ht⟩ := h
  have h1 : (d * t) % 2 = 0 := by omega
  have h2 : (d * t) % 2 = (t % 2) % 2 := by
    rw [Nat.mul_mod, hd, Nat.one_mul]
  have ht2 : t % 2 = 0 := by omega
  obtain ⟨s, hs⟩ : 2 ∣ t := Nat.dvd_of_mod_eq_zero ht2
  refine ⟨s, ?_⟩
  have hcomm : d * (2 * s) = 2 * (d * s) := by
    rw [← Nat.mul_assoc, Nat.mul_comm d 2, Nat.mul_assoc]
  have hkey : 2 * x = 2 * (d * s) := by rw [ht, hs, hcomm]
  omega

/-- An odd divisor of `2 ^ k * x` divides `x`. -/
theorem odd_dvd_of_dvd_two_pow_mul {d x : Nat} (hd : d % 2 = 1) :
    ∀ {k : Nat}, d ∣ 2 ^ k * x → d ∣ x := by
  intro k
  induction k with
  | zero => intro h; simpa using h
  | succ k ih =>
    intro h
    refine ih (odd_dvd_of_dvd_two_mul hd ?_)
    have hrw : 2 ^ (k + 1) * x = 2 * (2 ^ k * x) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    rw [hrw] at h
    exact h

/-! ## The gap equation -/

/-- **The one-run cycle equation, subtraction-free.**  There is a positive `d`
with `2 ^ L = 3 ^ a + d` and `d * m + 2 ^ a = 3 ^ a`: the gap times the least
point is exactly `3 ^ a - 2 ^ a`. -/
theorem one_run_gap {m a L : Nat} (ha : 0 < a) (hm : 0 < m)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) :
    ∃ d : Nat, 0 < d ∧ 2 ^ L = 3 ^ a + d ∧ d * m + 2 ^ a = 3 ^ a := by
  have hlt := OneRunCycle.three_pow_lt_two_pow_of_one_run ha hm heq
  obtain ⟨d, hd⟩ : ∃ d : Nat, 2 ^ L = 3 ^ a + d := ⟨2 ^ L - 3 ^ a, by omega⟩
  refine ⟨d, by omega, hd, ?_⟩
  have h1 : (3 ^ a + d) * m = 3 ^ a * m + d * m := Nat.add_mul ..
  have h2 : 3 ^ a * (m + 1) = 3 ^ a * m + 3 ^ a := by rw [Nat.mul_add, Nat.mul_one]
  rw [hd] at heq
  omega

/-- A one-run cycle has strictly more steps than odd steps. -/
theorem run_lt_length {m a L : Nat} (ha : 0 < a) (hm : 0 < m)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) : a < L := by
  have hlt := OneRunCycle.three_pow_lt_two_pow_of_one_run ha hm heq
  have h23 : (2:Nat) ^ a < 3 ^ a := RunValue.two_pow_lt_three_pow a ha
  rcases Nat.lt_or_ge a L with h | h
  · exact h
  · exact absurd (Arith.two_pow_le_two_pow h) (by omega)

/-- The gap of a one-run cycle is odd. -/
theorem gap_odd {a L d : Nat} (hL : 0 < L) (hd : 2 ^ L = 3 ^ a + d) : d % 2 = 1 := by
  have h2L : (2:Nat) ^ L % 2 = 0 := by
    have hrw : (2:Nat) ^ L = 2 * 2 ^ (L - 1) := by
      rw [← Arith.two_pow_succ]
      congr 1
      omega
    omega
  have h3 := Arith.three_pow_odd a
  omega

/-! ## The order obstruction -/

/-- **The order obstruction, subtraction-free.**  For a one-run cycle with `a`
odd steps and `L = a + e` total steps, the gap `d = 2 ^ L - 3 ^ a` satisfies
`2 ^ a * u = d * (m + 1)` where `2 ^ e = u + 1`, and — the gap being odd — it
divides `u = 2 ^ (L - a) - 1` outright. -/
theorem one_run_order {m a e L : Nat} (ha : 0 < a) (hm : 0 < m) (hLe : L = a + e)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) :
    ∃ d u : Nat, 0 < d ∧ 2 ^ L = 3 ^ a + d ∧ 2 ^ e = u + 1 ∧
      2 ^ a * u = d * (m + 1) ∧ d ∣ u := by
  obtain ⟨d, hdpos, hd, hdm⟩ := one_run_gap ha hm heq
  obtain ⟨u, hu⟩ : ∃ u : Nat, 2 ^ e = u + 1 :=
    ⟨2 ^ e - 1, by have := Arith.two_pow_pos e; omega⟩
  have hsplit : (2:Nat) ^ L = 2 ^ a * 2 ^ e := by rw [hLe, Nat.pow_add]
  have hexp : (2:Nat) ^ a * (u + 1) = 2 ^ a * u + 2 ^ a := by
    rw [Nat.mul_add, Nat.mul_one]
  have hd1 : d * (m + 1) = d * m + d := by rw [Nat.mul_add, Nat.mul_one]
  rw [hu] at hsplit
  have hkey : 2 ^ a * u = d * (m + 1) := by omega
  have hodd : d % 2 = 1 := gap_odd (by omega) hd
  refine ⟨d, u, hdpos, hd, hu, hkey, ?_⟩
  exact odd_dvd_of_dvd_two_pow_mul hodd ⟨m + 1, hkey⟩

/-- **The order obstruction in classical form.**  `2 ^ L - 3 ^ a` divides
`2 ^ (L - a) - 1`. -/
theorem one_run_order_dvd {m a L : Nat} (ha : 0 < a) (hm : 0 < m)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) :
    (2 ^ L - 3 ^ a) ∣ (2 ^ (L - a) - 1) := by
  have haL := run_lt_length ha hm heq
  obtain ⟨d, u, hdpos, hd, hu, _, hdvd⟩ :=
    one_run_order (e := L - a) ha hm (by omega) heq
  have h1 : 2 ^ L - 3 ^ a = d := by omega
  have h2 : 2 ^ (L - a) - 1 = u := by omega
  rw [h1, h2]
  exact hdvd

/-- **The gap is at most `2 ^ (L - a) - 1`.**  Stated without subtraction:
`d + 1 ≤ 2 ^ e`. -/
theorem gap_add_one_le {m a e L : Nat} (ha : 0 < a) (hm : 0 < m) (hLe : L = a + e)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) :
    ∃ d : Nat, 2 ^ L = 3 ^ a + d ∧ d + 1 ≤ 2 ^ e := by
  have haL := run_lt_length ha hm heq
  obtain ⟨d, u, hdpos, hd, hu, _, hdvd⟩ := one_run_order ha hm hLe heq
  have hepos : 0 < e := by omega
  have h2e : (2:Nat) ^ 1 ≤ 2 ^ e := Arith.two_pow_le_two_pow hepos
  have hupos : 0 < u := by
    have : (2:Nat) ^ 1 = 2 := by decide
    omega
  have hle : d ≤ u := Arith.le_of_dvd_pos hupos hdvd
  exact ⟨d, hd, by omega⟩

/-! ## The exclusion -/

/-- **The one-run exclusion.**  If `2 ^ L + 6 ^ a < 2 ^ (L + a) + 2 ^ a` then the
one-run cycle equation has no positive solution at all. -/
theorem no_one_run_of_gap {m a L : Nat} (ha : 0 < a) (hm : 0 < m)
    (hgap : 2 ^ L + 6 ^ a < 2 ^ (L + a) + 2 ^ a)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) : False := by
  have haL := run_lt_length ha hm heq
  obtain ⟨d, hd, hdle⟩ := gap_add_one_le (e := L - a) ha hm (by omega) heq
  have hsplit : (2:Nat) ^ L = 2 ^ a * 2 ^ (L - a) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmul : (2:Nat) ^ a * (d + 1) ≤ 2 ^ a * 2 ^ (L - a) :=
    Nat.mul_le_mul_left _ hdle
  have hexp : (2:Nat) ^ a * (d + 1) = 2 ^ a * d + 2 ^ a := by
    rw [Nat.mul_add, Nat.mul_one]
  have hbig : (2:Nat) ^ (L + a) = 2 ^ a * 3 ^ a + 2 ^ a * d := by
    have h1 : (2:Nat) ^ (L + a) = 2 ^ a * 2 ^ L := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [h1, hd, Nat.mul_add]
  have hsix : (2:Nat) ^ a * 3 ^ a = 6 ^ a := by
    rw [← Nat.mul_pow]
  rw [hsix] at hbig
  omega

/-- **The exclusion in the clean form.**  `2 ^ L + 6 ^ a ≤ 2 ^ (L + a)` already
excludes every one-run cycle with these parameters. -/
theorem no_one_run_of_gap' {m a L : Nat} (ha : 0 < a) (hm : 0 < m)
    (hgap : 2 ^ L + 6 ^ a ≤ 2 ^ (L + a))
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) : False := by
  refine no_one_run_of_gap ha hm ?_ heq
  have := Arith.two_pow_pos a
  omega

/-! ## The trivial cycle -/

/-- **A single odd step forces the trivial cycle.**  With `a = 1` the gap
equation reads `d * m = 1`, so `m = 1`, `d = 1` and `L = 2`: the loop
`1 → 2 → 1`, and nothing else. -/
theorem one_run_run_one {m L : Nat} (hm : 0 < m)
    (heq : 3 ^ 1 * (m + 1) = 2 ^ L * m + 2 ^ 1) : m = 1 ∧ L = 2 := by
  obtain ⟨d, hdpos, hd, hdm⟩ := one_run_gap (a := 1) (by omega) hm heq
  have h3 : (3:Nat) ^ 1 = 3 := by decide
  have h2 : (2:Nat) ^ 1 = 2 := by decide
  have hone : d * m = 1 := by omega
  have hd1 : d = 1 := Nat.dvd_one.mp ⟨m, hone.symm⟩
  subst hd1
  rw [Nat.one_mul] at hone
  subst hone
  refine ⟨rfl, ?_⟩
  have hfour : (2:Nat) ^ L = 4 := by omega
  rcases Nat.lt_or_ge L 2 with hlt | hge
  · have : (2:Nat) ^ L ≤ 2 ^ 1 := Arith.two_pow_le_two_pow (by omega)
    rw [h2] at this
    omega
  · rcases Nat.lt_or_ge L 3 with hlt' | hge'
    · omega
    · have : (2:Nat) ^ 3 ≤ 2 ^ L := Arith.two_pow_le_two_pow hge'
      have h8 : (2:Nat) ^ 3 = 8 := by decide
      omega

/-! ## Monotonicity in the cycle length -/

/-- The exclusion hypothesis only gets easier as the cycle lengthens. -/
theorem gap_mono {a L L' : Nat} (hle : L ≤ L')
    (h : 2 ^ L + 6 ^ a ≤ 2 ^ (L + a)) : 2 ^ L' + 6 ^ a ≤ 2 ^ (L' + a) := by
  obtain ⟨q, hqe⟩ : ∃ q : Nat, L' = L + q := ⟨L' - L, by omega⟩
  subst hqe
  have hq : (2:Nat) ^ (L + q) = 2 ^ L * 2 ^ q := Nat.pow_add ..
  have hbig : (2:Nat) ^ (L + q + a) = 2 ^ (L + a) * 2 ^ q := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hqpos : 1 ≤ (2:Nat) ^ q := Arith.two_pow_pos q
  have hmul : (2 ^ L + 6 ^ a) * 2 ^ q ≤ 2 ^ (L + a) * 2 ^ q :=
    Nat.mul_le_mul_right _ h
  have hexp : (2 ^ L + 6 ^ a) * 2 ^ q = 2 ^ L * 2 ^ q + 6 ^ a * 2 ^ q := Nat.add_mul ..
  have hsix : (6:Nat) ^ a * 1 ≤ 6 ^ a * 2 ^ q := Nat.mul_le_mul_left _ hqpos
  rw [Nat.mul_one] at hsix
  omega

/-! ## The minimal length, and a decidable sweep -/

/-- `minLen a` is the least `L` with `3 ^ a < 2 ^ L`, computed by stepping the
exponent up by one or two at each `a`. -/
def minLen : Nat → Nat
  | 0 => 1
  | a + 1 => if 3 ^ (a + 1) < 2 ^ (minLen a + 1) then minLen a + 1 else minLen a + 2

/-- `minLen a` brackets `3 ^ a` between consecutive powers of two. -/
theorem minLen_spec : ∀ a : Nat, 3 ^ a < 2 ^ minLen a ∧ 2 ^ minLen a ≤ 2 * 3 ^ a := by
  intro a
  induction a with
  | zero => decide
  | succ a ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp3 : (3:Nat) ^ (a + 1) = 3 ^ a * 3 := Nat.pow_succ ..
    have hp2a : (2:Nat) ^ (minLen a + 1) = 2 * 2 ^ minLen a := Arith.two_pow_succ _
    have hp2b : (2:Nat) ^ (minLen a + 2) = 2 * 2 ^ (minLen a + 1) := Arith.two_pow_succ _
    have hunf : minLen (a + 1) =
        if 3 ^ (a + 1) < 2 ^ (minLen a + 1) then minLen a + 1 else minLen a + 2 := rfl
    rw [hunf]
    split
    · next hcond => exact ⟨hcond, by omega⟩
    · next hcond => exact ⟨by omega, by omega⟩

/-- `minLen a` is positive. -/
theorem minLen_pos (a : Nat) : 0 < minLen a := by
  have h := (minLen_spec a).1
  have h1 : 1 ≤ (3:Nat) ^ a := Nat.one_le_pow a 3 (by omega)
  rcases Nat.eq_zero_or_pos (minLen a) with h0 | hp
  · rw [h0] at h
    have : (2:Nat) ^ 0 = 1 := by decide
    omega
  · exact hp

/-- **`minLen a` really is minimal**: any `L` with `3 ^ a < 2 ^ L` is at least
`minLen a`. -/
theorem minLen_le {a L : Nat} (h : 3 ^ a < 2 ^ L) : minLen a ≤ L := by
  obtain ⟨h1, h2⟩ := minLen_spec a
  have hpos := minLen_pos a
  rcases Nat.lt_or_ge L (minLen a) with hlt | hge
  · exfalso
    have hstep : (2:Nat) ^ minLen a = 2 * 2 ^ (minLen a - 1) := by
      rw [← Arith.two_pow_succ]
      congr 1
      omega
    have hmono : (2:Nat) ^ L ≤ 2 ^ (minLen a - 1) := Arith.two_pow_le_two_pow (by omega)
    omega
  · exact hge

/-- The decidable one-run exclusion test at the minimal length. -/
def gapOK (a : Nat) : Bool := decide (2 ^ minLen a + 6 ^ a ≤ 2 ^ (minLen a + a))

/-- **The test decides the exclusion.**  If `gapOK a` holds then no `L` at all
admits a one-run cycle with `a` odd steps: the test is run at the minimal `L`
and `gap_mono` carries it to every larger one. -/
theorem no_one_run_of_check {m a L : Nat} (ha : 0 < a) (hm : 0 < m)
    (hchk : gapOK a = true)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) : False := by
  have hlt := OneRunCycle.three_pow_lt_two_pow_of_one_run ha hm heq
  have hbase : 2 ^ minLen a + 6 ^ a ≤ 2 ^ (minLen a + a) := of_decide_eq_true hchk
  exact no_one_run_of_gap' ha hm (gap_mono (minLen_le hlt) hbase) heq

set_option exponentiation.threshold 6000 in
set_option maxRecDepth 100000 in
/-- **The sweep.**  Every run length `2 ≤ a < 2048` passes the test.  Kernel
computation, no floating point, no verified range. -/
theorem gapOK_sweep : ∀ a : Nat, a < 2048 → 2 ≤ a → gapOK a = true := by decide

/-- **No one-run cycle with `2 ≤ a < 2048`.**  Unconditional: the verified range
`m ≥ 307 200` is not used, only `m ≥ 1`. -/
theorem no_one_run_of_run_lt {m a L : Nat} (h2 : 2 ≤ a) (hlt : a < 2048) (hm : 0 < m)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) : False :=
  no_one_run_of_check (by omega) hm (gapOK_sweep a hlt h2) heq

/-- **The one-run classification below `a = 2048`.**  The trivial cycle is the
only one-run solution: `m = 1`, `a = 1`, `L = 2`. -/
theorem one_run_trivial {m a L : Nat} (ha : 0 < a) (hlt : a < 2048) (hm : 0 < m)
    (heq : 3 ^ a * (m + 1) = 2 ^ L * m + 2 ^ a) : m = 1 ∧ a = 1 ∧ L = 2 := by
  rcases Nat.lt_or_ge a 2 with h1 | h2
  · have ha1 : a = 1 := by omega
    subst ha1
    obtain ⟨hm1, hL⟩ := one_run_run_one hm heq
    exact ⟨hm1, rfl, hL⟩
  · exact absurd heq (fun h => (no_one_run_of_run_lt h2 hlt hm h).elim)

/-! ## Chained to actual cycles -/

/-- **No one-run cycle, from the run data.**  `j` odd steps from `m` followed by
pure halving back to `m`, with the gap hypothesis, is impossible. -/
theorem no_one_run_cycle {m j L : Nat} (hj : 0 < j) (hm : 0 < m) (hjL : j ≤ L)
    (hrun : OddRuns.OddRun m j) (hdesc : acceleratedOrbit j m = 2 ^ (L - j) * m)
    (hgap : 2 ^ L + 6 ^ j ≤ 2 ^ (L + j)) : False :=
  no_one_run_of_gap' hj hm hgap (OneRunCycle.one_run_equation hjL hrun hdesc)

/-- **No one-run cycle with a short run.**  Under `2 ≤ j < 2048` no gap
hypothesis is needed: the sweep supplies it. -/
theorem no_short_one_run_cycle {m j L : Nat} (h2 : 2 ≤ j) (hlt : j < 2048) (hm : 0 < m)
    (hjL : j ≤ L) (hrun : OddRuns.OddRun m j)
    (hdesc : acceleratedOrbit j m = 2 ^ (L - j) * m) : False :=
  no_one_run_of_run_lt h2 hlt hm (OneRunCycle.one_run_equation hjL hrun hdesc)

/-- **The accumulator of a one-run cycle is exactly `3 ^ a - 2 ^ a`.**  This is
the bridge to `CycleAccumulator.cycle_gap_mul`: the gap times the point is the
accumulator, and here the gap times the point is `3 ^ a - 2 ^ a`. -/
theorem oneRun_affineC {m L : Nat} (hm : 0 < m) (hcyc : AccIsCycleOf m L)
    (hrun : OddRuns.OddRun m (oddCount m L))
    (hdesc : acceleratedOrbit (oddCount m L) m = 2 ^ (L - oddCount m L) * m) :
    affineC L m + 2 ^ oddCount m L = 3 ^ oddCount m L := by
  obtain ⟨hapos, haL, hlt⟩ := accCycle_bounds hm hcyc
  have heq := OneRunCycle.one_run_equation (Nat.le_of_lt haL) hrun hdesc
  obtain ⟨d, hdpos, hd, hdm⟩ := one_run_gap (by omega) hm heq
  have hgapmul := CycleAccumulator.cycle_gap_mul hm hcyc
  have hgapeq : 2 ^ L - 3 ^ oddCount m L = d := by omega
  rw [hgapeq] at hgapmul
  omega

/-- **The order obstruction for an accelerated cycle.**  If the cycle is a single
odd run then its gap divides `2 ^ (L - a) - 1`. -/
theorem accCycle_gap_dvd_order {m L : Nat} (hm : 0 < m) (hcyc : AccIsCycleOf m L)
    (hrun : OddRuns.OddRun m (oddCount m L))
    (hdesc : acceleratedOrbit (oddCount m L) m = 2 ^ (L - oddCount m L) * m) :
    (2 ^ L - 3 ^ oddCount m L) ∣ (2 ^ (L - oddCount m L) - 1) := by
  obtain ⟨hapos, haL, hlt⟩ := accCycle_bounds hm hcyc
  exact one_run_order_dvd (by omega) hm
    (OneRunCycle.one_run_equation (Nat.le_of_lt haL) hrun hdesc)

/-- **The one-run accelerated cycle theorem.**  A positive accelerated cycle that
consists of a single odd run and whose run length passes the test is impossible;
and for `oddCount m L < 2048` the test is automatic unless the run has length
one, in which case the cycle is the trivial `1 → 2 → 1`. -/
theorem accCycle_one_run_trivial {m L : Nat} (hm : 0 < m) (hcyc : AccIsCycleOf m L)
    (hlt : oddCount m L < 2048)
    (hrun : OddRuns.OddRun m (oddCount m L))
    (hdesc : acceleratedOrbit (oddCount m L) m = 2 ^ (L - oddCount m L) * m) :
    m = 1 ∧ oddCount m L = 1 ∧ L = 2 := by
  obtain ⟨hapos, haL, _⟩ := accCycle_bounds hm hcyc
  exact one_run_trivial (by omega) hlt hm
    (OneRunCycle.one_run_equation (Nat.le_of_lt haL) hrun hdesc)

end OneRunOrder
end Collatz
