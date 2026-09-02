import Collatz.Strategy.StairGap

/-!
# The staircase development, parametric in the step

`Strategy.StairGap` proved, for the step `665`, that the gap
`gapAt a = 2 · 2 ^ (fexp a) − 3 ^ a` obeys an exact two-branch recurrence whose
branch is decided by the gap itself.  Nothing in that argument used `665`.  It
used only

* `2 ^ n < 3 ^ m` — so `δ = 3 ^ m − 2 ^ n` is a positive integer, and
* `3 ^ m < 2 ^ (n + 1)` — so `δ < 2 ^ n`,

i.e. exactly that `n = fexp m`.  This file states the development once over such
a pair, and instantiates it at the **next** one.

## Which pairs are useful

`δ / 3 ^ m` is how fast the normalised gap drains per rung, so a small ratio is a
long, expensive staircase.  Ratios at the convergent denominators of `log₂ 3`:

| `m` | `n = fexp m` | `δ / 3 ^ m` |
|---|---|---|
| `665` | `1054` | `4.365 · 10⁻⁵` |
| `15601` | `24726` | `0.5` — the other side, useless here |
| `31867` | `50508` | `7.265 · 10⁻⁶` |
| `79335` | `125742` | `0.5` — the other side |

The convergents alternate sides; the ladder rides the ones approaching from
below, `665` and then `31867`.  Last round predicted the sign would reverse at
the next level.  It does not: the reversal happens on the *dual* quantity
`3 ^ a − 2 ^ (fexp a)`, and on the gap itself the algebra repeats verbatim with
new constants.

## What the second level gives

The level-`665` staircase drains at `4.365 · 10⁻⁵` per rung and breaks at
`a = 15601` with `gapAt / 3 ^ a = 1.819 · 10⁻⁵` — that is the cliff
`StairGap.range_gt_142907493`.  Stepping by `31867` from there continues to
drain, at `7.265 · 10⁻⁶` per rung, through

    a = 15601 → 47468 → 79335,

with normalised gaps `1.819e−5`, `1.093e−5`, `3.665e−6`, and then it breaks.
Each is a new cliff for the certificate route, and the last is the deepest this
development reaches: **a certificate whose reach passes `79335` needs a verified
range above `3 608 044 635`.**
-/

namespace Collatz
namespace StairGeneric

open RealizableBound StairGap

/-! ## The parametric step -/

/-- `m` is a staircase step with shift `n` when `n = fexp m`, written as the two
comparisons the algebra actually uses. -/
structure Step (m n : Nat) : Prop where
  lo : (2:Nat) ^ n < 3 ^ m
  hi : (3:Nat) ^ m < 2 ^ (n + 1)

/-- The drain per rung, `3 ^ m − 2 ^ n`. -/
def delta (m n : Nat) : Nat := 3 ^ m - 2 ^ n

/-- The no-break criterion at `a` for the step `(m, n)`. -/
def NoBreak (m n a : Nat) : Prop := 3 ^ a * delta m n < 2 ^ n * gapAt a

theorem three_pow_eq {m n : Nat} (h : Step m n) : (3:Nat) ^ m = 2 ^ n + delta m n := by
  have := h.lo
  unfold delta
  omega

theorem delta_lt {m n : Nat} (h : Step m n) : delta m n < 2 ^ n := by
  have h1 := h.hi
  have h2 : (2:Nat) ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
  have h3 : 1 ≤ (2:Nat) ^ n := Nat.one_le_pow n 2 (by omega)
  unfold delta
  omega

/-- `2 ^ (fexp a + n + 1) = 2 · 2 ^ (fexp a) · 2 ^ n`. -/
theorem pow_split (a n : Nat) :
    (2:Nat) ^ (fexp a + n + 1) = 2 * 2 ^ fexp a * 2 ^ n := by
  rw [show fexp a + n + 1 = fexp a + 1 + n from by omega, Nat.pow_add,
    Nat.pow_succ, Nat.mul_comm (2 ^ fexp a) 2]

/-- The lower half of both branches. -/
theorem pow_le_shift {m n : Nat} (h : Step m n) (a : Nat) :
    (2:Nat) ^ (fexp a + n) ≤ 3 ^ (a + m) := by
  rw [Nat.pow_add 2 (fexp a) n, Nat.pow_add 3 a m]
  exact Nat.mul_le_mul (fexp_le a) (Nat.le_of_lt h.lo)

/-! ## The dichotomy -/

theorem fexp_step_noBreak {m n a : Nat} (h : Step m n) (hb : NoBreak m n a) :
    fexp (a + m) = fexp a + n := by
  refine RouteCap.fexp_eq_of (pow_le_shift h a) ?_
  have e2 : (3:Nat) ^ (a + m) = 3 ^ a * 3 ^ m := Nat.pow_add 3 a m
  have e4 : (3:Nat) ^ a * 3 ^ m = 3 ^ a * 2 ^ n + 3 ^ a * delta m n := by
    rw [three_pow_eq h, Nat.mul_add]
  have e5 : 2 * 2 ^ fexp a * 2 ^ n = gapAt a * 2 ^ n + 3 ^ a * 2 ^ n := by
    rw [← gapAt_add a, Nat.add_mul]
  have e6 : gapAt a * 2 ^ n = 2 ^ n * gapAt a := Nat.mul_comm _ _
  have e7 := pow_split a n
  unfold NoBreak at hb
  omega

theorem fexp_step_break {m n a : Nat} (h : Step m n)
    (hb : 2 ^ n * gapAt a ≤ 3 ^ a * delta m n) :
    fexp (a + m) = fexp a + n + 1 := by
  refine RouteCap.fexp_eq_of ?_ ?_
  · have e2 : (3:Nat) ^ (a + m) = 3 ^ a * 3 ^ m := Nat.pow_add 3 a m
    have e4 : (3:Nat) ^ a * 3 ^ m = 3 ^ a * 2 ^ n + 3 ^ a * delta m n := by
      rw [three_pow_eq h, Nat.mul_add]
    have e5 : 2 * 2 ^ fexp a * 2 ^ n = gapAt a * 2 ^ n + 3 ^ a * 2 ^ n := by
      rw [← gapAt_add a, Nat.add_mul]
    have e6 : gapAt a * 2 ^ n = 2 ^ n * gapAt a := Nat.mul_comm _ _
    have e7 := pow_split a n
    omega
  · have e2 : (3:Nat) ^ (a + m) = 3 ^ a * 3 ^ m := Nat.pow_add 3 a m
    have e8 : (2:Nat) ^ (fexp a + n + 1 + 1) = 2 ^ (fexp a + 1) * 2 ^ (n + 1) := by
      rw [show fexp a + n + 1 + 1 = fexp a + 1 + (n + 1) from by omega, Nat.pow_add]
    have hlt := lt_fexp a
    have hpos : 0 < (3:Nat) ^ m := by
      have := Nat.one_le_pow m 3 (by omega); omega
    have hstep : (3:Nat) ^ a * 3 ^ m < 2 ^ (fexp a + 1) * 3 ^ m :=
      Nat.mul_lt_mul_of_pos_right hlt hpos
    have hstep2 : (2:Nat) ^ (fexp a + 1) * 3 ^ m ≤ 2 ^ (fexp a + 1) * 2 ^ (n + 1) :=
      Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt h.hi)
    omega

/-! ## The two identities -/

/-- **The no-break recurrence, exactly.** -/
theorem gap_step {m n a : Nat} (h : Step m n) (hb : NoBreak m n a) :
    gapAt (a + m) + 3 ^ a * delta m n = 2 ^ n * gapAt a := by
  have hf := fexp_step_noBreak h hb
  have hdef : gapAt (a + m) = 2 * 2 ^ fexp (a + m) - 3 ^ (a + m) := rfl
  have hle : (3:Nat) ^ (a + m) ≤ 2 * 2 ^ fexp (a + m) := three_pow_le (a + m)
  have e2 : (3:Nat) ^ (a + m) = 3 ^ a * 3 ^ m := Nat.pow_add 3 a m
  have e4 : (3:Nat) ^ a * 3 ^ m = 3 ^ a * 2 ^ n + 3 ^ a * delta m n := by
    rw [three_pow_eq h, Nat.mul_add]
  have h3 : 2 * (2:Nat) ^ fexp (a + m) = 2 ^ n * (2 * 2 ^ fexp a) := by
    rw [hf, show fexp a + n = n + fexp a from by omega, Nat.pow_add,
      ← Nat.mul_assoc 2 (2 ^ n) (2 ^ fexp a), Nat.mul_comm 2 (2 ^ n), Nat.mul_assoc]
  have h2 : (2:Nat) ^ n * (gapAt a + 3 ^ a) = 2 ^ n * (2 * 2 ^ fexp a) := by
    rw [gapAt_add a]
  have h1 : (2:Nat) ^ n * (gapAt a + 3 ^ a) = 2 ^ n * gapAt a + 2 ^ n * 3 ^ a :=
    Nat.mul_add _ _ _
  have e12 : (2:Nat) ^ n * 3 ^ a = 3 ^ a * 2 ^ n := Nat.mul_comm _ _
  omega

/-- **The break recurrence, exactly.**  The gap resets upward. -/
theorem gap_break {m n a : Nat} (h : Step m n)
    (hb : 2 ^ n * gapAt a ≤ 3 ^ a * delta m n) :
    gapAt (a + m) = 2 ^ (n + 1) * gapAt a + 3 ^ a * (2 ^ n - delta m n) := by
  have hf := fexp_step_break h hb
  have hdef : gapAt (a + m) = 2 * 2 ^ fexp (a + m) - 3 ^ (a + m) := rfl
  have hle : (3:Nat) ^ (a + m) ≤ 2 * 2 ^ fexp (a + m) := three_pow_le (a + m)
  have e2 : (3:Nat) ^ (a + m) = 3 ^ a * 3 ^ m := Nat.pow_add 3 a m
  have e4 : (3:Nat) ^ a * 3 ^ m = 3 ^ a * 2 ^ n + 3 ^ a * delta m n := by
    rw [three_pow_eq h, Nat.mul_add]
  have h3 : 2 * (2:Nat) ^ fexp (a + m) = 2 ^ (n + 1) * (2 * 2 ^ fexp a) := by
    rw [hf, show fexp a + n + 1 = (n + 1) + fexp a from by omega, Nat.pow_add,
      ← Nat.mul_assoc 2 (2 ^ (n + 1)) (2 ^ fexp a), Nat.mul_comm 2 (2 ^ (n + 1)),
      Nat.mul_assoc]
  have h2 : (2:Nat) ^ (n + 1) * (gapAt a + 3 ^ a) = 2 ^ (n + 1) * (2 * 2 ^ fexp a) := by
    rw [gapAt_add a]
  have h1 : (2:Nat) ^ (n + 1) * (gapAt a + 3 ^ a)
      = 2 ^ (n + 1) * gapAt a + 2 ^ (n + 1) * 3 ^ a := Nat.mul_add _ _ _
  have e11 : (3:Nat) ^ a * (2 ^ n - delta m n) = 3 ^ a * 2 ^ n - 3 ^ a * delta m n :=
    Nat.mul_sub _ _ _
  have e13 : (3:Nat) ^ a * delta m n ≤ 3 ^ a * 2 ^ n :=
    Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt (delta_lt h))
  have e14 : (2:Nat) ^ (n + 1) * 3 ^ a = 3 ^ a * 2 ^ n + 3 ^ a * 2 ^ n := by
    have t1 : (2:Nat) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    rw [t1, Nat.add_mul, Nat.mul_comm (2 ^ n) (3 ^ a)]
  omega

/-! ## A run is finite -/

/-- `a` starts a run of at least `k` rungs of step `m`. -/
def Run (m n a k : Nat) : Prop := ∀ j : Nat, j < k → NoBreak m n (a + m * j)

set_option maxRecDepth 10000 in
theorem run_invariant {m n : Nat} (h : Step m n) (a : Nat) : ∀ k : Nat, Run m n a k →
    gapAt (a + m * k) * 3 ^ m + k * delta m n * (3 ^ a * 3 ^ (m * k))
      ≤ gapAt a * 3 ^ (m * k) * 3 ^ m := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hrun
    have hIH := ih (fun j hj => hrun j (by omega))
    have ha : a + m * (k + 1) = a + m * k + m := by rw [Nat.mul_succ]; omega
    have hstep : gapAt (a + m * (k + 1)) + 3 ^ (a + m * k) * delta m n
        = 2 ^ n * gapAt (a + m * k) := by
      have hs := gap_step h (m := m) (n := n) (a := a + m * k) (by
        have := hrun k (by omega); exact this)
      rw [← ha] at hs
      exact hs
    have hY : (3:Nat) ^ (a + m * k) = 3 ^ a * 3 ^ (m * k) := Nat.pow_add 3 a (m * k)
    have hW : (3:Nat) ^ (m * (k + 1)) = 3 ^ (m * k) * 3 ^ m := by
      rw [Nat.mul_succ, Nat.pow_add]
    rw [hW, ← Nat.mul_assoc (3 ^ a) (3 ^ (m * k)) (3 ^ m),
      ← Nat.mul_assoc (gapAt a) (3 ^ (m * k)) (3 ^ m)]
    rw [hY] at hstep
    exact StairGap.run_algebra (Nat.le_of_lt h.lo) hstep hIH

/-- **A run of step `m` has bounded length**: `k · δ · 3 ^ a ≤ gapAt a · 3 ^ m`. -/
theorem run_bound {m n a k : Nat} (h : Step m n) (hr : Run m n a k) :
    k * delta m n * 3 ^ a ≤ gapAt a * 3 ^ m := by
  have hinv := run_invariant h a k hr
  have hone : 1 ≤ (3:Nat) ^ (m * k) := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < (3:Nat) ^ (m * k) := by omega
  have hL : k * delta m n * (3 ^ a * 3 ^ (m * k))
      = k * delta m n * 3 ^ a * 3 ^ (m * k) := (Nat.mul_assoc _ _ _).symm
  have hR : gapAt a * 3 ^ (m * k) * 3 ^ m = gapAt a * 3 ^ m * 3 ^ (m * k) := by
    rw [Nat.mul_assoc, Nat.mul_comm (3 ^ (m * k)) (3 ^ m), ← Nat.mul_assoc]
  have hchain : k * delta m n * 3 ^ a * 3 ^ (m * k)
      ≤ gapAt a * 3 ^ m * 3 ^ (m * k) := by omega
  exact Nat.le_of_mul_le_mul_right hchain hpos

/-- A run longer than its budget is impossible, so a break occurs. -/
theorem break_within {m n a k : Nat} (h : Step m n)
    (hlt : gapAt a * 3 ^ m < k * delta m n * 3 ^ a) : ¬ Run m n a k := by
  intro hr
  have := run_bound h hr
  omega

/-! ## The two levels, as instances

`Step 665 1054` recovers everything in `Strategy.StairGap`; `Step 31867 50508` is
the next one, and it is what continues the ladder past `StairGap`'s cliff. -/

theorem step1 : Step 665 1054 :=
  ⟨StairGap.two_pow_lt_three_pow, StairGap.three_pow_lt_two_pow⟩

/-- `StairGap`'s `stairDelta` is this file's `delta` at the first step. -/
theorem delta_one : delta 665 1054 = StairGap.stairDelta := rfl

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem step2_lo : (2:Nat) ^ 50508 < 3 ^ 31867 := by decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem step2_hi : (3:Nat) ^ 31867 < 2 ^ (50508 + 1) := by decide

/-- **The second ladder-side staircase.**  `31867` is the next convergent
denominator of `log₂ 3` approaching from below, after `665`; the intervening one,
`15601`, approaches from above and gives `δ / 3 ^ m = 1/2`, useless here. -/
theorem step2 : Step 31867 50508 := ⟨step2_lo, step2_hi⟩

/-! ## The level-2 run: `15601 → 47468 → 79335`, then a break

`StairGap.break_at_15601` ends the level-1 staircase at `a = 15601` with
`gapAt / 3 ^ a = 1.819 · 10⁻⁵`.  Stepping by `31867` keeps draining, at
`7.265 · 10⁻⁶` a rung.  Note that `fexp` at `47468` and `79335` is *derived* from
the recurrence, not computed: no comparison at `125 743` bits is ever made to
establish it. -/

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem noBreak_15601 : NoBreak 31867 50508 15601 := by
  unfold NoBreak delta
  rw [StairGap.gapAt_15601]
  decide

theorem fexp_47468 : fexp 47468 = 75234 := by
  have h := fexp_step_noBreak step2 noBreak_15601
  rw [show (15601:Nat) + 31867 = 47468 from by omega, StairGap.fexp_15601] at h
  omega

theorem gapAt_47468 : gapAt 47468 = 2 * 2 ^ 75234 - 3 ^ 47468 := by
  unfold gapAt; rw [fexp_47468]

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem noBreak_47468 : NoBreak 31867 50508 47468 := by
  unfold NoBreak delta
  rw [gapAt_47468]
  decide

theorem fexp_79335 : fexp 79335 = 125742 := by
  have h := fexp_step_noBreak step2 noBreak_47468
  rw [show (47468:Nat) + 31867 = 79335 from by omega, fexp_47468] at h
  omega

theorem gapAt_79335 : gapAt 79335 = 2 * 2 ^ 125742 - 3 ^ 79335 := by
  unfold gapAt; rw [fexp_79335]

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem break_arith_79335 :
    2 ^ 50508 * (2 * 2 ^ 125742 - 3 ^ 79335) ≤ 3 ^ 79335 * (3 ^ 31867 - 2 ^ 50508) := by
  decide

/-- **The level-2 run ends at `79335`.**  Three rungs: `15601`, `47468`, `79335`. -/
theorem break_at_79335 : ¬ NoBreak 31867 50508 79335 := by
  intro h
  unfold NoBreak delta at h
  rw [gapAt_79335] at h
  have := break_arith_79335
  omega

/-! ## The new cliffs

`RouteCap.range_gt_of_reach` needs `2 ^ F ≤ 3 ^ a` and `3 ^ a < 2 ^ (F+1)`, which
`fexp_le` and `lt_fexp` supply once `fexp a` is known — and it is known from the
recurrence.  Only the witness inequality is a kernel computation. -/

theorem lo_47468 : (2:Nat) ^ 75234 ≤ 3 ^ 47468 := by
  have := fexp_le 47468; rw [fexp_47468] at this; exact this

theorem hi_47468 : (3:Nat) ^ 47468 < 2 ^ (75234 + 1) := by
  have := lt_fexp 47468; rw [fexp_47468] at this; exact this

theorem lo_79335 : (2:Nat) ^ 125742 ≤ 3 ^ 79335 := by
  have := fexp_le 79335; rw [fexp_79335] at this; exact this

theorem hi_79335 : (3:Nat) ^ 79335 < 2 ^ (125742 + 1) := by
  have := lt_fexp 79335; rw [fexp_79335] at this; exact this

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 200000 in
theorem wit_47468 :
    6 * 723837160 * (2 * 2 ^ 75234 - 3 ^ 47468) ≤ 47468 * 3 ^ 47468 := by decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 200000 in
theorem wit_79335 :
    6 * 3608044635 * (2 * 2 ^ 125742 - 3 ^ 79335) ≤ 79335 * 3 ^ 79335 := by decide

/-- A certificate reaching past `47468` needs a verified range above
`723 837 160`. -/
theorem range_gt_723837160 {c A : Nat} (hA : 47468 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    723837160 < c :=
  RouteCap.range_gt_of_reach hA lo_47468 hi_47468 wit_47468 hcert

/-- **The deepest cliff this development reaches.**  A certificate whose reach
passes `79335` needs a verified range above `3 608 044 635` — against the
`3 380 808` that reaches `8286`, a thousandfold for less than ten times the
reach.  `79335` is the last rung of the level-2 staircase (`break_at_79335`),
which is why the gap, and hence the price, is extremal there. -/
theorem range_gt_3608044635 {c A : Nat} (hA : 79335 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    3608044635 < c :=
  RouteCap.range_gt_of_reach hA lo_79335 hi_79335 wit_79335 hcert

end StairGeneric
end Collatz
