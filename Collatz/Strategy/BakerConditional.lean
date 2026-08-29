import Collatz.Strategy.HorizonSharp

/-!
# The external input, named — and exactly what it buys

Five rounds have concluded that what remains is an effective lower bound on
`|L log 2 − a log 3|`.  That is a statement this development cannot prove.  It
*can* be named, and what follows from it can be proved.  This file does that, and
then proves the limitation: **naming it is not enough.**

## The input

Write a cycle's gap as `2 ^ L = 3 ^ a + G`, `G > 0`.  A linear-forms bound says
`Λ = L log 2 − a log 3` is not too small, and since `Λ ≈ G / 3 ^ a`, its integer
shape is a function `f` with

`3 ^ a ≤ f a · G`     for every legal `(L, a, G)`   (`EffectiveGap f`).

Baker–Wüstholz / Matveev give such an `f`, polynomial in `a`, with an effective
constant.  Nothing here assumes a particular one.

## What it buys — `conditional_cycle_bound`

For a cycle of minimum `m` and odd-count `a` satisfying the product bound, and in
the range `2a ≤ 3m`:

**`EffectiveGap f  →  3m ≤ 2 · a · f a`.**

With the polynomial `f a = a ^ C` this is `3m ≤ 2 · a ^ (C+1)`
(`baker_polynomial`), i.e.

`a ≥ (3m / 2) ^ (1/(C+1))`.

**A lower bound on the cycle's odd-count, not an exclusion.**  That is genuinely
what this route yields, and it is the shape of the Steiner / Simons–de Weger
results the repository already carries at `length_ge_6809`.

## What it does not buy, and this is the point

The hypothesis `2a ≤ 3m` is not a convenience.  Round XXI proved the product bound
**vacuous** for `a ≥ 0.76 · 3m = 2.28 m` (`HorizonSharp.product_bound_vacuous_sharp`,
re-exported here as `no_input_beyond_horizon`).  Beyond the horizon the product
bound holds automatically, so it carries no information, so
`conditional_cycle_bound` has **no input to consume — for any `f` whatsoever**.

So the situation, stated exactly:

| region | status |
|---|---|
| `a ≤ 1.5 m` | `EffectiveGap f` gives `3m ≤ 2 a f a` |
| `1.5 m < a < 2.28 m` | covered by neither statement |
| `a ≥ 2.28 m` | product bound provably vacuous; **no `f` helps** |

**An effective linear-forms bound, combined with the product family, provably
cannot exclude cycles with large odd-count.**  That is not a limitation of Baker's
theorem; it is a limitation of the family it would be fed into.  Whatever closes
the cycle half must bring a second constraint that survives past `a ≈ 2.28 m`, and
no such constraint exists anywhere in this repository.

This is the specification a solution has to meet, and it is now a theorem rather
than a summary.
-/

namespace Collatz
namespace BakerConditional

open HorizonSharp ProductCeiling

/-! ## Two elementary power estimates -/

/-- Telescoping the binomial: `(x+1) ^ (a+1) ≤ x ^ (a+1) + (a+1) · (x+1) ^ a`. -/
theorem pow_succ_diff : ∀ (a x : Nat), (x + 1) ^ (a + 1) ≤ x ^ (a + 1) + (a + 1) * (x + 1) ^ a := by
  intro a
  induction a with
  | zero => intro x; simp
  | succ a ih =>
    intro x
    have hexpand : (x ^ (a + 1) + (a + 1) * (x + 1) ^ a) * (x + 1)
        = x ^ (a + 1 + 1) + x ^ (a + 1) + (a + 1) * (x + 1) ^ (a + 1) := by
      have e1 : x ^ (a + 1) * (x + 1) = x ^ (a + 1 + 1) + x ^ (a + 1) := by
        rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_succ]
      have e2 : (a + 1) * (x + 1) ^ a * (x + 1) = (a + 1) * (x + 1) ^ (a + 1) := by
        rw [Nat.mul_assoc, ← Nat.pow_succ]
      rw [Nat.add_mul, e1, e2]
    have hchain : (x + 1) ^ (a + 1 + 1)
        ≤ x ^ (a + 1 + 1) + x ^ (a + 1) + (a + 1) * (x + 1) ^ (a + 1) := by
      calc (x + 1) ^ (a + 1 + 1) = (x + 1) ^ (a + 1) * (x + 1) := Nat.pow_succ _ _
        _ ≤ (x ^ (a + 1) + (a + 1) * (x + 1) ^ a) * (x + 1) :=
            Nat.mul_le_mul_right _ (ih x)
        _ = x ^ (a + 1 + 1) + x ^ (a + 1) + (a + 1) * (x + 1) ^ (a + 1) := hexpand
    have hsmall : x ^ (a + 1) ≤ (x + 1) ^ (a + 1) := Nat.pow_le_pow_left (by omega) _
    have hcoef : (a + 1 + 1) * (x + 1) ^ (a + 1)
        = (a + 1) * (x + 1) ^ (a + 1) + (x + 1) ^ (a + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **The reciprocal Bernoulli.**  `(x+1) ^ A · (x − A) ≤ x ^ (A+1)`, written with
`x = A + y` so no subtraction appears.  This is the upper bound on `(1 + 1/x) ^ A`
that Bernoulli does not give. -/
theorem pow_ratio_le : ∀ (A y : Nat), 1 ≤ y →
    (A + y + 1) ^ A * y ≤ (A + y) ^ (A + 1) := by
  intro A
  induction A with
  | zero => intro y hy; simp
  | succ A ih =>
    intro y hy
    have hrec := ih (y + 1) (by omega)
    -- `hrec : (A + (y+1) + 1) ^ A * (y+1) ≤ (A + (y+1)) ^ (A+1)`
    have hx1 : A + (y + 1) + 1 = (A + 1 + y) + 1 := by omega
    have hx2 : A + (y + 1) = A + 1 + y := by omega
    rw [hx1, hx2] at hrec
    -- key linear step: `((A+1+y)+1) * y ≤ (A+1+y) * (y+1)`
    have hlin : ((A + 1 + y) + 1) * y ≤ (A + 1 + y) * (y + 1) := by
      have e1 : ((A + 1 + y) + 1) * y = (A + 1 + y) * y + y := by
        rw [Nat.add_mul, Nat.one_mul]
      have e2 : (A + 1 + y) * (y + 1) = (A + 1 + y) * y + (A + 1 + y) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    calc ((A + 1 + y) + 1) ^ (A + 1) * y
        = ((A + 1 + y) + 1) ^ A * (((A + 1 + y) + 1) * y) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ ((A + 1 + y) + 1) ^ A * ((A + 1 + y) * (y + 1)) :=
          Nat.mul_le_mul_left _ hlin
      _ = (((A + 1 + y) + 1) ^ A * (y + 1)) * (A + 1 + y) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ (A + 1 + y) ^ (A + 1) * (A + 1 + y) := Nat.mul_le_mul_right _ hrec
      _ = (A + 1 + y) ^ (A + 1 + 1) := (Nat.pow_succ _ _).symm

/-- **The ratio stays under two below half the base.**  `2A ≤ x` gives
`(x+1) ^ A ≤ 2 · x ^ A`.  The exact converse of `HorizonSharp`: there the ratio
is shown to *pass* two, here to *stay under* it. -/
theorem pow_le_two_mul {A x : Nat} (hx : 0 < x) (h : 2 * A ≤ x) :
    (x + 1) ^ A ≤ 2 * x ^ A := by
  have hAx : A ≤ x := by omega
  obtain ⟨y, hy⟩ : ∃ y, x = A + y := ⟨x - A, by omega⟩
  have hy1 : 1 ≤ y := by omega
  have hr := pow_ratio_le A y hy1
  rw [← hy] at hr
  -- `hr : (x+1) ^ A * y ≤ x ^ (A+1)`
  have hdouble : (x + 1) ^ A * x ≤ (x + 1) ^ A * (2 * y) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : (x + 1) ^ A * (2 * y) = 2 * ((x + 1) ^ A * y) := by
    rw [Nat.mul_left_comm]
  have hchain : (x + 1) ^ A * x ≤ 2 * x ^ (A + 1) := by
    rw [hexp] at hdouble
    have : 2 * ((x + 1) ^ A * y) ≤ 2 * x ^ (A + 1) := Nat.mul_le_mul_left _ hr
    omega
  have hsplit : 2 * x ^ (A + 1) = 2 * x ^ A * x := by
    rw [Nat.pow_succ, Nat.mul_assoc]
  rw [hsplit] at hchain
  exact Nat.le_of_mul_le_mul_right hchain hx

/-! ## The named external input -/

/-- **An effective linear-forms bound, in integer shape.**  `f` bounds how small
the gap `G = 2 ^ L − 3 ^ a` can be relative to `3 ^ a`.  Baker–Wüstholz supplies
such an `f`, polynomial in `a`; nothing below assumes which one. -/
def EffectiveGap (f : Nat → Nat) : Prop :=
  ∀ L a G : Nat, 1 ≤ a → 0 < G → 2 ^ L = 3 ^ a + G → 3 ^ a ≤ f a * G

/-! ## What it buys -/

/-- **The conditional cycle bound.**  Given an effective gap bound `f`, a cycle of
minimum `m` and odd-count `a` obeying the product bound, in the range `2a ≤ 3m`,
satisfies `3m ≤ 2 · a · f a`.

Read as a bound on `a`: the odd-count of a cycle cannot be too small relative to
the verified range.  It is a *lower* bound on `a`, not an exclusion. -/
theorem conditional_cycle_bound {f : Nat → Nat} (hf : EffectiveGap f)
    {m A L G : Nat} (hm : 0 < m) (hGpos : 0 < G)
    (hG : 2 ^ L = 3 ^ (A + 1) + G)
    (hprod : 2 ^ L * m ^ (A + 1) ≤ (3 * m + 1) ^ (A + 1))
    (hsmall : 2 * (A + 1) ≤ 3 * m) :
    3 * m ≤ 2 * (A + 1) * f (A + 1) := by
  have hgap := hf L (A + 1) G (by omega) hGpos hG
  have hxpos : 0 < 3 * m := by omega
  have hsplit : (3 * m) ^ (A + 1) = 3 ^ (A + 1) * m ^ (A + 1) := Nat.mul_pow 3 m (A + 1)
  -- the product bound with the gap split out
  have hstep1 : (3 * m) ^ (A + 1) + G * m ^ (A + 1) ≤ (3 * m + 1) ^ (A + 1) := by
    rw [hG] at hprod
    have hdist : (3 ^ (A + 1) + G) * m ^ (A + 1)
        = 3 ^ (A + 1) * m ^ (A + 1) + G * m ^ (A + 1) := Nat.add_mul _ _ _
    rw [hsplit]
    omega
  -- telescoping the right-hand side
  have hstep2 := pow_succ_diff A (3 * m)
  have hstep3 : G * m ^ (A + 1) ≤ (A + 1) * (3 * m + 1) ^ A := by omega
  -- feed in the effective bound
  have hstep4 : 3 ^ (A + 1) * m ^ (A + 1) ≤ f (A + 1) * (G * m ^ (A + 1)) := by
    have h1 : 3 ^ (A + 1) * m ^ (A + 1) ≤ (f (A + 1) * G) * m ^ (A + 1) :=
      Nat.mul_le_mul_right _ hgap
    rw [Nat.mul_assoc] at h1
    exact h1
  have hstep5 : (3 * m) ^ (A + 1) ≤ f (A + 1) * ((A + 1) * (3 * m + 1) ^ A) := by
    have h1 : f (A + 1) * (G * m ^ (A + 1)) ≤ f (A + 1) * ((A + 1) * (3 * m + 1) ^ A) :=
      Nat.mul_le_mul_left _ hstep3
    rw [hsplit]
    exact Nat.le_trans hstep4 h1
  -- the reciprocal Bernoulli removes the `+1`
  have hratio : (3 * m + 1) ^ A ≤ 2 * (3 * m) ^ A := pow_le_two_mul hxpos (by omega)
  have hstep6 : (3 * m) ^ (A + 1) ≤ (2 * (A + 1) * f (A + 1)) * (3 * m) ^ A := by
    have h1 : f (A + 1) * ((A + 1) * (3 * m + 1) ^ A)
        ≤ f (A + 1) * ((A + 1) * (2 * (3 * m) ^ A)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hratio)
    have h2 : f (A + 1) * ((A + 1) * (2 * (3 * m) ^ A))
        = (2 * (A + 1) * f (A + 1)) * (3 * m) ^ A := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [← h2]
    exact Nat.le_trans hstep5 h1
  -- cancel the common power
  have hpowsplit : (3 * m) ^ (A + 1) = (3 * m) * (3 * m) ^ A := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hApos : 0 < (3 * m) ^ A := Nat.pow_pos hxpos
  rw [hpowsplit] at hstep6
  exact Nat.le_of_mul_le_mul_right hstep6 hApos

/-- **The polynomial case.**  With Baker's `f a = a ^ C`, a cycle in range
satisfies `3m ≤ 2 · a ^ (C+1)` — equivalently `a ≥ (3m/2) ^ (1/(C+1))`.  A lower
bound on the odd-count, which is what this route actually yields. -/
theorem baker_polynomial {C : Nat} (hf : EffectiveGap (fun a => a ^ C))
    {m A L G : Nat} (hm : 0 < m) (hGpos : 0 < G)
    (hG : 2 ^ L = 3 ^ (A + 1) + G)
    (hprod : 2 ^ L * m ^ (A + 1) ≤ (3 * m + 1) ^ (A + 1))
    (hsmall : 2 * (A + 1) ≤ 3 * m) :
    3 * m ≤ 2 * (A + 1) ^ (C + 1) := by
  have h := conditional_cycle_bound hf hm hGpos hG hprod hsmall
  have he : 2 * (A + 1) * (A + 1) ^ C = 2 * (A + 1) ^ (C + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm ((A + 1) ^ C) (A + 1), Nat.mul_assoc]
  omega

/-! ## What it does not buy -/

/-- **No input beyond the horizon.**  Past `a ≈ 2.28 m` the product bound holds
outright (Round XXI), so it is not a constraint, so `conditional_cycle_bound` has
nothing to consume — **whatever `f` is**.  An effective linear-forms bound,
combined with the product family, cannot reach cycles of large odd-count. -/
theorem no_input_beyond_horizon {m a k K : Nat} (hm : 0 < m)
    (hk : 19 * (3 * m) ≤ 100 * k) (ha : k * 4 ≤ a) (hK : 2 ^ K ≤ 3 ^ a) :
    2 ^ (K + 1) * m ^ a ≤ (3 * m + 1) ^ a :=
  HorizonSharp.product_bound_vacuous_sharp hm hk ha hK

/-- **The two regions do not meet.**  `conditional_cycle_bound` needs `2a ≤ 3m`;
the horizon starts at `a ≥ 0.76 · 3m`.  Since `1/2 < 0.76`, there is a band
`1.5 m < a < 2.28 m` on which neither theorem says anything.  Stated as the
arithmetic fact that the two side conditions are incompatible: no `a` satisfies
both. -/
theorem regions_disjoint {m a k : Nat} (hm : 0 < m)
    (hk : 19 * (3 * m) ≤ 100 * k) (hhor : k * 4 ≤ a) (hsmall : 2 * a ≤ 3 * m) :
    False := by
  -- `a ≥ 4k ≥ 4·(57m/100)` forces `2a ≥ 4.56 m > 3 m`
  have hk' : 57 * m ≤ 100 * k := by omega
  have h1 : 100 * (k * 4) = 400 * k := by omega
  have h2 : 228 * m ≤ 400 * k := by omega
  have h3 : 400 * k ≤ 100 * a := by omega
  omega

end BakerConditional
end Collatz
