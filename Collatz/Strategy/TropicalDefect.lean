import Collatz.Strategy.NewModels

/-!
# The tropical shadow, its defect, and why the coupling has rank one

Round IX's postscript named the surviving object of this development:

> `r j = C j / (3 ^ (A j) * n)` — the accumulator measured against the orbit,
> a quantity that is a function of neither the `2`-adic datum nor the archimedean
> one alone.

This file is a geometer's report on that object, and it is a **negative** one, with
an exact accounting of where the information goes.  Three things are established.

## 1.  Tropicalisation is exactly the map "forget `d`", and its defect is exactly `r`

Write the exact affine law for `3x + d` (`DenominatorScalar.gen_affine_exact`) as

`2 ^ j * x_j = 3 ^ (A j) * x + d * U j`.

Tropicalising in the archimedean (Maslov) sense replaces the sum by its dominant
term.  Define the two pieces:

* `tropShadow d j x = 3 ^ (A j) * x` — the value the orbit would have at `d = 0`;
* `tropDefect d j x = d * U j` — everything tropicalisation throws away.

Then `trop_sandwich` says the tropical value is correct **to within one bit**:

`max shadow defect ≤ 2 ^ j * x_j ≤ 2 * max shadow defect`,

and `trop_error_is_min` says the discarded quantity is precisely the *other* branch,
`min shadow defect`.  Furthermore `trop_within_one_bit_iff` shows that the tropical
error is under a bit measured against the shadow exactly when `defect < shadow`,
i.e. exactly when `r j < 1`.  So:

> **The tropicalisation defect of the Collatz affine law is exactly the coupling
> `r`, and the one-bit sandwich is exactly `Discrepancy.bridge_two_sided`.**

That is the whole tropical contribution, and it is a closure, not an opening: the
tropical shadow `3 ^ (A j) * x` is a function of the parity word and the magnitude
separately, hence lies in Class 1 of `CLOSURE.md`; and the `d = 0` map is `d`-free
by construction, hence lies in Class 4.  A tropical mechanism is refuted before it
is written.  There is no tropical vertex to exploit either: the "min attained twice"
locus of the cycle equation over `Q_2` is `t_1 = 0`, i.e. *the cycle minimum is odd*,
which the development already has.

## 2.  The coupling has rank one — a new death screen

`CLOSURE.md` lists two diagnostics: additivity (`disc_append`) and the complete
invariant (`wC_inj`).  This file adds a third, and it is the one that kills discrete
curvature.

`word_determines` proves that the pair `(A j, U j)` is a function of the parity
sequence alone — the same word gives the same `A` and the same `U`, for **every**
constant `d` and **every** starting point.  Since `C = d * U`, the coupling factors:

> `r j = (d / x) * (U j / 3 ^ (A j))` — **one archimedean scalar times one
> word-determined path.**

`coupling_determined_by_scale` is that statement: two orbits with the same word and
the same scale `d / x` have *identical* coupling paths, pointwise, at every `j`.
So the coupling — a path — carries exactly **one** real number of archimedean
information, namely `lambda = d / x`, and nothing else.

**The screen.**  Any statistic of the coupling path that is homogeneous of degree
zero — every discrete curvature, turning angle, torsion, cross-ratio, or projective
invariant, since all of these are by definition invariant under rescaling the path —
is independent of `lambda`, hence a function of the word alone, hence `d`-free, hence
refuted by the genuine cycles of `3x - 1`, `3x + 5`, `3x + 7`, `3x + 11`, `3x + 13`.

> **Diagnostic 3 (homogeneity).**  If a proposed invariant of the coupling is
> scale-invariant, it is dead.  This kills curvature *before* the additivity screen
> has to be consulted, and it kills it whether or not the curvature is additive.

`coupling_d_blind` is the concrete witness: at the scaled point `d * x` the coupling
of `3x + d` equals the coupling of `3x + 1` at `x`, pointwise, for every `j`.

## 3.  What is left: the scale, and the normal form it satisfies

If the coupling contributes exactly one number, the only possible theorem is an
inequality on that number.  Section 3 derives the sharp one.

`genU_cap` is the exact bound on the unit accumulator,

`2 ^ (A j) * U j + 2 ^ j * 2 ^ (A j) <= 2 ^ j * 3 ^ (A j)`,

equivalently `U j <= 2 ^ j * ((3/2) ^ (A j) - 1)`, with **equality at the all-odd
word**.  *This is not new*: at `d = 1` it is exactly
`AccumulatorSharp.affineC_shortfall`, found in the index after the fact.  What is
added here is only its extension to every `3x + d`, which the argument below needs
in order to be checked against the soundness filter.  Recorded as a duplicate with
a generalisation, not as a discovery.

Pairing it with non-descent (`never_drops_affine`) gives the **normal form**: on any
orbit that has not dropped below its start by step `j`,

`2 ^ (A j) * x * (2 ^ j - 3 ^ (A j)) <= d * 2 ^ j * (3 ^ (A j) - 2 ^ (A j))`,

stated subtraction-free as `normal_form`.  Every orbit segment reduces to this single
scalar inequality between one word functional and one archimedean number; that is the
canonical representation the mandate asked for, and an infinite non-descending
trajectory is precisely a trajectory satisfying it at every `j`.

The consequence, `light_bounds_start`, consumes assets (a), (c) and (d):

> if the orbit of `x` under `3x + 1` has not dropped below `x` by step `j`, and the
> prefix is **light by a full bit** (`2 * 3 ^ (A j) <= 2 ^ j`), then
> `2 ^ (A j) * x + 2 ^ (A j + 1) <= 2 * 3 ^ (A j)`.

With the verified range `x >= 1086464` this forces `A j >= 33`
(`light_forces_thirty_three`), hence `j >= 54`.  So a non-descending orbit above the
verified range cannot be a full bit light before step `54`.

`no_light_scale_generalised` shows this really does extend
`Structure.MinimalHeavy.no_light_scale`: under that theorem's extra hypothesis
`2 ^ j <= x` — which confines it to `j <= 20` at the verified range —
`light_bounds_start` gives an outright contradiction, and without it still gives the
odd-count bound.  It also drops the minimality hypothesis for plain non-descent.

**Two honest limitations, stated because they matter more than the theorem.**
First, this is the same asset in new coordinates: it is what "the verified range is
worth `L = 183` of `6809`" looks like locally, and it does not escape it.  Second,
and worse, it is far from the truth.  Measured on `3000` random starts above
`1086464`, the maximum of `2 ^ j / 3 ^ (A j)` over *all* non-descending prefixes is
`1` — non-descending prefixes are never light **at all**, not merely never light by a
full bit.  So the normal form recovers a factor-`2` shadow of a statement that is
empirically exact.  The gap is precisely the coupling `r`, and by the rank-one
theorem above the coupling contributes only `1 / x`, which at `x >= 1086464` is too
small to close it.  That is the mechanism of the failure, and it is the same
mechanism as everywhere else in this development.
-/

namespace Collatz
namespace TropicalDefect

open Reach Denominator DenominatorScalar NewModels

/-! ## 1.  The tropical shadow and its defect -/

/-- At `d = 1` the generalised odd count is the development's `oddCount`. -/
theorem genOddCount_one (j x : Nat) : genOddCount 1 j x = oddCount x j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have horb : genOrbit 1 j x = acceleratedOrbit j x := genOrbit_one j x
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have h1 : genOddCount 1 (j + 1) x = genOddCount 1 j x := by
        rw [genOddCount, if_neg (by rw [horb]; omega), Nat.add_zero]
      omega
    · have h1 : genOddCount 1 (j + 1) x = genOddCount 1 j x + 1 := by
        rw [genOddCount, if_pos (by rw [horb]; exact ho)]
      omega

/-- The tropical (Maslov) shadow of `2 ^ j * x_j`: the value at `d = 0`, i.e. the
term the archimedean tropicalisation keeps when the orbit dominates. -/
def tropShadow (d j x : Nat) : Nat := 3 ^ genOddCount d j x * x

/-- The tropicalisation defect: everything the shadow discards.  It is the
accumulator, hence exactly the numerator of the coupling `r`. -/
def tropDefect (d j x : Nat) : Nat := d * genU d j x

/-- **Shadow plus defect is exact.**  The affine law, read as a tropical
decomposition. -/
theorem trop_exact {d : Nat} (hd : d % 2 = 1) (j x : Nat) :
    2 ^ j * genOrbit d j x = tropShadow d j x + tropDefect d j x :=
  gen_affine_exact hd x j

/-- **The tropical value is correct to within one bit.**  This is the
logarithm-free form of `bridge_two_sided`, obtained from tropical geometry alone. -/
theorem trop_sandwich {d : Nat} (hd : d % 2 = 1) (j x : Nat) :
    max (tropShadow d j x) (tropDefect d j x) ≤ 2 ^ j * genOrbit d j x ∧
      2 ^ j * genOrbit d j x ≤ 2 * max (tropShadow d j x) (tropDefect d j x) := by
  rw [trop_exact hd j x]
  omega

/-- **The information tropicalisation destroys is exactly the subdominant branch.**
Nothing else is lost, and the loss is an equality, not an estimate. -/
theorem trop_error_is_min {d : Nat} (hd : d % 2 = 1) (j x : Nat) :
    2 ^ j * genOrbit d j x - max (tropShadow d j x) (tropDefect d j x)
      = min (tropShadow d j x) (tropDefect d j x) := by
  rw [trop_exact hd j x]
  omega

/-- **The tropical error is under one bit against the shadow exactly when the
coupling is `< 1`.**  So the open bit of `bridge_two_sided` and the tropicalisation
defect are the same object, not merely comparable ones. -/
theorem trop_within_one_bit_iff {d : Nat} (hd : d % 2 = 1) (j x : Nat) :
    2 ^ j * genOrbit d j x < 2 * tropShadow d j x ↔
      tropDefect d j x < tropShadow d j x := by
  rw [trop_exact hd j x]
  omega

/-- The shadow and the defect are **jointly homogeneous of degree one** in `d` along
the scaled ray.  So the tropical picture cannot see `d` at all: it rescales. -/
theorem trop_scaling {d : Nat} (hd : d % 2 = 1) (j x : Nat) :
    tropShadow d j (d * x) = d * tropShadow 1 j x ∧
      tropDefect d j (d * x) = d * tropDefect 1 j x := by
  have h := gen_scale_data hd j x
  constructor
  · show 3 ^ genOddCount d j (d * x) * (d * x) = d * (3 ^ genOddCount 1 j x * x)
    rw [h.1, genOddCount_one]
    ac_rfl
  · show d * genU d j (d * x) = d * (1 * genU 1 j x)
    rw [h.2, genU_one, Nat.one_mul]

/-! ## 2.  The word determines the pair `(A, U)`: the coupling has rank one -/

/-- **The parity word determines the odd count and the unit accumulator.**  Two
orbits — of *any* two constants, from *any* two starting points — that read the same
parity sequence carry the same `A` and the same `U`.

This is the rank-one factorisation of the coupling: `r j = (d / x) * (U j / 3 ^ A j)`
with the second factor a pure word function. -/
theorem word_determines {d d' x x' : Nat} : ∀ j : Nat,
    (∀ i, i < j → genOrbit d i x % 2 = genOrbit d' i x' % 2) →
      genOddCount d j x = genOddCount d' j x' ∧ genU d j x = genU d' j x' := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro hw
    have hprev : ∀ i, i < j → genOrbit d i x % 2 = genOrbit d' i x' % 2 :=
      fun i hi => hw i (Nat.lt_succ_of_lt hi)
    have hlast : genOrbit d j x % 2 = genOrbit d' j x' % 2 := hw j (Nat.lt_succ_self j)
    have hA := (ih hprev).1
    have hU := (ih hprev).2
    rcases Arith.mod_two_eq_zero_or_one (genOrbit d j x) with he | ho
    · have he' : genOrbit d' j x' % 2 = 0 := by rw [← hlast]; exact he
      have hcA : genOddCount d (j + 1) x = genOddCount d j x := by
        rw [genOddCount, if_neg (by omega), Nat.add_zero]
      have hcA' : genOddCount d' (j + 1) x' = genOddCount d' j x' := by
        rw [genOddCount, if_neg (by omega), Nat.add_zero]
      exact ⟨by rw [hcA, hcA', hA],
        by rw [genU_even he, genU_even he', hU]⟩
    · have ho' : genOrbit d' j x' % 2 = 1 := by rw [← hlast]; exact ho
      have hcA : genOddCount d (j + 1) x = genOddCount d j x + 1 := by
        rw [genOddCount, if_pos ho]
      have hcA' : genOddCount d' (j + 1) x' = genOddCount d' j x' + 1 := by
        rw [genOddCount, if_pos ho']
      exact ⟨by rw [hcA, hcA', hA],
        by rw [genU_odd ho, genU_odd ho', hU]⟩

/-- **The coupling path is determined by the word and the single scalar `d / x`.**

Cross-multiplied so that no division occurs: `defect / shadow` at `(d, x)` equals
`defect / shadow` at `(d', x')`, at *every* `j`, as soon as the words agree and the
scales agree.

So the object Round IX named — a path coupling the `2`-adic and archimedean data —
contributes exactly **one** number of archimedean information.  It has rank one. -/
theorem coupling_determined_by_scale {d d' x x' : Nat} (hscale : d * x' = d' * x)
    {j : Nat} (hw : ∀ i, i < j → genOrbit d i x % 2 = genOrbit d' i x' % 2) :
    tropDefect d j x * tropShadow d' j x' = tropDefect d' j x' * tropShadow d j x := by
  have h := word_determines j hw
  show d * genU d j x * (3 ^ genOddCount d' j x' * x')
      = d' * genU d' j x' * (3 ^ genOddCount d j x * x)
  rw [← h.1, ← h.2]
  calc d * genU d j x * (3 ^ genOddCount d j x * x')
      = genU d j x * 3 ^ genOddCount d j x * (d * x') := by ac_rfl
    _ = genU d j x * 3 ^ genOddCount d j x * (d' * x) := by rw [hscale]
    _ = d' * genU d j x * (3 ^ genOddCount d j x * x) := by ac_rfl

/-- **The coupling is `d`-blind on the scaled ray.**  The coupling of `3x + d` at
`d * x` is pointwise equal to the coupling of `3x + 1` at `x`.  Concrete witness for
the homogeneity screen. -/
theorem coupling_d_blind {d : Nat} (hd : d % 2 = 1) (j x : Nat) :
    tropDefect d j (d * x) * tropShadow 1 j x
      = tropDefect 1 j x * tropShadow d j (d * x) := by
  have hs := trop_scaling hd j x
  rw [hs.1, hs.2]
  ac_rfl

/-! ## 3.  The cap, the normal form, and the one asset it consumes -/

/-- Pure arithmetic step for the even branch of `genU_cap`. -/
theorem cap_step_even (P Q W U : Nat) (h : P * U + W * P ≤ W * Q) :
    P * U + 2 * W * P ≤ 2 * W * Q := by
  have e2 : 2 * W * P = 2 * (W * P) := by ac_rfl
  have e3 : 2 * W * Q = 2 * (W * Q) := by ac_rfl
  rw [e2, e3]; omega

/-- Pure arithmetic step for the odd branch of `genU_cap`.  The cap is *exactly*
preserved here — this inequality is an equality when the hypothesis is. -/
theorem cap_step_odd (P Q W U : Nat) (h : P * U + W * P ≤ W * Q) :
    2 * P * (3 * U + W) + 2 * W * (2 * P) ≤ 2 * W * (3 * Q) := by
  have e1 : 2 * P * (3 * U + W) = 2 * 3 * (P * U) + 2 * (W * P) := by
    rw [Nat.mul_add]; ac_rfl
  have e2 : 2 * W * (2 * P) = 2 * 2 * (W * P) := by ac_rfl
  have e3 : 2 * W * (3 * Q) = 2 * 3 * (W * Q) := by ac_rfl
  rw [e1, e2, e3]; omega

/-- **The sharp cap on the unit accumulator.**  Subtraction-free form of

`2 ^ A * U ≤ 2 ^ j * (3 ^ A - 2 ^ A)`,

with equality at the all-odd word.  At `d = 1` this **is**
`AccumulatorSharp.affineC_shortfall`; the content here is only that it holds for
every constant `d`, with the same word data, so the normal form below can be tested
against the soundness filter. -/
theorem genU_cap (d : Nat) : ∀ (j x : Nat),
    2 ^ genOddCount d j x * genU d j x + 2 ^ j * 2 ^ genOddCount d j x
      ≤ 2 ^ j * 3 ^ genOddCount d j x := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ j ih =>
    intro x
    have hIH := ih x
    rcases Arith.mod_two_eq_zero_or_one (genOrbit d j x) with he | ho
    · have hcA : genOddCount d (j + 1) x = genOddCount d j x := by
        rw [genOddCount, if_neg (by omega), Nat.add_zero]
      rw [hcA, genU_even he, Arith.two_pow_succ]
      exact cap_step_even _ _ _ _ hIH
    · have hcA : genOddCount d (j + 1) x = genOddCount d j x + 1 := by
        rw [genOddCount, if_pos ho]
      rw [hcA, genU_odd ho, Arith.two_pow_succ, Arith.two_pow_succ,
        Arith.three_pow_succ]
      exact cap_step_odd _ _ _ _ hIH

/-- Non-descent at step `j`, expressed against the affine law. -/
theorem never_drops_affine {d : Nat} (hd : d % 2 = 1) {j x : Nat}
    (hnd : x ≤ genOrbit d j x) :
    2 ^ j * x ≤ 3 ^ genOddCount d j x * x + d * genU d j x := by
  rw [← gen_affine_exact hd x j]
  exact Nat.mul_le_mul_left _ hnd

/-- **The normal form of an orbit segment.**  Subtraction-free statement of

`2 ^ A * x * (2 ^ j - 3 ^ A) <= d * 2 ^ j * (3 ^ A - 2 ^ A)`.

Every orbit segment that has not dropped below its start reduces to this single
inequality between the word functional on the right and the archimedean number `x` on
the left.  An infinite non-descending trajectory is exactly one satisfying it at every
`j`; there is nothing else to check. -/
theorem normal_form {d : Nat} (hd : d % 2 = 1) {j x : Nat} (hnd : x ≤ genOrbit d j x) :
    2 ^ genOddCount d j x * (2 ^ j * x) + d * (2 ^ j * 2 ^ genOddCount d j x)
      ≤ 2 ^ genOddCount d j x * (3 ^ genOddCount d j x * x)
        + d * (2 ^ j * 3 ^ genOddCount d j x) := by
  have hnd' := never_drops_affine hd hnd
  have hcap := genU_cap d j x
  have hL : 2 ^ genOddCount d j x * (2 ^ j * x)
      ≤ 2 ^ genOddCount d j x * (3 ^ genOddCount d j x * x + d * genU d j x) :=
    Nat.mul_le_mul_left _ hnd'
  have hR : d * (2 ^ genOddCount d j x * genU d j x)
      + d * (2 ^ j * 2 ^ genOddCount d j x)
      ≤ d * (2 ^ j * 3 ^ genOddCount d j x) := by
    have hh := Nat.mul_le_mul_left d hcap
    rw [Nat.mul_add] at hh
    exact hh
  have hexp : 2 ^ genOddCount d j x * (3 ^ genOddCount d j x * x + d * genU d j x)
      = 2 ^ genOddCount d j x * (3 ^ genOddCount d j x * x)
        + d * (2 ^ genOddCount d j x * genU d j x) := by
    rw [Nat.mul_add]; ac_rfl
  omega

/-- **A light prefix bounds the starting point.**  If the orbit of `x` under
`3x + 1` has not dropped below `x` by step `j`, and the prefix is light by a full
bit, then `x` is bounded by a pure function of the odd count.

Consumes assets (c) and (d): the statement is `d = 1`. -/
theorem light_bounds_start {j x : Nat} (hnd : x ≤ genOrbit 1 j x)
    (hlight : 2 * 3 ^ genOddCount 1 j x ≤ 2 ^ j) :
    2 ^ genOddCount 1 j x * x + 2 * 2 ^ genOddCount 1 j x
      ≤ 2 * 3 ^ genOddCount 1 j x := by
  have hnf := normal_form (d := 1) (by decide) hnd
  rw [Nat.one_mul, Nat.one_mul] at hnf
  have hWpos : 0 < 2 ^ j := Nat.two_pow_pos j
  -- lightness, multiplied up: `2 * (P * (Q * x)) ≤ P * (W * x)`
  have hk1 : 2 * 3 ^ genOddCount 1 j x * x ≤ 2 ^ j * x :=
    Nat.mul_le_mul_right x hlight
  have hk2 : 2 ^ genOddCount 1 j x * (2 * 3 ^ genOddCount 1 j x * x)
      ≤ 2 ^ genOddCount 1 j x * (2 ^ j * x) :=
    Nat.mul_le_mul_left _ hk1
  have he : 2 ^ genOddCount 1 j x * (2 * 3 ^ genOddCount 1 j x * x)
      = 2 * (2 ^ genOddCount 1 j x * (3 ^ genOddCount 1 j x * x)) := by ac_rfl
  rw [he] at hk2
  -- assemble, then cancel the common factor `2 ^ j`
  have hmain : 2 ^ j * (2 ^ genOddCount 1 j x * x + 2 * 2 ^ genOddCount 1 j x)
      ≤ 2 ^ j * (2 * 3 ^ genOddCount 1 j x) := by
    have e1 : 2 ^ j * (2 ^ genOddCount 1 j x * x + 2 * 2 ^ genOddCount 1 j x)
        = 2 ^ genOddCount 1 j x * (2 ^ j * x)
          + 2 * (2 ^ j * 2 ^ genOddCount 1 j x) := by
      rw [Nat.mul_add]
      have ea : 2 ^ j * (2 ^ genOddCount 1 j x * x)
          = 2 ^ genOddCount 1 j x * (2 ^ j * x) := by ac_rfl
      have eb : 2 ^ j * (2 * 2 ^ genOddCount 1 j x)
          = 2 * (2 ^ j * 2 ^ genOddCount 1 j x) := by ac_rfl
      rw [ea, eb]
    have e2 : 2 ^ j * (2 * 3 ^ genOddCount 1 j x)
        = 2 * (2 ^ j * 3 ^ genOddCount 1 j x) := by ac_rfl
    rw [e1, e2]
    omega
  exact Nat.le_of_mul_le_mul_left hmain hWpos

/-- **`Structure.MinimalHeavy.no_light_scale`, recovered from the normal form.**

Under that theorem's extra hypothesis `2 ^ j ≤ x` the conclusion is not a bound on
the odd count but an outright contradiction — so `light_bounds_start` really does
extend it, keeping a (weaker) conclusion outside its range.  Note the hypothesis here
is only non-descent at `j`, not minimality. -/
theorem no_light_scale_generalised {j x : Nat} (hnd : x ≤ genOrbit 1 j x)
    (hsmall : 2 ^ j ≤ x) (hlight : 2 * 3 ^ genOddCount 1 j x ≤ 2 ^ j) : False := by
  have hb := light_bounds_start hnd hlight
  have hpos : 0 < 2 ^ genOddCount 1 j x := Nat.two_pow_pos _
  have hge : x ≤ 2 ^ genOddCount 1 j x * x := Nat.le_mul_of_pos_left x hpos
  omega

/-- Monotonicity helper: `3 ^ k * 2 ^ m ≤ 3 ^ m * 2 ^ k` for `k ≤ m`. -/
theorem pow_cross_le {k m : Nat} (h : k ≤ m) : 3 ^ k * 2 ^ m ≤ 3 ^ m * 2 ^ k := by
  obtain ⟨t, ht⟩ : ∃ t, m = k + t := ⟨m - k, by omega⟩
  subst ht
  have h23 : (2 : Nat) ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by decide) t
  calc 3 ^ k * 2 ^ (k + t) = 3 ^ k * 2 ^ k * 2 ^ t := by
        rw [Nat.pow_add, Nat.mul_assoc]
    _ ≤ 3 ^ k * 2 ^ k * 3 ^ t := Nat.mul_le_mul_left _ h23
    _ = 3 ^ (k + t) * 2 ^ k := by rw [Nat.pow_add]; ac_rfl

/-- **The verified range forbids a light prefix before `A = 33`.**

If the orbit of `x` under `3x + 1` never drops below `x` up to step `j`, `x` is above
the verified range `1086464`, and the prefix is a full bit light, then the odd count
is at least `33` — hence `j ≥ 54`.

Consumes assets (a), (c), (d).  Strictly generalises
`Structure.MinimalHeavy.no_light_scale`, which additionally requires `2 ^ j ≤ x`. -/
theorem light_forces_thirty_three {j x : Nat} (hnd : x ≤ genOrbit 1 j x)
    (hx : 1086464 ≤ x) (hlight : 2 * 3 ^ genOddCount 1 j x ≤ 2 ^ j) :
    33 ≤ genOddCount 1 j x := by
  refine Nat.le_of_not_lt (fun hlt => ?_)
  have hA : genOddCount 1 j x ≤ 32 := by omega
  have hbound := light_bounds_start hnd hlight
  -- from the numeric fact `2 * 3 ^ 32 ≤ 1086464 * 2 ^ 32` and monotonicity
  have hcross := pow_cross_le hA
  have hnum : 2 * 3 ^ 32 ≤ 1086464 * 2 ^ 32 := by decide
  have h32pos : 0 < 2 ^ 32 := Nat.two_pow_pos 32
  have hstep : 2 * 3 ^ genOddCount 1 j x * 2 ^ 32
      ≤ 1086464 * 2 ^ genOddCount 1 j x * 2 ^ 32 := by
    calc 2 * 3 ^ genOddCount 1 j x * 2 ^ 32
        = 2 * (3 ^ genOddCount 1 j x * 2 ^ 32) := Nat.mul_assoc _ _ _
      _ ≤ 2 * (3 ^ 32 * 2 ^ genOddCount 1 j x) :=
          Nat.mul_le_mul_left 2 hcross
      _ = 2 * 3 ^ 32 * 2 ^ genOddCount 1 j x := by ac_rfl
      _ ≤ 1086464 * 2 ^ 32 * 2 ^ genOddCount 1 j x :=
          Nat.mul_le_mul_right _ hnum
      _ = 1086464 * 2 ^ genOddCount 1 j x * 2 ^ 32 := by ac_rfl
  have hsmall : 2 * 3 ^ genOddCount 1 j x ≤ 1086464 * 2 ^ genOddCount 1 j x := by
    have := Nat.le_of_mul_le_mul_right hstep h32pos
    exact this
  have hbig : 1086464 * 2 ^ genOddCount 1 j x ≤ 2 ^ genOddCount 1 j x * x := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hx
  have hpos : 0 < 2 ^ genOddCount 1 j x := Nat.two_pow_pos _
  omega

/-! ## Axiom audit -/

#print axioms trop_sandwich
#print axioms trop_error_is_min
#print axioms trop_within_one_bit_iff
#print axioms trop_scaling
#print axioms word_determines
#print axioms coupling_determined_by_scale
#print axioms coupling_d_blind
#print axioms genU_cap
#print axioms normal_form
#print axioms light_bounds_start
#print axioms no_light_scale_generalised
#print axioms light_forces_thirty_three

end TropicalDefect
end Collatz
