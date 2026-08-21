import Collatz.Strategy.AccumulatorClass
import Collatz.Strategy.CycleCriterion

/-!
# The high part: what the parity word does *not* determine

By Terras a parity word of length `L` is exactly one residue class modulo
`2 ^ L`, so writing `x = r + 2 ^ L · m` with `r = x % 2 ^ L` the word pins `r`
outright and leaves only `m` — the **high part** — free.  Every "state
dependent" statement about an orbit, as opposed to about its word, must
therefore be a statement about `m`.

This file works out exactly what `m` does, and the answer is deflationary.

## The law

`Congruence.accOrbit_pow_two_mul_add` — already in the repository — says

`T^L(2 ^ L · m + r) = 3 ^ a(r,L) · m + T^L(r)`.

Restated on the high part itself (`orbit_high`):

`T^L(x) = 3 ^ a · (x / 2 ^ L) + T^L(x % 2 ^ L)`,   `a = a(x,L)`.

The offset is exactly the Terras quotient (`offset_exact`, `two_pow_dvd_offset`):

`2 ^ L · T^L(r) = 3 ^ a · r + C_L(x)`,  i.e.  `T^L(r) = (3 ^ a · r + C) / 2 ^ L`,

so the "new" state-dependent recursion `m ↦ 3 ^ a · m + r'` has `r' = T^L(r)`:
its offset is the orbit of the *smallest* member of the class.  Nothing in it
is new information — the multiplier is the word's `3 ^ a` and the offset is the
word's own orbit.

## It is exactly self-similar

`renorm_compose`: the law at window `j + k` is the law at window `j` composed
with the law at window `k`, with multiplier `3 ^ (a_j + a_k)`.  The high part
of `x` at scale `2 ^ (j+k)` obeys the same affine law with the same shape.
Renormalising — splitting off `2 ^ L` and keeping `m` — returns a problem with
the *same* triple `(2 ^ L, 3 ^ a, C)`; `renorm_faithful` records that the
splitting is a bijection, so the renormalisation neither loses nor gains
information.  This is why every word-level attack reappears verbatim at every
scale.

## At a cycle the high part is zero

`cycle_high` turns `T^L(n) = n` into `(2 ^ L − 3 ^ a) · m = T^L(r) − r`, which
is the cycle equation `(2 ^ L − 3 ^ a) · n = C` renormalised by
`n ↦ m`, `C ↦ (C − G·r) / 2 ^ L`.  It is the same equation, not a new one.
And `cycle_high_vacuous`: as soon as `n < 2 ^ L` the high part is `0` and the
renormalised equation degenerates to `0 = 0`.  Measured: every element of a
hypothetical cycle at `(L,a)` is at most `2 ^ (L−a) · (3 ^ a − 2 ^ a) / G`,
which is below `2 ^ L` for every `a ≤ 20000` except `a = 1`, with a margin of
about `a` bits (at the frontier `(6809, 4296)`: elements `< 2 ^ 2524` against a
scale of `2 ^ 6809`, a margin of 4285 bits).  So the high part carries *no*
information about a cycle: it is identically `0`.

## No descent on it either

`high_part_expands`: `m ↦ 3 ^ a · m + r'` strictly increases every positive `m`
once `a > 0`, and `high_part_fix_forces_zero`: its only fixed point is `0`.
Quantitatively `offset_lt` gives `r' < 2 · 3 ^ a`, hence `growth_ratio`:

`3 ^ a · m ≤ T^L(x) < 3 ^ a · (m + 2)`,

so up to an additive error of `2` the high part is multiplied by `3 ^ a` while
the scale is multiplied by `2 ^ L`.  The comparison of growth rates is exactly
`3 ^ a` against `2 ^ L` — the gap, already the object of study — with no
remainder term of its own.
-/

namespace Collatz
namespace HighPart

open Reach Congruence AffineExact AccumulatorClass

/-! ## The splitting -/

/-- The low part of `x` at scale `L`: the residue the parity word determines. -/
def lowPart (L x : Nat) : Nat := x % 2 ^ L

/-- The high part of `x` at scale `L`: everything the parity word does *not*
determine. -/
def highPart (L x : Nat) : Nat := x / 2 ^ L

/-- The splitting is exact. -/
theorem split (L x : Nat) : 2 ^ L * highPart L x + lowPart L x = x := by
  have := Nat.div_add_mod x (2 ^ L)
  simp [highPart, lowPart]
  omega

/-- The low part is below the scale. -/
theorem lowPart_lt (L x : Nat) : lowPart L x < 2 ^ L :=
  Nat.mod_lt _ (Arith.two_pow_pos L)

/-- **The renormalisation is faithful.**  Splitting into high and low parts
loses nothing and gains nothing: it is inverted by reassembly.  Consequently a
statement about the pair `(low, high)` is a statement about `x`, which is why
passing to the high part cannot introduce information the original problem did
not already contain. -/
theorem renorm_faithful {L x y : Nat}
    (hlow : lowPart L x = lowPart L y) (hhigh : highPart L x = highPart L y) :
    x = y := by
  have hx := split L x
  have hy := split L y
  rw [hlow, hhigh] at hx
  omega

/-! ## The affine law on the high part -/

/-- The word is a function of the low part. -/
theorem oddCount_lowPart (L x : Nat) : oddCount (lowPart L x) L = oddCount x L := by
  exact oddCount_congr_of_mod (x := lowPart L x) (y := x) (j := L)
    (by simp [lowPart])

/-- The accumulator is a function of the low part. -/
theorem affineC_lowPart (L x : Nat) : affineC L (lowPart L x) = affineC L x := by
  exact affineC_congr_of_mod
    (by simp [lowPart])

/-- **The high-part law.**  `T^L(x) = 3 ^ a · m + T^L(r)`: on each residue class
the `L`-step map is affine in the high part, with multiplier `3 ^ a` and offset
the orbit of the class representative. -/
theorem orbit_high (L x : Nat) :
    acceleratedOrbit L x
      = 3 ^ oddCount x L * highPart L x + acceleratedOrbit L (lowPart L x) := by
  have h := accOrbit_pow_two_mul_add L (highPart L x) (lowPart L x)
  rw [split] at h
  rw [h, oddCount_lowPart]

/-- **The offset is the Terras quotient.**  `2 ^ L · r' = 3 ^ a · r + C`, so
`r' = (3 ^ a · r + C) / 2 ^ L` exactly, with `C` the accumulator of the word. -/
theorem offset_exact (L x : Nat) :
    2 ^ L * acceleratedOrbit L (lowPart L x)
      = 3 ^ oddCount x L * lowPart L x + affineC L x := by
  have h := affine_exact (lowPart L x) L
  rw [oddCount_lowPart, affineC_lowPart] at h
  exact h

/-- The divisibility the quotient needs: `2 ^ L ∣ 3 ^ a · r + C`. -/
theorem two_pow_dvd_offset (L x : Nat) :
    2 ^ L ∣ 3 ^ oddCount x L * lowPart L x + affineC L x :=
  ⟨acceleratedOrbit L (lowPart L x), (offset_exact L x).symm⟩

/-- The offset written as the quotient itself. -/
theorem offset_eq_div (L x : Nat) :
    acceleratedOrbit L (lowPart L x)
      = (3 ^ oddCount x L * lowPart L x + affineC L x) / 2 ^ L := by
  rw [← offset_exact L x, Nat.mul_div_cancel_left _ (Arith.two_pow_pos L)]

/-! ## Self-similarity -/

/-- **The law composes.**  Two consecutive windows give the law at the combined
window with the multipliers multiplied — the same statement one scale up, with
no new parameter.  This is the precise sense in which the high-part recursion
is self-similar. -/
theorem renorm_compose (j k x : Nat) :
    acceleratedOrbit (j + k) x
      = 3 ^ (oddCount x j + oddCount (acceleratedOrbit j x) k) * highPart (j + k) x
        + acceleratedOrbit (j + k) (lowPart (j + k) x) := by
  rw [orbit_high, AccumulatorArith.oddCount_add x j k]

/-- The multiplier of the composite window is the product of the multipliers. -/
theorem multiplier_mul (j k x : Nat) :
    3 ^ oddCount x (j + k)
      = 3 ^ oddCount x j * 3 ^ oddCount (acceleratedOrbit j x) k := by
  rw [AccumulatorArith.oddCount_add x j k, Nat.pow_add]

/-- **The 3-adic dual of Terras.**  The word determines `T^L(x)` modulo `3 ^ a`:
two starting points with the same low part have `L`-step images differing by a
multiple of `3 ^ a`. -/
theorem orbit_mod_three_pow (L x : Nat) :
    ∃ k : Nat, acceleratedOrbit L x = acceleratedOrbit L (lowPart L x)
      + 3 ^ oddCount x L * k :=
  ⟨highPart L x, by rw [orbit_high]; omega⟩

/-! ## Size of the offset, and the growth comparison -/

/-- The accumulator is below `2 ^ j · 3 ^ a`. -/
theorem affineC_lt (x : Nat) : ∀ j : Nat, affineC j x < 2 ^ j * 3 ^ oddCount x j := by
  have hAC : ∀ p q : Nat, (2 * p) * (3 * q) = 6 * (p * q) := by
    intro p q
    calc (2 * p) * (3 * q) = 2 * (p * (3 * q)) := by rw [Nat.mul_assoc]
      _ = 2 * ((p * 3) * q) := by rw [Nat.mul_assoc]
      _ = 2 * ((3 * p) * q) := by rw [Nat.mul_comm p 3]
      _ = 2 * (3 * (p * q)) := by rw [Nat.mul_assoc]
      _ = 6 * (p * q) := by rw [← Nat.mul_assoc]
  intro j
  induction j with
  | zero => simp [affineC]
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    have h2 : 0 < 2 ^ j := Arith.two_pow_pos j
    have h3 : 0 < 3 ^ oddCount x j := Arith.three_pow_pos _
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hcount : oddCount x (j + 1) = oddCount x j := by omega
      have hmul : 2 ^ j * 3 ^ oddCount x j ≤ 2 ^ (j + 1) * 3 ^ oddCount x j := by
        rw [Arith.two_pow_succ]
        exact Nat.mul_le_mul_right _ (by omega)
      rw [affineC_even he, hcount]
      omega
    · have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      have hbig : 2 ^ (j + 1) * 3 ^ (oddCount x j + 1)
          = 6 * (2 ^ j * 3 ^ oddCount x j) := by
        rw [Arith.two_pow_succ, Arith.three_pow_succ]
        exact hAC (2 ^ j) (3 ^ oddCount x j)
      have hle : 2 ^ j ≤ 2 ^ j * 3 ^ oddCount x j := Nat.le_mul_of_pos_right _ h3
      rw [affineC_odd ho, hcount, hbig]
      omega

/-- **The offset is smaller than twice the multiplier.**  `r' < 2 · 3 ^ a`. -/
theorem offset_lt (L x : Nat) :
    acceleratedOrbit L (lowPart L x) < 2 * 3 ^ oddCount x L := by
  have hexact := offset_exact L x
  have hC := affineC_lt x L
  have hr := lowPart_lt L x
  have h3 : 0 < 3 ^ oddCount x L := Arith.three_pow_pos _
  have hstep : 3 ^ oddCount x L * (lowPart L x + 1) ≤ 3 ^ oddCount x L * 2 ^ L :=
    Nat.mul_le_mul_left _ (by omega)
  have hexpand : 3 ^ oddCount x L * (lowPart L x + 1)
      = 3 ^ oddCount x L * lowPart L x + 3 ^ oddCount x L := by
    rw [Nat.mul_add, Nat.mul_one]
  have hcomm : 3 ^ oddCount x L * 2 ^ L = 2 ^ L * 3 ^ oddCount x L := Nat.mul_comm _ _
  have hkey : 2 ^ L * (2 * 3 ^ oddCount x L) = 2 * (2 ^ L * 3 ^ oddCount x L) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ L) 2]
  have hgoal : 2 ^ L * acceleratedOrbit L (lowPart L x)
      < 2 ^ L * (2 * 3 ^ oddCount x L) := by omega
  exact Nat.lt_of_mul_lt_mul_left hgoal

/-- **The growth comparison, exactly.**  The `L`-step image is the high part
multiplied by `3 ^ a`, with an additive error below `2 · 3 ^ a`.  The high part
therefore expands by exactly `3 ^ a` while the scale expands by `2 ^ L`: the
comparison of rates is `3 ^ a` against `2 ^ L`, the gap, and nothing else. -/
theorem growth_ratio (L x : Nat) :
    3 ^ oddCount x L * highPart L x ≤ acceleratedOrbit L x ∧
      acceleratedOrbit L x < 3 ^ oddCount x L * (highPart L x + 2) := by
  have h := orbit_high L x
  have ho := offset_lt L x
  constructor
  · omega
  · rw [Nat.mul_add]
    omega

/-! ## The high part at a cycle -/

/-- **The renormalised cycle equation.**  `T^L(n) = n` becomes
`3 ^ a · m + T^L(r) = 2 ^ L · m + r`, i.e. `(2 ^ L − 3 ^ a) · m = T^L(r) − r`
in `Nat`-safe additive form. -/
theorem cycle_high {L n : Nat} (h : acceleratedOrbit L n = n) :
    3 ^ oddCount n L * highPart L n + acceleratedOrbit L (lowPart L n)
      = 2 ^ L * highPart L n + lowPart L n := by
  have hs := split L n
  have ho := orbit_high L n
  omega

/-- **And it is vacuous below the scale.**  If `n < 2 ^ L` — which every element
of a cycle satisfies once `G · 2 ^ a > 3 ^ a`, hence at every cycle-plausible
pair with `a ≥ 2` — the high part is `0` and the renormalised cycle equation
degenerates to `T^L(n) = n`, carrying no information at all. -/
theorem cycle_high_vacuous {L n : Nat} (hn : n < 2 ^ L) :
    highPart L n = 0 ∧ lowPart L n = n := by
  constructor
  · exact Nat.div_eq_of_lt hn
  · exact Nat.mod_eq_of_lt hn

/-- Below the scale the renormalised equation says exactly `T^L(n) = n` again. -/
theorem cycle_high_below_scale {L n : Nat} (hn : n < 2 ^ L) :
    (3 ^ oddCount n L * highPart L n + acceleratedOrbit L (lowPart L n)
        = 2 ^ L * highPart L n + lowPart L n)
      ↔ acceleratedOrbit L n = n := by
  obtain ⟨hh, hl⟩ := cycle_high_vacuous (L := L) (n := n) hn
  rw [hh, hl]
  constructor <;> intro h <;> omega

/-- **The high part of a cycle vanishes, from a bound on the accumulator alone.**
If the accumulator of the cycle word is below `2 ^ L · G` — the measured
situation at every cycle-plausible pair with `a ≥ 2` — then the cycle lies
strictly below the scale, so its high part is `0` and the renormalised equation
of `cycle_high` says nothing. -/
theorem cycle_high_zero_of_accumulator {L x : Nat} (hx : 0 < x) (hL : 0 < L)
    (hgap : 3 ^ oddCount x L < 2 ^ L)
    (hcyc : acceleratedOrbit L x = x)
    (hC : affineC L x < 2 ^ L * (2 ^ L - 3 ^ oddCount x L)) :
    highPart L x = 0 ∧ lowPart L x = x := by
  have heq : (2 ^ L - 3 ^ oddCount x L) * x = affineC L x :=
    (CycleCriterion.cycle_iff_gap_mul hx hL hgap).mp hcyc
  have hGpos : 0 < 2 ^ L - 3 ^ oddCount x L := by omega
  have hcomm : 2 ^ L * (2 ^ L - 3 ^ oddCount x L)
      = (2 ^ L - 3 ^ oddCount x L) * 2 ^ L := Nat.mul_comm _ _
  have hlt : (2 ^ L - 3 ^ oddCount x L) * x < (2 ^ L - 3 ^ oddCount x L) * 2 ^ L := by
    omega
  exact cycle_high_vacuous (Nat.lt_of_mul_lt_mul_left hlt)

/-! ## No descent on the high part -/

/-- The high-part map is expanding: a positive high part strictly increases. -/
theorem high_part_expands {a m r : Nat} (ha : 0 < a) (hm : 0 < m) :
    m < 3 ^ a * m + r := by
  have h3 : 3 ≤ 3 ^ a := by
    have : (3:Nat) ^ 1 ≤ 3 ^ a := Arith.three_pow_le_three_pow ha
    simpa using this
  have : 3 * m ≤ 3 ^ a * m := Nat.mul_le_mul_right _ h3
  omega

/-- Its only fixed point is `0`, so no orbit of the high part can recur at a
positive value with the same window data. -/
theorem high_part_fix_forces_zero {a m r : Nat} (ha : 0 < a)
    (h : 3 ^ a * m + r = m) : m = 0 ∧ r = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp at h; omega
  · exact absurd h (by have := high_part_expands (a := a) (m := m) (r := r) ha hm; omega)

/-- **The high part is below the orbit value.**  `highPart L x < T^L(x)` when the
window has an odd step and the high part is positive.

*Corrected:* an earlier docstring here said this shows the high part "strictly
increases", and used it to conclude that no descent on the high part exists.  Both
are wrong.  The theorem compares a *high part* with an *orbit value* — incommensurable
objects — and the quantity a descent argument would rank, `highPart L (T^L x)` against
`highPart L x`, actually **decreases** in the cycle-plausible regime, since
`highPart L (T^L x) = ⌊(3^a m + r')/2^L⌋ < m` whenever `3^a < 2^L`.  Counterexample to
the old claim: `x = 13`, `L = 2` gives `highPart = 3` and `highPart (T² 13) = highPart 10
= 2`.

The branch is still uninteresting, but for a different reason: at a cycle the high part
is identically `0` by `cycle_high_zero_of_accumulator`, so there is nothing to descend
on. -/
theorem no_descent_on_high_part {L x : Nat} (ha : 0 < oddCount x L)
    (hm : 0 < highPart L x) : highPart L x < acceleratedOrbit L x := by
  have h := orbit_high L x
  have := high_part_expands (a := oddCount x L) (m := highPart L x)
    (r := acceleratedOrbit L (lowPart L x)) ha hm
  omega

end HighPart
end Collatz
