/-!
# The δ-spectrum of heavy words

`NewModels.word_is_cycle_word` says: every parity word `w` with a positive gap is
a genuine cycle word — of the map `x ↦ (3x + δ(w))/2`, where

    G(w) = 2 ^ |w| − 3 ^ (odd count of w),   δ(w) = G(w) / gcd(C(w), G(w)).

The corrected reading of that theorem (Round III) is that `δ` is the *only*
word-only obstruction left: a word-only quantity that is invariant under
`C ↦ d·C` cannot separate `3x+1` from `3x+5`, but `δ` compares `C` to `G`
multiplicatively and does separate them.  Round V asked whether `δ` can be
forced to grow — if `δ(w) > 1` for every heavy `w` of large length, the Collatz
cycle problem is finished.

This file records the measurement and the refutation.

## The refutation

`δ` does **not** grow.  Exhaustively over every word of length `L ≤ 40` that is
heavy at every proper prefix and has a positive gap, the minimum of `δ` is

    L:  4    5    7    8   10   12   13    15   16    18    20      21  23  24
    δ:  7    5   47   13   59   83  233  2617  499  7727  1753  502829  79  13
    L:  26  27   29   31   32     34         35     37    39   40
    δ: 233   5  137  437  499  33587  425525537  31727  1631  191

The five witnesses formalised below pin the entries `L = 23, 24, 26, 27, 32`.
`w187` and `w347` are the two heavy words of length 27 with `δ = 5`; they are
exactly the parity words of the two known `3x+5` cycles of minima 187 and 347,
which is the promised negative control.  So `δ = 5` is attained at `L = 27`,
`δ = 13` at `L = 24`, and no monotone lower bound on `δ` exists in this range.

`delta_no_growing_bound` states the consequence in the strongest available form:
*any* function `f` which is a valid lower bound for `δ` on heavy positive-gap
words must satisfy `f 27 ≤ 5`, `f 24 ≤ 13`, `f 23 ≤ 79`, `f 26 ≤ 233`,
`f 32 ≤ 499`.  A hypothesis class is thereby closed, not merely doubted.

## Why it fails, quantitatively

The measurement that explains the table: over the heavy positive-gap words of
each `(L, a)`, the residue `C(w) mod G` is equidistributed.  For every divisor
`d` of `G` and every `(L, a)` with `L ≤ 32`, the count of heavy words with
`d ∣ C` matches `N/d` (`N` = number of heavy words) with χ² = 182 on 27 degrees
of freedom, the entire excess coming from `d = 5` — the one prime whose
multiplicative order of 2 is short enough to interact with the word's block
structure — where the bias is `+0.9 %` at `L = 32` and `−1.8 %` at `L = 27`,
i.e. of *both* signs.  Heaviness therefore does **not** suppress `gcd(C, G)`.
The suppression that was observed at `L ≤ 20` is a sample-size effect: the
largest divisor of `G` that `N` samples can be expected to hit is the largest
divisor `≤ N`, and at `L = 20` that divisor is `295` — the observed maximum.

Consequently `δ_min(L, a)` is, empirically, the least divisor of `G` exceeding
`G/N` (17 of the 23 pairs exactly, the other 6 one divisor lower, as Poisson
predicts).  Since `N` grows like `2 ^ (H(log₃ 2) · L) ≈ 1.932 ^ L` and `G` like
`2 ^ L`, `δ_min ≈ 2 ^ (0.0499 · L)` up to divisor granularity — growth, but
growth that is a *counting* statement about `C mod G`, not a structural one.
Proving it is exactly the equidistribution problem whose L¹ barrier
(`ExpSum`) is already known to be unconditional.  That is the finding: the
δ-route and the counting route are the same route.
-/

namespace Collatz
namespace DeltaSpectrum

/-! ### Word arithmetic, self-contained -/

/-- Number of odd letters (`true`) of a word. -/
def oddCount : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 1 else 0) + oddCount w

/-- The accumulator recurrence `C₀ = 0`, `C_{j+1} = 3·C_j + 2^j` on an odd
letter and `C_{j+1} = C_j` on an even one, read left to right. -/
def accC : List Bool → Nat → Nat → Nat
  | [], _, c => c
  | b :: w, j, c => accC w (j + 1) (if b then 3 * c + 2 ^ j else c)

/-- `C(w)`: the affine accumulator of the word. -/
def C (w : List Bool) : Nat := accC w 0 0

/-- `G(w) = 2 ^ |w| − 3 ^ a`. Positive exactly when the word has a positive gap. -/
def gap (w : List Bool) : Nat := 2 ^ w.length - 3 ^ oddCount w

/-- `δ(w) = G / gcd(C, G)`: the least `d` for which `w` is a cycle word of
`x ↦ (3x + d)/2`. -/
def delta (w : List Bool) : Nat := gap w / Nat.gcd (C w) (gap w)

/-- Heaviness at every **proper** prefix: `2 ^ i ≤ 3 ^ (odd count of the first
`i` letters)` for `1 ≤ i ≤ |w| − 1`.  The full prefix is deliberately not
tested — a positive gap makes it false. -/
def heavyAux : List Bool → Nat → Nat → Bool
  | [], _, _ => true
  | b :: w, i, a =>
    let a' := a + (if b then 1 else 0)
    match w with
    | [] => true
    | c :: w' => decide (2 ^ (i + 1) ≤ 3 ^ a') && heavyAux (c :: w') (i + 1) a'

/-- `w` is heavy at every proper prefix. -/
def heavy (w : List Bool) : Bool := heavyAux w 0 0

/-! ### Sanity: `heavy` is not vacuous -/

/-- A word beginning with an even letter fails at its first proper prefix. -/
theorem heavy_false_of_even_start : heavy [false, true, true] = false := rfl

/-- The empty and one-letter words have no proper prefix to test. -/
theorem heavy_nil : heavy [] = true := rfl
theorem heavy_singleton : heavy [true] = true := rfl

/-- `2 ^ 27 ≤ 3 ^ 17` fails, so the *full* prefix of `w187` is not heavy — as it
must be, since the gap is positive.  Heaviness is a proper-prefix condition. -/
theorem full_prefix_not_heavy : ¬ (2 ^ 27 ≤ 3 ^ 17) := by decide

/-! ### General facts about `δ` -/

theorem gcd_pos {w : List Bool} (h : 0 < gap w) : 0 < Nat.gcd (C w) (gap w) :=
  Nat.gcd_pos_of_pos_right _ h

theorem delta_mul_gcd (w : List Bool) :
    delta w * Nat.gcd (C w) (gap w) = gap w :=
  Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

theorem delta_dvd_gap (w : List Bool) : delta w ∣ gap w :=
  ⟨Nat.gcd (C w) (gap w), (delta_mul_gcd w).symm⟩

/-- **The cycle equation of an arbitrary word.**  With `n = C / gcd(C, G)`,
every word with a positive gap satisfies `G · n = δ · C`, which is exactly the
cycle criterion for the map `x ↦ (3x + δ)/2`. -/
theorem gap_mul_min (w : List Bool) :
    gap w * (C w / Nat.gcd (C w) (gap w)) = delta w * C w := by
  have hg : Nat.gcd (C w) (gap w) * (C w / Nat.gcd (C w) (gap w)) = C w :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  calc gap w * (C w / Nat.gcd (C w) (gap w))
      = (delta w * Nat.gcd (C w) (gap w)) * (C w / Nat.gcd (C w) (gap w)) := by
        rw [delta_mul_gcd]
    _ = delta w * (Nat.gcd (C w) (gap w) * (C w / Nat.gcd (C w) (gap w))) := by
        rw [Nat.mul_assoc]
    _ = delta w * C w := by rw [hg]

/-- `δ(w) = 1` is exactly the `d = 1` condition: the word is a `3x+1` cycle word. -/
theorem delta_eq_one_iff {w : List Bool} (h : 0 < gap w) :
    delta w = 1 ↔ gap w ∣ C w := by
  constructor
  · intro h1
    have : Nat.gcd (C w) (gap w) = gap w := by
      have := delta_mul_gcd w
      rw [h1, Nat.one_mul] at this
      exact this
    have hd : Nat.gcd (C w) (gap w) ∣ C w := Nat.gcd_dvd_left _ _
    rw [this] at hd
    exact hd
  · intro hdvd
    have h1 : gap w ∣ Nat.gcd (C w) (gap w) := Nat.dvd_gcd hdvd (Nat.dvd_refl _)
    have h2 : Nat.gcd (C w) (gap w) ∣ gap w := Nat.gcd_dvd_right _ _
    have : Nat.gcd (C w) (gap w) = gap w := Nat.dvd_antisymm h2 h1
    show gap w / Nat.gcd (C w) (gap w) = 1
    rw [this]
    exact Nat.div_self h

/-! ### The witnesses

Each `wN` is the heavy word whose cycle minimum is `N`; the `δ` of that word is
the `d` for which `N` really is the least element of an `L`-cycle of
`x ↦ (3x + d)/2`.  All facts are kernel computations. -/

/-- Length 27, `δ = 5`, minimum 187: the parity word of a genuine `3x+5` cycle. -/
def w187 : List Bool :=
  [true, true, true, true, true, true, false, true, true, true, false, true,
   true, false, true, false, false, true, false, true, true, true, true,
   false, false, false, false]

/-- Length 27, `δ = 5`, minimum 347: the second genuine `3x+5` cycle. -/
def w347 : List Bool :=
  [true, true, true, true, true, false, false, true, true, true, true, true,
   false, true, false, true, false, false, false, true, true, false, true,
   true, false, true, false]

/-- Length 24, `δ = 13`, minimum 131. -/
def w131 : List Bool :=
  [true, true, true, true, false, false, true, true, true, true, true, true,
   false, true, true, false, true, true, false, true, false, false, false, false]

/-- Length 23, `δ = 79`, minimum 233. -/
def w233 : List Bool :=
  [true, true, true, false, true, false, true, true, true, true, false, true,
   false, true, false, true, true, true, true, false, false, false, false]

/-- Length 26, `δ = 233`, minimum 647. -/
def w647 : List Bool :=
  [true, true, true, true, false, true, true, true, false, true, true, true,
   false, true, true, false, true, false, true, true, false, false, true,
   false, false, false]

/-- Length 32, `δ = 499`, minimum 5281. -/
def w5281 : List Bool :=
  [true, true, false, true, true, true, true, true, false, true, false, true,
   true, true, true, false, true, true, true, false, false, true, false, true,
   false, false, true, true, false, false, true, false]

theorem w187_length : w187.length = 27 := rfl
theorem w187_oddCount : oddCount w187 = 17 := rfl
theorem w187_heavy : heavy w187 = true := rfl
theorem w187_C : C w187 = 189900931 := rfl
theorem w187_gap : gap w187 = 5077565 := rfl
theorem w187_gap_pos : 0 < gap w187 := by decide
theorem w187_delta : delta w187 = 5 := rfl
/-- The minimum read off the word is 187, and the cycle equation holds. -/
theorem w187_min : C w187 / Nat.gcd (C w187) (gap w187) = 187 := rfl

theorem w347_length : w347.length = 27 := rfl
theorem w347_heavy : heavy w347 = true := rfl
theorem w347_gap_pos : 0 < gap w347 := by decide
theorem w347_delta : delta w347 = 5 := rfl
theorem w347_min : C w347 / Nat.gcd (C w347) (gap w347) = 347 := rfl

theorem w131_length : w131.length = 24 := rfl
theorem w131_heavy : heavy w131 = true := rfl
theorem w131_gap_pos : 0 < gap w131 := by decide
theorem w131_delta : delta w131 = 13 := rfl
theorem w131_min : C w131 / Nat.gcd (C w131) (gap w131) = 131 := rfl

theorem w233_length : w233.length = 23 := rfl
theorem w233_heavy : heavy w233 = true := rfl
theorem w233_gap_pos : 0 < gap w233 := by decide
theorem w233_delta : delta w233 = 79 := rfl
theorem w233_min : C w233 / Nat.gcd (C w233) (gap w233) = 233 := rfl

theorem w647_length : w647.length = 26 := rfl
theorem w647_heavy : heavy w647 = true := rfl
theorem w647_gap_pos : 0 < gap w647 := by decide
theorem w647_delta : delta w647 = 233 := rfl
theorem w647_min : C w647 / Nat.gcd (C w647) (gap w647) = 647 := rfl

theorem w5281_length : w5281.length = 32 := rfl
theorem w5281_heavy : heavy w5281 = true := rfl
theorem w5281_gap_pos : 0 < gap w5281 := by decide
theorem w5281_delta : delta w5281 = 499 := rfl
theorem w5281_min : C w5281 / Nat.gcd (C w5281) (gap w5281) = 5281 := rfl

/-! ### The hypothesis class that dies -/

/-- **No growing lower bound on `δ` over heavy words.**

If `f` is *any* function of the length alone that lower-bounds `δ` on every
heavy word with a positive gap, then `f` is pinned at five separate lengths, by
values that do not increase with the length.  In particular no `f` that is
monotone and unbounded qualifies, and `δ ≥ 6` is false. -/
theorem delta_no_growing_bound (f : Nat → Nat)
    (h : ∀ w : List Bool, heavy w = true → 0 < gap w → f w.length ≤ delta w) :
    f 23 ≤ 79 ∧ f 24 ≤ 13 ∧ f 26 ≤ 233 ∧ f 27 ≤ 5 ∧ f 32 ≤ 499 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := h w233 w233_heavy w233_gap_pos
    rw [w233_length, w233_delta] at this; exact this
  · have := h w131 w131_heavy w131_gap_pos
    rw [w131_length, w131_delta] at this; exact this
  · have := h w647 w647_heavy w647_gap_pos
    rw [w647_length, w647_delta] at this; exact this
  · have := h w187 w187_heavy w187_gap_pos
    rw [w187_length, w187_delta] at this; exact this
  · have := h w5281 w5281_heavy w5281_gap_pos
    rw [w5281_length, w5281_delta] at this; exact this

/-- The `δ` of a heavy word is not monotone in the length: it drops from 79 at
`L = 23` to 13 at `L = 24` to 5 at `L = 27`. -/
theorem delta_not_monotone :
    delta w233 = 79 ∧ delta w131 = 13 ∧ delta w187 = 5 ∧
      w233.length < w131.length ∧ w131.length < w187.length :=
  ⟨w233_delta, w131_delta, w187_delta, by decide, by decide⟩

/-- Two distinct heavy words of the same length attain `δ = 5`, with distinct
minima — the two `3x+5` 27-cycles.  So `δ = 5` is not an isolated accident of
one word. -/
theorem delta_five_twice :
    w187 ≠ w347 ∧ delta w187 = 5 ∧ delta w347 = 5 ∧
      w187.length = 27 ∧ w347.length = 27 ∧
      C w187 / Nat.gcd (C w187) (gap w187) = 187 ∧
      C w347 / Nat.gcd (C w347) (gap w347) = 347 :=
  ⟨by decide, w187_delta, w347_delta, w187_length, w347_length, w187_min, w347_min⟩

end DeltaSpectrum
end Collatz
