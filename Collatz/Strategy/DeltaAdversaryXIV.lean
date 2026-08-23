import Collatz.Strategy.DeltaSpectrum

/-!
# Round XIV adversary: what `δ` does and does not say

Three facts, all kernel computations or short inductions, aimed at the two
formulations the round is reaching for.

## 1. `δ ≥ 2` is false as stated

`wTriv = [true, false]` is heavy, has a positive gap, and has `δ = 1`.  It is the
word of the cycle `1 → 2 → 1`.  So every Round XIV statement of the shape
"`δ(w) ≥ 2` for every heavy word with a positive gap" is **false**, not merely
equivalent to the conjecture: the trivial cycle is a heavy positive-gap word and
it must be excluded by hypothesis.  `DeltaSpectrum`'s header is careful about
this ("`δ = 1` occurs only at `L = 2`"); a theorem statement must be too.

## 2. `gcd(C, G) = 1` is false, and by a wide margin

`wSix = 1111110000` (`a = 6`, `L = 10`) is heavy, `C = 665`, `G = 295 = 5·59`,
so `gcd(C, G) = 5`.  Its `δ` is `59`, so `G ∤ C` survives untouched.  Any
strengthening of the target to "`C` and `G` are coprime" dies here, at the
smallest length where it can die: exhaustively, `gcd(C,G) > 1` first occurs at
`a = 6` and then occurs for `5/12`, `1/30`, `13/85`, `23/173`, `38/476`,
`89/961`, `618/2652`, `0/8045`, `234/17637`, `3935/51033`, `15973/108950` of the
heavy positive-gap words at `a = 6,…,16`.  It is a common event, not a rare one.

## 3. Heaviness plus a positive gap pins the length: `L = ⌊a log₂ 3⌋ + 1`

`heavy_ledge` below: a heavy word of length `L ≥ 2` satisfies `2 ^ (L−1) ≤ 3 ^ a`.
With a positive gap (`3 ^ a < 2 ^ L`) this sandwiches `2 ^ L` strictly between
`3 ^ a` and `2 · 3 ^ a`, so `L` is determined by `a`.  The heavy positive-gap
words are therefore a *single* family indexed by `a`, not a two-parameter one —
which is what makes the direct search of section 60 of the round report possible:
for each `a` there is exactly one length to test, exactly one `G`, and the cycle
minimum `x = C/G` is bounded by `Bcap a / G`, a computable number.

## The search that this enables (measured, not proved here)

Because the accumulator sumset has unique representation
(`NewModels`, Model 3), the map `C ↦ (t_0 < ⋯ < t_(a−1))` is *decodable*:
`t_i = v₂(R_i)`, `R_(i+1) = R_i − 3 ^ (a−1−i) · 2 ^ (t_i)`.  So testing whether
some heavy word has `G ∣ C` costs `O(a)` per candidate value of `x = C/G`, and
`x` ranges only over `1 … ⌊Bcap a / G⌋`.  Running that for every `a` from `1` to
`9000` — i.e. every heavy positive-gap word of length `L ≤ 14265`, all of them,
not a sample — the **only** word with `δ = 1` is `wTriv`, at `a = 1`, `L = 2`,
`x = 1`.  Positive controls: the decoder recovers the genuine cycle words of
`3x+5` (`n = 187, 347`, `L = 27`), `3x+7` (`n = 5`, `L = 4`) and `3x+13`
(`n = 131`, `L = 24`), each of which lies in the box at `L = ⌊a log₂ 3⌋ + 1`,
so the search is not vacuous and would have returned a `3x+1` cycle word had one
existed in range.  The previous exhaustive range in this repo was `L ≤ 40`.
-/

namespace Collatz
namespace DeltaAdversaryXIV

open DeltaSpectrum

/-! ## 1. The trivial cycle is a heavy positive-gap word with `δ = 1` -/

/-- The parity word of `1 → 2 → 1`. -/
def wTriv : List Bool := [true, false]

theorem wTriv_heavy : heavy wTriv = true := rfl
theorem wTriv_C : C wTriv = 1 := rfl
theorem wTriv_gap : gap wTriv = 1 := rfl
theorem wTriv_gap_pos : 0 < gap wTriv := by decide
theorem wTriv_delta : delta wTriv = 1 := rfl
theorem wTriv_min : C wTriv / Nat.gcd (C wTriv) (gap wTriv) = 1 := rfl

/-- **`δ ≥ 2` on heavy positive-gap words is false.**  The trivial cycle is a
counterexample, so the target must exclude it explicitly. -/
theorem delta_ge_two_false :
    ¬ (∀ w : List Bool, heavy w = true → 0 < gap w → 2 ≤ delta w) := by
  intro h
  have := h wTriv wTriv_heavy wTriv_gap_pos
  rw [wTriv_delta] at this
  exact absurd this (by decide)

/-- Equivalently, `G ∣ C` does occur on a heavy positive-gap word. -/
theorem gap_dvd_C_not_impossible :
    ¬ (∀ w : List Bool, heavy w = true → 0 < gap w → ¬ (gap w ∣ C w)) := by
  intro h
  exact h wTriv wTriv_heavy wTriv_gap_pos (by decide)

/-! ## 2. `gcd(C, G) = 1` is false -/

/-- `1111110000`: six odd steps then four halvings, the shortest heavy word with
`gcd(C, G) > 1`. -/
def wSix : List Bool :=
  [true, true, true, true, true, true, false, false, false, false]

theorem wSix_length : wSix.length = 10 := rfl
theorem wSix_oddCount : oddCount wSix = 6 := rfl
theorem wSix_heavy : heavy wSix = true := rfl
theorem wSix_C : C wSix = 665 := rfl
theorem wSix_gap : gap wSix = 295 := rfl
theorem wSix_gap_pos : 0 < gap wSix := by decide
theorem wSix_gcd : Nat.gcd (C wSix) (gap wSix) = 5 := rfl
theorem wSix_delta : delta wSix = 59 := rfl

/-- **The coprimality strengthening is false.**  There is a heavy positive-gap
word with `gcd(C, G) = 5`. -/
theorem coprime_false :
    ¬ (∀ w : List Bool, heavy w = true → 0 < gap w → Nat.gcd (C w) (gap w) = 1) := by
  intro h
  have := h wSix wSix_heavy wSix_gap_pos
  rw [wSix_gcd] at this
  exact absurd this (by decide)

/-- …while the real target is untouched at that word: `δ = 59 > 1`, i.e. `G ∤ C`.
So `gcd(C,G) = 1` is strictly stronger than `G ∤ C` **and** it is false; only the
weak form can be the target. -/
theorem wSix_not_cycle_word : ¬ (gap wSix ∣ C wSix) := by decide

/-! ## 3. Heaviness pins the length -/

/-- The engine of `heavy_ledge`: the last proper prefix tested by `heavyAux` is
the one of length `|w| − 1`, and its test is `2 ^ (i + |w| − 1) ≤ 3 ^ (a + …)`. -/
theorem heavyAux_last :
    ∀ (w : List Bool) (i a : Nat), heavyAux w i a = true → 2 ≤ w.length →
      2 ^ (i + w.length - 1) ≤ 3 ^ (a + oddCount w)
  | [], _, _, _, h => by simp at h
  | [_], _, _, _, h => by simp at h
  | b :: c :: w', i, a, hh, _ => by
    have hstep : decide (2 ^ (i + 1) ≤ 3 ^ (a + (if b then 1 else 0))) = true
        ∧ heavyAux (c :: w') (i + 1) (a + (if b then 1 else 0)) = true := by
      have : heavyAux (b :: c :: w') i a
          = (decide (2 ^ (i + 1) ≤ 3 ^ (a + (if b then 1 else 0)))
              && heavyAux (c :: w') (i + 1) (a + (if b then 1 else 0))) := rfl
      rw [this, Bool.and_eq_true] at hh
      exact hh
    have hone : 2 ^ (i + 1) ≤ 3 ^ (a + (if b then 1 else 0)) := of_decide_eq_true hstep.1
    have hodd : oddCount (b :: c :: w') = (if b then 1 else 0) + oddCount (c :: w') := rfl
    cases w' with
    | nil =>
      have hlen : (b :: c :: ([] : List Bool)).length = 2 := rfl
      rw [hlen, hodd]
      have h1 : i + 2 - 1 = i + 1 := by omega
      rw [h1]
      have h2 : a + (if b then 1 else 0) ≤ a + ((if b then 1 else 0) + oddCount [c]) := by
        omega
      exact Nat.le_trans hone (Nat.pow_le_pow_right (by omega) h2)
    | cons d w'' =>
      have hIH := heavyAux_last (c :: d :: w'') (i + 1) (a + (if b then 1 else 0))
        hstep.2 (by simp)
      have hlen : i + 1 + (c :: d :: w'').length - 1
          = i + (b :: c :: d :: w'').length - 1 := by simp; omega
      have hcnt : a + (if b then 1 else 0) + oddCount (c :: d :: w'')
          = a + oddCount (b :: c :: d :: w'') := by rw [hodd]; omega
      rw [hlen, hcnt] at hIH
      exact hIH

/-- **A heavy word of length `≥ 2` is on or below the ledge.** -/
theorem heavy_ledge {w : List Bool} (h : heavy w = true) (h2 : 2 ≤ w.length) :
    2 ^ (w.length - 1) ≤ 3 ^ oddCount w := by
  have := heavyAux_last w 0 0 h h2
  simpa using this

/-- **Heaviness and a positive gap determine the length from the odd count.**
`3 ^ a < 2 ^ L ≤ 2 · 3 ^ a`, so `L = ⌊a log₂ 3⌋ + 1` and the heavy positive-gap
words form a one-parameter family. -/
theorem heavy_gap_pos_sandwich {w : List Bool} (h : heavy w = true)
    (h2 : 2 ≤ w.length) (hg : 0 < gap w) :
    3 ^ oddCount w < 2 ^ w.length ∧ 2 ^ w.length ≤ 2 * 3 ^ oddCount w := by
  have hlow : 3 ^ oddCount w < 2 ^ w.length := by
    have : gap w = 2 ^ w.length - 3 ^ oddCount w := rfl
    rw [this] at hg
    have hpos : 0 < 2 ^ w.length := Nat.two_pow_pos _
    omega
  refine ⟨hlow, ?_⟩
  have hled := heavy_ledge h h2
  have hsplit : (2:Nat) ^ w.length = 2 * 2 ^ (w.length - 1) := by
    have : w.length = (w.length - 1) + 1 := by omega
    rw [this]
    rw [Nat.pow_succ]
    have : w.length - 1 + 1 - 1 = w.length - 1 := by omega
    rw [this]
    omega
  omega

end DeltaAdversaryXIV
end Collatz
