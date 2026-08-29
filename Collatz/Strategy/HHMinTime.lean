import Collatz.Strategy.HalbeisenHungerbuhler
import Collatz.Strategy.ExtremalTime
import Collatz.Strategy.AffineExchange

/-!
# The two forms of `M_{l,n}` are the same number

Halbeisen–Hungerbühler's cycle criterion needs the minimum of the accumulator
over all words with `n` ones in `l` letters, `M_{l,n}`.  The repository builds it
twice: `HalbeisenHungerbuhler.hhMin l n l` folds over **all `l` letter positions**
of the ceiling Beatty word, weighting the `0` letters by nothing; and
`ExtremalTime.hhMinTime l n n = Crel (tildeList l n n)` folds over just the **`n`
one-positions**, given by the extremal times `tildeTime l n i = i·l/n`.

They are one sum, reindexed along the support of the word.  Round XXXIX found
that they were *not* equal as the repository then stood — `beattyRem l n 0` was
`0`, the floor word, while `hhMinTime` used the ceiling word, and the two
disagreed at 136 of the tested points.  With `beattyRem l n 0 = l - 1` they
agree, and this file proves it.

## The proof

The endpoint statement does not induct.  What does is the prefix invariant

**`hhMin l n j = 3 ^ (n − beattyCount l n j) · hhMinTime l n (beattyCount l n j)`**

for every `j ≤ l`: the partial fold over positions `< j` equals `Crel` of the
extremal times consumed so far, corrected by the power of `3` owed to the ones
not yet reached.  At `j = l` the count is `n` (`beatty_count_eq`), the correction
is `3 ^ 0`, and the target falls out.

The step splits on the letter at `j`.  The `1` case needs
`tildeTime_of_bit`: at a one-position `j`, the extremal time of the count there
is `j` itself.  That comes from `beatty_invariant`
(`beattyRem l n j + l · beattyCount l n j = (l−1) + j·n`) together with the
bit-`1` condition `l ≤ beattyRem l n j + n`, which pin
`j·n ≤ beattyCount l n j · l < (j+1)·n` and hence the floor division.

## What it closes, and what it does not

This is gap (3) of the four between `CycleLemma` and
`HalbeisenHungerbuhler.HHExtremal`.  With `HHBridge` closing (1) and (2), the
gap that remained when this file landed was (4): the **rotation law**,
transporting minimality of `x` across the rotation that `cycle_lemma` selects for
itself.  That is now `RotationLaw`, and **`HHExtremal` is proved** in
`HHLemmaFive`; the theorems depending on it are unconditional.
-/

namespace Collatz
namespace ExtremalTime

open AffineExchange AccumulatorAutomaton HalbeisenHungerbuhler

/-- `beattyCount` is monotone in the prefix length. -/
theorem beattyCount_mono (l n : Nat) : ∀ a b, a ≤ b → beattyCount l n a ≤ beattyCount l n b := by
  intro a b h
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hc : a ≤ b
    · have hrec := ih hc
      have hbb := beattyBit_le_one l n b
      show beattyCount l n a ≤ beattyBit l n b + beattyCount l n b
      omega
    · have ha : a = b + 1 := by omega
      subst ha
      exact Nat.le_refl _

/-- The running weight never exceeds `n` within the word. -/
theorem beattyCount_le_n {l n : Nat} (hl : 0 < l) (hnl : n ≤ l) :
    ∀ j, j ≤ l → beattyCount l n j ≤ n := by
  intro j hj
  have hmono := beattyCount_mono l n j l hj
  have heq := beatty_count_eq hl hnl
  omega

/-- **Position lemma.** If the `j`-th letter of the Beatty word is `1`, its running
weight `i = beattyCount l n j` is exactly the index for which the extremal time
`tildeTime l n i` lands back on `j`. -/
theorem tildeTime_of_bit {l n j : Nat} (hl : 0 < l) (hnl : n ≤ l) (_hn : 0 < n)
    (hbit : beattyBit l n j = 1) :
    tildeTime l n (beattyCount l n j) = j := by
  have hle : l ≤ beattyRem l n j + n := by
    unfold beattyBit at hbit
    split at hbit
    · assumption
    · omega
  have hinv := beatty_invariant hl hnl j
  have hlt := beattyRem_lt hl hnl j
  have hcomm : l * beattyCount l n j = beattyCount l n j * l := Nat.mul_comm _ _
  have hlo : j * n ≤ beattyCount l n j * l := by rw [← hcomm]; omega
  have hexpand : (j + 1) * n = j * n + n := by rw [Nat.add_mul, Nat.one_mul]
  have hhi' : beattyCount l n j * l < j * n + n := by rw [← hcomm]; omega
  have hhi : beattyCount l n j * l < (j + 1) * n := by omega
  unfold tildeTime
  exact Nat.div_eq_of_lt_le hlo hhi

/-- **The generalized invariant.** For every prefix length `j ≤ l`, the `hhMin`
fold over positions `< j` equals `Crel` of the first `beattyCount l n j` extremal
times, corrected by the `3`-power for the `n − beattyCount l n j` ones not yet
consumed. -/
theorem hhMin_eq_hhMinTime_prefix {l n : Nat} (hl : 0 < l) (hnl : n ≤ l) (hn : 0 < n) :
    ∀ j, j ≤ l →
      hhMin l n j = 3 ^ (n - beattyCount l n j) * hhMinTime l n (beattyCount l n j) := by
  intro j
  induction j with
  | zero =>
    intro _
    show (0 : Nat) = 3 ^ (n - 0) * hhMinTime l n 0
    simp [hhMinTime, tildeList_zero, Crel]
  | succ j ih =>
    intro hjl
    have hjl' : j ≤ l := by omega
    have ihj := ih hjl'
    rcases Nat.eq_zero_or_pos (beattyBit l n j) with hb0 | hb1
    · -- bit is 0: the prefix sum and the count do not move
      have hcnt_eq : beattyCount l n (j + 1) = beattyCount l n j := by
        show beattyBit l n j + beattyCount l n j = beattyCount l n j
        omega
      show beattyBit l n j * 2 ^ j * 3 ^ (n - beattyCount l n (j + 1)) + hhMin l n j
          = 3 ^ (n - beattyCount l n (j + 1)) * hhMinTime l n (beattyCount l n (j + 1))
      rw [hcnt_eq, hb0]
      simpa using ihj
    · -- bit is 1: one more one-position, landing exactly at tildeTime l n i
      have hbb := beattyBit_le_one l n j
      have hb1' : beattyBit l n j = 1 := by omega
      have hcnt_eq : beattyCount l n (j + 1) = beattyCount l n j + 1 := by
        show beattyBit l n j + beattyCount l n j = beattyCount l n j + 1
        omega
      have hpos := tildeTime_of_bit (l := l) (n := n) (j := j) hl hnl hn hb1'
      have hnew : hhMinTime l n (beattyCount l n j + 1)
          = 3 * hhMinTime l n (beattyCount l n j) + 2 ^ (tildeTime l n (beattyCount l n j)) := by
        show Crel (tildeList l n (beattyCount l n j + 1))
            = 3 * Crel (tildeList l n (beattyCount l n j))
              + 2 ^ (tildeTime l n (beattyCount l n j))
        rw [tildeList_succ, Crel_append]
        simp [Crel]
      have hcnt_lt : beattyCount l n j < n := by
        have := beattyCount_le_n hl hnl (j + 1) hjl
        omega
      show beattyBit l n j * 2 ^ j * 3 ^ (n - beattyCount l n (j + 1)) + hhMin l n j
          = 3 ^ (n - beattyCount l n (j + 1)) * hhMinTime l n (beattyCount l n (j + 1))
      rw [hb1', hcnt_eq, hnew, hpos, Nat.one_mul, ihj]
      have e1 : (3:Nat) ^ (n - beattyCount l n j)
          = 3 ^ (n - (beattyCount l n j + 1)) * 3 := by
        have hexp : n - beattyCount l n j = (n - (beattyCount l n j + 1)) + 1 := by omega
        rw [hexp, Nat.pow_succ]
      rw [e1]
      generalize (3:Nat) ^ (n - (beattyCount l n j + 1)) = P
      generalize hhMinTime l n (beattyCount l n j) = T
      generalize (2:Nat) ^ j = Q
      calc Q * P + P * 3 * T
          = P * Q + P * 3 * T := by rw [Nat.mul_comm Q P]
        _ = P * 3 * T + P * Q := by rw [Nat.add_comm]
        _ = P * (3 * T) + P * Q := by rw [Nat.mul_assoc]
        _ = P * (3 * T + Q) := by rw [← Nat.mul_add]

/-- **The target.** `hhMinTime` at the full length `n` agrees with `hhMin` at the
full letter count `l` — Halbeisen–Hungerbühler's `M_{l,n}`, in the two forms this
repository builds it. -/
theorem hhMinTime_eq_hhMin {l n : Nat} (hl : 0 < l) (hnl : n ≤ l) (hn : 0 < n) :
    hhMinTime l n n = hhMin l n l := by
  have h := hhMin_eq_hhMinTime_prefix hl hnl hn l (Nat.le_refl l)
  have hc := beatty_count_eq hl hnl
  rw [hc] at h
  simpa using h.symm

end ExtremalTime
end Collatz
