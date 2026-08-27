import Collatz.Strategy.AccumulatorAutomaton

/-!
# The exchange law: what the accumulator pays for the order of the odd steps

`AccumulatorAutomaton.C_eq_Crel` writes the accumulator as a function of the odd
step *times* alone,

`C(w) = Crel [t₁, …, t_a] = Σ_i 3 ^ (a − i) · 2 ^ (t_i)`,

and records that every invariant blind to those times is vacuous.  This file
supplies the missing quantitative half: **exactly what changes when a single odd
step moves one tick later**, and the ordering principle that follows.

## The exchange constant

`Crel_bump`:  `Crel (u ++ (t+1) :: v) = Crel (u ++ t :: v) + 3 ^ |v| · 2 ^ t`.

At the level of words this is the adjacent transposition `OE ↦ EO`
(`C_exchange`): the two words have the same length, the same odd count and the
same valuation total, and their accumulators differ by exactly

`3 ^ (odd count of the suffix) · 2 ^ (length of the prefix)`.

So the accumulator is **strictly** order-sensitive, with an explicit constant —
the exact form of the noncommutativity that the multiplicative invariant
`(j, a) ↦ (2 ^ j, 3 ^ a)` discards, since both those numbers are unchanged by
the swap.

## The ordering principle

`Crel_mono` / `Crel_lt_of_lt`: raising odd-step times pointwise raises the
accumulator, strictly as soon as one time genuinely rises.  Iterating from the
bottom and from the top pins the two extremes exactly:

* earliest possible odd steps, `[0, 1, …, a−1]`:  `Crel + 2 ^ a = 3 ^ a`;
* latest possible, `[t, t+1, …, t+a−1]`:  `Crel + 2 ^ (t+a) = 2 ^ t · 3 ^ a`.

These are the two bounds `AffineExact.three_pow_le_affineC` and
`AffineExact.affineC_le`, now derived from a single exchange law rather than by
two separate inductions, and with the exact gap between them:

`max − min = (2 ^ t − 1) · (3 ^ a − 2 ^ a)`   (`Crel_extremal_gap`).

## Honest reading — what the order-sensitivity is worth

The never-drop demand `deficit m j = 2 ^ j m − 3 ^ a m` depends on `(j, a)` only,
so the exchange law moves `C` while leaving the demand fixed: among all windows
with a given `(j, a)`, the never-drop inequality is **hardest for the earliest
arrangement and easiest for the latest** (`window_mono`).  That is a genuine
majorization principle, and it is the reason the positional cap is the right
upper bound.

It does not, by itself, exclude anything, and the reason is recorded rather than
rediscovered: every parity word of length `j` is realised by exactly one residue
class mod `2 ^ j`, so the extremal arrangement is always arithmetically
realizable, and `maxC(never-drop compatible) = maxC(all words)` at every level
measured.  The order information is real; the extremum it selects is not
forbidden.
-/

namespace Collatz
namespace AffineExchange

open DeltaSpectrum AccumulatorAutomaton

/-! ## The append law for `Crel` -/

/-- `Crel` is a cocycle for concatenation of time lists: the prefix is amplified
by `3` once per later odd step. -/
theorem Crel_append : ∀ (u v : List Nat),
    Crel (u ++ v) = 3 ^ v.length * Crel u + Crel v := by
  intro u
  induction u with
  | nil => intro v; simp [Crel]
  | cons t u ih =>
    intro v
    show 3 ^ (u ++ v).length * 2 ^ t + Crel (u ++ v)
        = 3 ^ v.length * (3 ^ u.length * 2 ^ t + Crel u) + Crel v
    rw [ih v, List.length_append, Nat.pow_add]
    have h : (3:Nat) ^ u.length * 3 ^ v.length = 3 ^ v.length * 3 ^ u.length :=
      Nat.mul_comm _ _
    rw [h, Nat.mul_add, Nat.mul_assoc]
    omega

/-- Scaling every odd-step time by a common shift scales the accumulator. -/
theorem Crel_shift : ∀ (ts : List Nat) (s : Nat),
    Crel (ts.map (· + s)) = 2 ^ s * Crel ts := by
  intro ts
  induction ts with
  | nil => intro s; simp [Crel]
  | cons t ts ih =>
    intro s
    show 3 ^ (ts.map (· + s)).length * 2 ^ (t + s) + Crel (ts.map (· + s))
        = 2 ^ s * (3 ^ ts.length * 2 ^ t + Crel ts)
    rw [ih s, List.length_map, Nat.pow_add, Nat.mul_add]
    have h : (3:Nat) ^ ts.length * (2 ^ t * 2 ^ s) = 2 ^ s * (3 ^ ts.length * 2 ^ t) := by
      rw [Nat.mul_comm (2 ^ t) (2 ^ s), Nat.mul_left_comm]
    rw [h]

/-! ## The exchange law -/

/-- **The exchange constant.**  Moving one odd step from time `t` to time `t + 1`
raises the accumulator by exactly `3 ^ (number of later odd steps) · 2 ^ t`. -/
theorem Crel_bump (u v : List Nat) (t : Nat) :
    Crel (u ++ (t + 1) :: v) = Crel (u ++ t :: v) + 3 ^ v.length * 2 ^ t := by
  rw [Crel_append u ((t + 1) :: v), Crel_append u (t :: v)]
  show 3 ^ (v.length + 1) * Crel u + (3 ^ v.length * 2 ^ (t + 1) + Crel v)
      = 3 ^ (v.length + 1) * Crel u + (3 ^ v.length * 2 ^ t + Crel v)
        + 3 ^ v.length * 2 ^ t
  have hp : (2:Nat) ^ (t + 1) = 2 ^ t + 2 ^ t := by
    rw [Nat.pow_succ]; omega
  rw [hp, Nat.mul_add]
  omega

/-- The bump is a strict increase. -/
theorem Crel_bump_lt (u v : List Nat) (t : Nat) :
    Crel (u ++ t :: v) < Crel (u ++ (t + 1) :: v) := by
  rw [Crel_bump]
  have h1 : 0 < (3:Nat) ^ v.length := Nat.pow_pos (by omega)
  have h2 : 0 < (2:Nat) ^ t := Nat.pow_pos (by omega)
  have : 0 < 3 ^ v.length * 2 ^ t := Nat.mul_pos h1 h2
  omega

/-- Moving one odd step from `t` to any later time `s` raises the accumulator. -/
theorem Crel_bump_le (u v : List Nat) : ∀ (t s : Nat), t ≤ s →
    Crel (u ++ t :: v) ≤ Crel (u ++ s :: v) := by
  intro t s hts
  rw [Crel_append u (t :: v), Crel_append u (s :: v)]
  show 3 ^ (v.length + 1) * Crel u + (3 ^ v.length * 2 ^ t + Crel v)
      ≤ 3 ^ (v.length + 1) * Crel u + (3 ^ v.length * 2 ^ s + Crel v)
  have hp : (2:Nat) ^ t ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hts
  have := Nat.mul_le_mul_left (3 ^ v.length) hp
  omega

/-! ## Pointwise domination of the time lists -/

/-- `Dom ts ss`: the two time lists have the same length and every time in `ss` is
at least the corresponding time in `ts`. -/
def Dom : List Nat → List Nat → Prop
  | [], [] => True
  | t :: ts, s :: ss => t ≤ s ∧ Dom ts ss
  | _, _ => False

theorem Dom_refl : ∀ ts : List Nat, Dom ts ts
  | [] => trivial
  | _ :: ts => ⟨Nat.le_refl _, Dom_refl ts⟩

theorem Dom_length : ∀ (ts ss : List Nat), Dom ts ss → ts.length = ss.length
  | [], [], _ => rfl
  | _ :: ts, _ :: ss, h => by
      have := Dom_length ts ss h.2
      simp [this]
  | [], _ :: _, h => absurd h (by simp [Dom])
  | _ :: _, [], h => absurd h (by simp [Dom])

/-- **The ordering principle.**  Later odd steps never cost less: pointwise
domination of the time lists implies domination of the accumulators. -/
theorem Crel_mono : ∀ (ts ss : List Nat), Dom ts ss → Crel ts ≤ Crel ss
  | [], [], _ => Nat.le_refl _
  | t :: ts, s :: ss, h => by
      have hlen : ts.length = ss.length := Dom_length ts ss h.2
      have hrec : Crel ts ≤ Crel ss := Crel_mono ts ss h.2
      have hp : (2:Nat) ^ t ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) h.1
      have hm : 3 ^ ts.length * 2 ^ t ≤ 3 ^ ss.length * 2 ^ s := by
        rw [hlen]
        exact Nat.mul_le_mul_left _ hp
      show 3 ^ ts.length * 2 ^ t + Crel ts ≤ 3 ^ ss.length * 2 ^ s + Crel ss
      omega
  | [], _ :: _, h => absurd h (by simp [Dom])
  | _ :: _, [], h => absurd h (by simp [Dom])

/-! ## The two extremes, from the one law

The earliest arrangement is `[0, 1, …, a−1]` and the latest is that list shifted
by the even count.  Both evaluate in closed form. -/

/-- **Earliest odd steps.**  `Crel [0, 1, …, a−1] = 3 ^ a − 2 ^ a`, stated without
subtraction.  This is the exact minimum over arrangements with `a` odd steps. -/
theorem Crel_range : ∀ a : Nat, Crel (List.range a) + 2 ^ a = 3 ^ a := by
  intro a
  induction a with
  | zero => simp [Crel]
  | succ a ih =>
    rw [List.range_succ, Crel_append (List.range a) [a]]
    show 3 ^ 1 * Crel (List.range a) + (3 ^ 0 * 2 ^ a + 0) + 2 ^ (a + 1) = 3 ^ (a + 1)
    have h2 : (2:Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
    have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ]; omega
    simp only [Nat.pow_one, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    omega

/-- **Latest odd steps.**  Shifting the earliest arrangement by `s` gives
`Crel + 2 ^ s · 2 ^ a = 2 ^ s · 3 ^ a`, the exact maximum over arrangements with
`a` odd steps inside a window with `s` even steps before them. -/
theorem Crel_range_shift (a s : Nat) :
    Crel ((List.range a).map (· + s)) + 2 ^ s * 2 ^ a = 2 ^ s * 3 ^ a := by
  rw [Crel_shift]
  have h := Crel_range a
  have := Nat.mul_le_mul_left (2 ^ s) (Nat.le_of_eq h.symm)
  rw [← h, Nat.mul_add]

/-- **The exact spread of the accumulator at fixed `(j, a)`.**  Between the
earliest and the latest arrangement the accumulator moves by
`(2 ^ s − 1)(3 ^ a − 2 ^ a)`, stated without subtraction. -/
theorem Crel_extremal_gap (a s : Nat) :
    Crel (List.range a) + 2 ^ s * 3 ^ a + 2 ^ a
      = Crel ((List.range a).map (· + s)) + 3 ^ a + 2 ^ s * 2 ^ a := by
  have h1 := Crel_range a
  have h2 := Crel_range_shift a s
  omega

/-! ## The word-level exchange

`times` distributes over concatenation, so the list statements above transfer to
adjacent transpositions of parity words. -/

/-- Odd-step times of a concatenation: the suffix clock starts at `|u|`. -/
theorem times_append : ∀ (u v : List Bool) (j : Nat),
    times (u ++ v) j = times u j ++ times v (j + u.length) := by
  intro u
  induction u with
  | nil => intro v j; simp [times]
  | cons b u ih =>
    intro v j
    have hlen : j + (u.length + 1) = (j + 1) + u.length := by omega
    cases b with
    | false =>
      show times (u ++ v) (j + 1) = times u (j + 1) ++ times v (j + (u.length + 1))
      rw [ih v (j + 1), hlen]
    | true =>
      show j :: times (u ++ v) (j + 1)
          = (j :: times u (j + 1)) ++ times v (j + (u.length + 1))
      rw [ih v (j + 1), hlen]
      rfl

/-- **The adjacent exchange, at the level of words.**  Swapping an odd letter with
the even letter following it changes nothing about the length, the odd count or
the valuation total, and changes the accumulator by exactly
`3 ^ (odd count of the suffix) · 2 ^ (length of the prefix)`. -/
theorem C_exchange (u v : List Bool) :
    C (u ++ [false, true] ++ v)
      = C (u ++ [true, false] ++ v) + 3 ^ oddCount v * 2 ^ u.length := by
  have hlen : ∀ w : List Bool, ((u ++ [false, true] ++ w)).length
      = u.length + 2 + w.length := by
    intro w; simp [List.length_append]; omega
  have hA : times (u ++ [false, true] ++ v) 0
      = times u 0 ++ ((u.length + 1) :: times v (u.length + 2)) := by
    rw [List.append_assoc, times_append u ([false, true] ++ v) 0]
    have h : times ([false, true] ++ v) (0 + u.length)
        = (u.length + 1) :: times v (u.length + 2) := by
      show times ([false, true] ++ v) (0 + u.length)
          = (u.length + 1) :: times v (u.length + 2)
      rw [times_append [false, true] v (0 + u.length)]
      have h2 : times [false, true] (0 + u.length) = [0 + u.length + 1] := by
        simp [times]
      rw [h2]
      have h3 : (0 + u.length) + ([false, true] : List Bool).length = u.length + 2 := by
        simp
      rw [h3]
      have h4 : 0 + u.length + 1 = u.length + 1 := by omega
      rw [h4]
      rfl
    rw [h]
  have hB : times (u ++ [true, false] ++ v) 0
      = times u 0 ++ (u.length :: times v (u.length + 2)) := by
    rw [List.append_assoc, times_append u ([true, false] ++ v) 0]
    have h : times ([true, false] ++ v) (0 + u.length)
        = u.length :: times v (u.length + 2) := by
      rw [times_append [true, false] v (0 + u.length)]
      have h2 : times [true, false] (0 + u.length) = [0 + u.length] := by
        simp [times]
      rw [h2]
      have h3 : (0 + u.length) + ([true, false] : List Bool).length = u.length + 2 := by
        simp
      rw [h3]
      have h4 : 0 + u.length = u.length := by omega
      rw [h4]
      rfl
    rw [h]
  rw [C_eq_Crel, C_eq_Crel, hA, hB, Crel_bump (times u 0) (times v (u.length + 2)) u.length]
  rw [times_length v (u.length + 2)]

/-- The swap is a strict increase: an odd step taken later always costs more. -/
theorem C_exchange_lt (u v : List Bool) :
    C (u ++ [true, false] ++ v) < C (u ++ [false, true] ++ v) := by
  rw [C_exchange]
  have h1 : 0 < (3:Nat) ^ oddCount v := Nat.pow_pos (by omega)
  have h2 : 0 < (2:Nat) ^ u.length := Nat.pow_pos (by omega)
  have : 0 < 3 ^ oddCount v * 2 ^ u.length := Nat.mul_pos h1 h2
  omega

/-! ## The majorization principle for the never-drop demand

The demand `2 ^ j · m − 3 ^ a · m` sees only `(j, a)`, and an adjacent
transposition changes neither.  So over the words of a fixed shape the never-drop
inequality is monotone in the arrangement: hardest at the earliest odd steps,
easiest at the latest. -/

/-- **Majorization.**  If a time list meets a demand `D`, so does every pointwise
later one.  The demand is the same number in both cases — it depends on the shape
`(j, a)`, which domination preserves. -/
theorem window_mono {ts ss : List Nat} (h : Dom ts ss) {D : Nat}
    (hmeet : D ≤ Crel ts) : D ≤ Crel ss :=
  Nat.le_trans hmeet (Crel_mono ts ss h)

/-- The earliest arrangement is the hardest case: if it meets the demand, every
arrangement of the same shape does. -/
theorem window_of_earliest {a : Nat} {ss : List Nat} (h : Dom (List.range a) ss)
    {D : Nat} (hmeet : D ≤ Crel (List.range a)) : D ≤ Crel ss :=
  window_mono h hmeet

end AffineExchange
end Collatz
