import Collatz.Strategy.HHBridge
import Collatz.Strategy.Discrepancy
import Collatz.Strategy.HalbeisenHungerbuhler

/-!
# Lemma 5, proved

`HalbeisenHungerbuhler.HHExtremal` names Halbeisen–Hungerbühler's Lemma 5 — that
`hhMin` really is the minimum of the accumulator over the admissible words — and
the repository carried it as an **assumed `Prop`** through many rounds, with
`hh_criterion` and `hh_no_cycle_below` conditional on it.

This file discharges it.

## The four gaps, and how they closed

* **(1), (2)** `HHBridge` — the word side and the orbit side of the accumulator
  are one recursion: `affineC L x = C (word x L)`.
* **(3)** `HHMinTime` — `hhMinTime l n n = hhMin l n l`, the two constructions of
  `M_{l,n}` reindexed along the support of the ceiling Beatty word.  True only
  after the Round XXXIX floor/ceiling correction.
* **(4a)** `RotationLaw` — `oddCount` over a full period is rotation-invariant, so
  the gap `2 ^ L − 3 ^ a` belongs to the cycle rather than to the point, and a
  bound at *any* rotation bounds the orbit minimum.
* **(4b)** `HHBridge.T` and `rotation_position_bound` — the `j`-th one-position,
  bounded by the `j`-th extremal Beatty time.
* **(4c)** here — `times_word_eq`, the last identity: the positions `times`
  reads off the word are exactly the one-positions `T`.

## The chain

`times_append` mirrors `accC_append` and lets the snoc-shaped `word` meet the
head-shaped `times`.  `T_stable` says lengthening the window does not move an
already-found position.  With those, `times_word_eq` goes by induction on `L`,
splitting on the last letter; the `1` branch turns on
`T y (L+1) (oddCount y L) = L` — the next one-position after all the earlier ones
is the new letter itself.

Then, for the rotation `r` that `cycle_lemma` selects:

`(2^L − 3^a)·x ≤ affineC L (orbit r x) = C (word …) = Crel (times …)`
`= Crel ((range a).map (T …)) ≤ hhMinTime L a a = hhMin L a L`

the first step by `RotationLaw.gap_mul_le_affineC_rotation`, the last by
`ExtremalTime.dominating_le_hhMinTime` and `HHMinTime.hhMinTime_eq_hhMin`.

## What this does and does not buy

`hh_criterion` and `hh_no_cycle_below` are now **unconditional**.  That is the
sharp Halbeisen–Hungerbühler criterion, in place of this repository's own weaker
product bound.

It is a statement about **cycles only**.  It says nothing about divergent orbits,
and it is not a proof of the Collatz conjecture.

**And at this repository's verified range it buys no new number.**  Evaluating the
criterion at `c = 1 086 464` — `hhMin L n L < (2 ^ L − 3 ^ n) · c` at the largest
admissible `n` — it holds for every `L ≤ 6808` and fails first at exactly
`(L, n) = (6809, 4296)`.  That is precisely the wall of
`RealizableFrontier6809.length_ge_6809`, which the repository already proves
unconditionally by a completely different route.  The sharp criterion reproduces
the existing bound and does not exceed it.

The reason is that both methods are stopped by the same Diophantine obstruction:
`6809/4296` is a semiconvergent of `log₂ 3` (`6809 = 485 + 6·1054`, the ladder of
`ExclusionRatio`), where `3 ^ n` sits so close to `2 ^ L` from below that the gap
`2 ^ L − 3 ^ n` collapses relative to `hhMin`.  Sharpening the *criterion* does not
move a wall whose position is set by how well `n/L` approximates `log₃ 2`.

What the proof does buy is exchange rate: the criterion is sharp, so any future
increase in the verified range converts into length more efficiently than the
product bound does.  Conditionally on Barina's `704 · 2 ^ 60` the criterion is
known to survive past `L = 125 743`, well beyond the `40 001` the repository's
conditional sweep records — but that is a measurement, not a kernel-checked
theorem, and certifying it would need an `O(log L)` evaluation of `hhMin` that
does not exist here.
-/

namespace Collatz
namespace HHBridge

open AccCycle DeltaSpectrum AccumulatorAutomaton

/-! ## `times` append law -/

theorem times_append : ∀ (u v : List Bool) (j : Nat),
    times (u ++ v) j = times u j ++ times v (j + u.length) := by
  intro u
  induction u with
  | nil => intro v j; simp [times]
  | cons b u ih =>
    intro v j
    cases b with
    | false =>
      show times (u ++ v) (j + 1) = times u (j + 1) ++ times v (j + (u.length + 1))
      rw [ih v (j + 1)]
      have : j + 1 + u.length = j + (u.length + 1) := by omega
      rw [this]
    | true =>
      show j :: times (u ++ v) (j + 1) = j :: times u (j + 1) ++ times v (j + (u.length + 1))
      rw [ih v (j + 1)]
      have : j + 1 + u.length = j + (u.length + 1) := by omega
      rw [this]
      rfl

/-! ## `oddCount` monotonicity, from the existing split law -/

theorem oddCount_mono (y : Nat) {m n : Nat} (h : m ≤ n) :
    oddCount y m ≤ oddCount y n := by
  have hsplit : oddCount y n = oddCount y m + oddCount (acceleratedOrbit m y) (n - m) :=
    Discrepancy.oddCount_split (n := y) (L := n) (j := m) h
  omega

/-! ## `range`-pointwise congruence for `map`, avoided via induction (no
`List.map_congr` in this repository). -/

theorem map_range_congr {n : Nat} (f g : Nat → Nat)
    (h : ∀ j, j < n → f j = g j) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append]
    have hih : (List.range n).map f = (List.range n).map g :=
      ih (fun j hj => h j (by omega))
    rw [hih]
    simp only [List.map_cons, List.map_nil]
    rw [h n (by omega)]

/-! ## `nextOne` is stable once enough fuel has already found a one-bit. -/

theorem nextOne_fuel_mono (y : Nat) : ∀ start fuel1 fuel2 : Nat, fuel1 ≤ fuel2 →
    oddCount y (start + fuel1) > oddCount y start →
    nextOne y start fuel1 = nextOne y start fuel2 := by
  intro start fuel1
  induction fuel1 generalizing start with
  | zero =>
    intro fuel2 hle h
    simp only [Nat.add_zero] at h
    omega
  | succ f ih =>
    intro fuel2 hle h
    obtain ⟨g, hg⟩ : ∃ g, fuel2 = g + 1 := ⟨fuel2 - 1, by omega⟩
    subst hg
    show (if w y start = 1 then start else nextOne y (start + 1) f)
        = (if w y start = 1 then start else nextOne y (start + 1) g)
    by_cases hb : w y start = 1
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      have hw01 := w_le_one y start
      have hstep : oddCount y (start + 1) = oddCount y start := by
        have h1 := Density.oddCount_succ_last y start
        have hweq : w y start = acceleratedOrbit start y % 2 := rfl
        rw [hweq] at hb
        omega
      have hidx : start + (f + 1) = start + 1 + f := by omega
      have h' : oddCount y (start + 1 + f) > oddCount y (start + 1) := by
        rw [hstep, ← hidx]; exact h
      exact ih (start + 1) g (by omega) h'

/-! ## `T` is stable under extending the horizon, for positions already found. -/

theorem T_stable (y : Nat) : ∀ L j, j < oddCount y L → T y (L + 1) j = T y L j := by
  intro L j
  induction j with
  | zero =>
    intro h
    have hwin : oddCount y (0 + L) > oddCount y 0 := by simpa using h
    have hmono := nextOne_fuel_mono y 0 L (L + 1) (by omega) hwin
    show nextOne y 0 (L + 1) = nextOne y 0 L
    exact hmono.symm
  | succ j ih =>
    intro h
    have hjlt : j < oddCount y L := by omega
    have ihj : T y (L + 1) j = T y L j := ih hjlt
    obtain ⟨hlt, hone, hcnt⟩ := T_spec y L j hjlt
    have hstep : oddCount y (T y L j + 1) = oddCount y (T y L j) + w y (T y L j) :=
      Density.oddCount_succ_last y (T y L j)
    rw [hcnt, hone] at hstep
    have hwinL : oddCount y L > oddCount y (T y L j + 1) := by rw [hstep]; exact h
    have hfuel_le : L - (T y L j + 1) ≤ (L + 1) - (T y L j + 1) := by omega
    have hwin : oddCount y ((T y L j + 1) + (L - (T y L j + 1))) > oddCount y (T y L j + 1) := by
      have heq : (T y L j + 1) + (L - (T y L j + 1)) = L := by omega
      rw [heq]; exact hwinL
    have hmono := nextOne_fuel_mono y (T y L j + 1) (L - (T y L j + 1))
      ((L + 1) - (T y L j + 1)) hfuel_le hwin
    show T y (L + 1) (j + 1) = T y L (j + 1)
    calc T y (L + 1) (j + 1)
        = nextOne y (T y (L + 1) j + 1) ((L + 1) - (T y (L + 1) j + 1)) := rfl
      _ = nextOne y (T y L j + 1) ((L + 1) - (T y L j + 1)) := by rw [ihj]
      _ = nextOne y (T y L j + 1) (L - (T y L j + 1)) := hmono.symm
      _ = T y L (j + 1) := rfl

/-! ## The main identity -/

theorem times_word_eq (y : Nat) : ∀ L,
    times (word y L) 0 = (List.range (oddCount y L)).map (T y L) := by
  intro L
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [word_succ, times_append, word_length]
    by_cases hb : w y L = 1
    · -- odd letter: the new one-position is exactly `L`.
      have hcount : oddCount y (L + 1) = oddCount y L + 1 := by
        have h1 := Density.oddCount_succ_last y L
        have hweq : w y L = acceleratedOrbit L y % 2 := rfl
        rw [hweq] at hb
        omega
      have hb' : decide (w y L = 1) = true := decide_eq_true hb
      have htL : T y (L + 1) (oddCount y L) = L := by
        have hlt : oddCount y L < oddCount y (L + 1) := by omega
        obtain ⟨hltL, _, hcnt⟩ := T_spec y (L + 1) (oddCount y L) hlt
        -- `T y (L+1) (oddCount y L) ≤ L` from `hltL : ... < L + 1`,
        -- and `oddCount` at that point already equals `oddCount y L`, so it
        -- cannot be strictly below `L` (else `oddCount` would have grown
        -- further by the time it reaches `L`, exceeding `oddCount y L`).
        rcases Nat.lt_or_ge (T y (L + 1) (oddCount y L)) L with hcase | hcase
        · exfalso
          have hle : T y (L + 1) (oddCount y L) + 1 ≤ L := by omega
          have hm := oddCount_mono y hle
          have hself : oddCount y (T y (L + 1) (oddCount y L) + 1)
              = oddCount y (T y (L + 1) (oddCount y L)) + w y (T y (L + 1) (oddCount y L)) :=
            Density.oddCount_succ_last y (T y (L + 1) (oddCount y L))
          have hone : w y (T y (L + 1) (oddCount y L)) = 1 := (T_spec y (L + 1) (oddCount y L) hlt).2.1
          rw [hone, hcnt] at hself
          omega
        · omega
      show times (word y L) 0 ++ times [decide (w y L = 1)] (0 + L)
          = (List.range (oddCount y (L + 1))).map (T y (L + 1))
      have htimes1 : times ([decide (w y L = 1)] : List Bool) (0 + L) = [0 + L] := by
        rw [hb']; rfl
      have h0L : (0 : Nat) + L = L := by omega
      rw [htimes1, h0L, ih, hcount, List.range_succ, List.map_append]
      have hpt : (List.range (oddCount y L)).map (T y L)
          = (List.range (oddCount y L)).map (T y (L + 1)) :=
        map_range_congr (T y L) (T y (L + 1)) (fun j hj => (T_stable y L j hj).symm)
      rw [hpt]
      show (List.range (oddCount y L)).map (T y (L + 1)) ++ [L]
          = (List.range (oddCount y L)).map (T y (L + 1)) ++ [T y (L + 1) (oddCount y L)]
      rw [htL]
    · -- even letter: no new position, and the earlier ones are unchanged.
      have hcount : oddCount y (L + 1) = oddCount y L := by
        have h1 := Density.oddCount_succ_last y L
        have hw01 := w_le_one y L
        have hweq : w y L = acceleratedOrbit L y % 2 := rfl
        rw [hweq] at hb
        omega
      have hb' : decide (w y L = 1) = false := decide_eq_false hb
      show times (word y L) 0 ++ times [decide (w y L = 1)] (0 + L)
          = (List.range (oddCount y (L + 1))).map (T y (L + 1))
      have htimes0 : times ([decide (w y L = 1)] : List Bool) (0 + L) = [] := by
        rw [hb']; rfl
      rw [htimes0, ih, hcount, List.append_nil]
      exact map_range_congr (T y L) (T y (L + 1)) (fun j hj => (T_stable y L j hj).symm)

/-! ## The payoff: `HHExtremal`'s conclusion for the chosen rotation. -/

theorem rotation_affineC_le_hhMin {x L : Nat} (h : AccIsCycleOf x L)
    (ha : 0 < oddCount x L) (hL : oddCount x L ≤ L) :
    ∃ r : Nat, r < L ∧
      AffineExact.affineC L (acceleratedOrbit r x) ≤ HalbeisenHungerbuhler.hhMin L (oddCount x L) L := by
  obtain ⟨r, hrlt, hcrel⟩ := rotation_Crel_le h ha
  refine ⟨r, hrlt, ?_⟩
  have hcount : oddCount (acceleratedOrbit r x) L = oddCount x L :=
    RotationLaw.oddCount_rotation_invariant h r
  have hident : times (word (acceleratedOrbit r x) L) 0
      = (List.range (oddCount x L)).map (T (acceleratedOrbit r x) L) := by
    rw [times_word_eq (acceleratedOrbit r x) L, hcount]
  have hchain : AffineExact.affineC L (acceleratedOrbit r x)
      = Crel ((List.range (oddCount x L)).map (T (acceleratedOrbit r x) L)) := by
    rw [affineC_eq_C, C_eq_Crel, hident]
  rw [hchain, ← ExtremalTime.hhMinTime_eq_hhMin (by omega) hL ha]
  exact hcrel

/-! ## Lemma 5

Everything above composes.  `accCycle_bounds` supplies `0 < a` and `a < L`;
`gap_mul_le_affineC_rotation` transports the bound from the chosen rotation back
to the orbit minimum. -/

/-- **Halbeisen–Hungerbühler Lemma 5.**  For a cycle whose minimum is `x`, the gap
times `x` is at most `M_{L,a}`.  This is the hypothesis the repository assumed. -/
theorem hhExtremal_holds : HalbeisenHungerbuhler.HHExtremal := by
  intro x L hx hcyc hmin
  obtain ⟨ha, haL, _⟩ := AccCycle.accCycle_bounds hx hcyc
  obtain ⟨r, _hrlt, hle⟩ := rotation_affineC_le_hhMin hcyc ha (Nat.le_of_lt haL)
  exact Nat.le_trans (RotationLaw.gap_mul_le_affineC_rotation hx hcyc hmin r) hle

/-- **The criterion, unconditional.**  `hh_criterion` with its hypothesis
discharged. -/
theorem hh_criterion' {x L m : Nat} (hx : 0 < x) (hcyc : AccIsCycleOf x L)
    (hmin : ∀ k : Nat, x ≤ acceleratedOrbit k x)
    (hgap : 0 < 2 ^ L - 3 ^ oddCount x L)
    (hsmall : HalbeisenHungerbuhler.hhMin L (oddCount x L) L
        < (2 ^ L - 3 ^ oddCount x L) * m) : x < m :=
  HalbeisenHungerbuhler.hh_criterion hhExtremal_holds hx hcyc hmin hgap hsmall

end HHBridge
end Collatz
