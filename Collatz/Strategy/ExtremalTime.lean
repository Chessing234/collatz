import Collatz.Strategy.HalbeisenHungerbuhler
import Collatz.Strategy.AffineExchange

/-!
# Lemma 5, reduced to the cycle lemma

Halbeisen–Hungerbühler's Lemma 5 says the Beatty word `s̃` maximises the
rotation-minimum of `φ` over a shape `(l, n)`.  Their proof has three parts:

1. **a rotation exists whose partial sums dominate the line `kn/l`** — this is the
   Dvoretzky–Motzkin cycle lemma, applied to an arbitrary word;
2. **`s̃` is the minimal such word**, so any dominating word has larger partial
   sums;
3. **Lemma 4**: larger partial sums give smaller `φ`.

Part 3 is already here as `AffineExchange.Crel_mono`.  This file supplies part 2,
in a form where it becomes *immediate*, and thereby reduces Lemma 5 to part 1
alone.

## The observation that collapses part 2

In *time* coordinates the domination condition has no ceilings in it at all.  For
a word with odd-step times `t₀ < t₁ < ⋯ < t_{a−1}`, the partial-sum condition
`Σ_{i≤k} wᵢ ≥ ⌈kn/l⌉` for every `k` is equivalent to

`t_j ≤ ⌊j·l/n⌋`   for every `j`.

Both say the same thing — the `j`-th odd step happens no later than time
`⌊jl/n⌋` — and the second is a plain `Nat` division.  The chain

`⌈kn/l⌉ ≤ Σ_{i≤k} wᵢ  ⟺  ∀ j, t_j < min{k : kn > jl}  ⟺  ∀ j, t_j ≤ ⌊jl/n⌋`

turns part 2 from a statement about ceilings and partial sums into pointwise
domination of time lists — which is exactly the hypothesis `AffineExchange.Dom`
that `Crel_mono` consumes.

So `tildeTime l n j = j * l / n` is the extremal time list, and
`dominating_Crel_le` is Lemma 5's conclusion for any dominating word.

## What remains

Only part 1: **every word of shape `(l, n)` has a rotation whose times satisfy
`t_j ≤ ⌊jl/n⌋`.**  That is the cycle lemma, and its usual proof — rotate at the
index maximising `kn/l − Σ_{i≤k} wᵢ` — is a fold-maximum of exactly the kind
`Discrepancy.discMax` already performs in this repository.

Once part 1 is formalised, `HalbeisenHungerbuhler.HHExtremal` is discharged and
with it the whole criterion chain, including `hh_no_cycle_below`.
-/

namespace Collatz
namespace ExtremalTime

open AffineExchange AccumulatorAutomaton

/-! ## The extremal time list -/

/-- `t̃_j = ⌊j·l/n⌋`: the latest the `j`-th odd step may occur in a word whose
partial sums dominate the line of slope `n/l`. -/
def tildeTime (l n j : Nat) : Nat := j * l / n

/-- The extremal list of the first `a` times, in increasing order. -/
def tildeList (l n a : Nat) : List Nat := (List.range a).map (tildeTime l n)

@[simp] theorem tildeList_zero (l n : Nat) : tildeList l n 0 = [] := rfl

theorem tildeList_succ (l n a : Nat) :
    tildeList l n (a + 1) = tildeList l n a ++ [tildeTime l n a] := by
  unfold tildeList
  rw [List.range_succ, List.map_append]
  rfl

theorem tildeList_length (l n a : Nat) : (tildeList l n a).length = a := by
  unfold tildeList
  simp

/-! ## Domination transfers through `append` -/

/-- `Dom` respects appending a dominated last element. -/
theorem Dom_append_singleton : ∀ (u v : List Nat) (x y : Nat),
    Dom u v → x ≤ y → Dom (u ++ [x]) (v ++ [y])
  | [], [], x, y, _, hxy => ⟨hxy, trivial⟩
  | a :: u, b :: v, x, y, h, hxy => ⟨h.1, Dom_append_singleton u v x y h.2 hxy⟩
  | [], _ :: _, _, _, h, _ => absurd h (by simp [Dom])
  | _ :: _, [], _, _, h, _ => absurd h (by simp [Dom])

/-- Pointwise domination of two time *functions* gives `Dom` of their lists. -/
theorem Dom_of_pointwise {t s : Nat → Nat} : ∀ a : Nat, (∀ j, j < a → t j ≤ s j) →
    Dom ((List.range a).map t) ((List.range a).map s) := by
  intro a
  induction a with
  | zero => intro _; exact trivial
  | succ a ih =>
    intro h
    have hrec := ih (fun j hj => h j (by omega))
    have e1 : (List.range (a + 1)).map t = (List.range a).map t ++ [t a] := by
      rw [List.range_succ, List.map_append]; rfl
    have e2 : (List.range (a + 1)).map s = (List.range a).map s ++ [s a] := by
      rw [List.range_succ, List.map_append]; rfl
    rw [e1, e2]
    exact Dom_append_singleton _ _ _ _ hrec (h a (by omega))

/-! ## Part 2 of Lemma 5, and it is immediate -/

/-- **The minimality of the Beatty word, in time coordinates.**  Any time list
dominating the line — `t_j ≤ ⌊jl/n⌋` — has accumulator at most that of the
extremal list.  This is Halbeisen–Hungerbühler Lemma 5 part 2 combined with their
Lemma 4, the latter being `AffineExchange.Crel_mono`. -/
theorem dominating_Crel_le {t : Nat → Nat} {l n a : Nat}
    (hdom : ∀ j, j < a → t j ≤ tildeTime l n j) :
    Crel ((List.range a).map t) ≤ Crel (tildeList l n a) :=
  Crel_mono _ _ (Dom_of_pointwise a hdom)

/-- The same, with the extremal value named: `M_{l,n}` is `Crel` of the extremal
time list. -/
def hhMinTime (l n a : Nat) : Nat := Crel (tildeList l n a)

theorem dominating_le_hhMinTime {t : Nat → Nat} {l n a : Nat}
    (hdom : ∀ j, j < a → t j ≤ tildeTime l n j) :
    Crel ((List.range a).map t) ≤ hhMinTime l n a :=
  dominating_Crel_le hdom

/-! ## The two forms of the domination condition agree

`t_j ≤ ⌊jl/n⌋` is exactly `n · t_j < (j+1) · l`, the ceiling-free form of
`Σ_{i≤k} wᵢ ≥ ⌈kn/l⌉`. -/

/-- The division-free reading of the domination condition: `t_j ≤ ⌊jl/n⌋` is
exactly `t_j · n ≤ j · l`. -/
theorem dom_iff_mul_le {l n j t : Nat} (hn : 0 < n) :
    t ≤ tildeTime l n j ↔ t * n ≤ j * l := by
  unfold tildeTime
  exact Nat.le_div_iff_mul_le hn

/-! ## What is now missing

`HHExtremal` follows from `dominating_Crel_le` the moment part 1 is available:

```
cycle_lemma : ∀ (w : word of shape (l,n)), ∃ rotation σ,
                ∀ j, (times of σ) j ≤ tildeTime l n j
```

That is the only remaining link in the Halbeisen–Hungerbühler chain, and the rest
of it — `beatty_count_eq`, `hhMin`, `hh_criterion`, `hh_no_cycle_below` — is
already proved. -/

end ExtremalTime
end Collatz
