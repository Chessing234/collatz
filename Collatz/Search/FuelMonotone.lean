import Collatz.Search.Sieved

/-!
# Fuel monotonicity for the block sweep

`Search.VerifiedExtended` notes that its fuel could be left at `200` only because
the first block needing more (`m = 1099`, `n = 1 126 015`, needing `224`) lies
past its endpoint, "which is why no monotonicity plumbing is required".  Any
further extension does cross that block, so the plumbing is required now.

This file supplies it.  `dropsWithin` is monotone in the fuel — spending more
steps cannot turn a found drop into a missed one — and so are `checkBlock` and
`checkRange`.  The consequence is that the sweeps already proved at fuel `200`
can be read at any larger fuel *for free*, so extending the range past block
`1099` costs only the new blocks, not a re-run of the old ones.

## Why this is the binding piece

With `Strategy.PreCertified` and `Strategy.FrontierParametric` in place, the
verified range is the only outstanding input to the next frontier rung: reaching
`1 358 718` yields `L ≥ 7863` by instantiation alone.  That range is `1327`
blocks against the present `1061`, and a direct scan of `[1 086 464, 1 358 718)`
shows the worst drop time there is exactly `224`, at `n = 1 126 015`.  So the
extension needs `266` further blocks at fuel `224` — and, via the lemmas below,
nothing at all from the `1061` blocks already done.
-/

namespace Collatz
namespace Search

open Reach

/-- One extra unit of fuel never loses a drop. -/
theorem dropsAux_succ_of {n : Nat} : ∀ (fuel cur : Nat),
    dropsAux n fuel cur = true → dropsAux n (fuel + 1) cur = true := by
  intro fuel
  induction fuel with
  | zero => intro cur h; exact absurd h (by simp [dropsAux])
  | succ fuel ih =>
    intro cur h
    rw [dropsAux_succ] at h
    rw [dropsAux_succ]
    by_cases hs : acceleratedStep cur < n
    · rw [if_pos hs]
    · rw [if_neg hs] at h
      rw [if_neg hs]
      exact ih _ h

/-- `dropsAux` is monotone in the fuel. -/
theorem dropsAux_add {n : Nat} : ∀ (f d cur : Nat),
    dropsAux n f cur = true → dropsAux n (f + d) cur = true := by
  intro f d cur h
  induction d with
  | zero => exact h
  | succ d ih =>
    have hrw : f + (d + 1) = (f + d) + 1 := by omega
    rw [hrw]
    exact dropsAux_succ_of _ _ ih

theorem dropsAux_mono {n : Nat} (f f' cur : Nat) (hle : f ≤ f')
    (h : dropsAux n f cur = true) : dropsAux n f' cur = true := by
  obtain ⟨d, rfl⟩ : ∃ d, f' = f + d := ⟨f' - f, by omega⟩
  exact dropsAux_add f d cur h

/-- **`dropsWithin` is monotone in the fuel.** -/
theorem dropsWithin_mono {f f' n : Nat} (hle : f ≤ f')
    (h : dropsWithin f n = true) : dropsWithin f' n = true :=
  dropsAux_mono f f' n hle h

/-- Hence so is the block checker. -/
theorem checkBlock_mono {m f f' : Nat} (hle : f ≤ f')
    (h : checkBlock m f = true) : checkBlock m f' = true := by
  rw [checkBlock, List.all_eq_true] at h ⊢
  intro r hr
  exact dropsWithin_mono hle (h r hr)

/-- And so is a whole range sweep: **a sweep proved at one fuel may be read at
any larger fuel, with no recomputation.** -/
theorem checkRange_mono {lo len f f' : Nat} (hle : f ≤ f') :
    checkRange lo len f = true → checkRange lo len f' = true := by
  induction len with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [checkRange, Bool.and_eq_true] at h ⊢
    exact ⟨checkBlock_mono hle h.1, ih h.2⟩

end Search
end Collatz
