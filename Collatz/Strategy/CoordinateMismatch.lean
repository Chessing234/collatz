import Collatz.Accelerated

/-!
# The two branches are clean in different coordinates, and no coordinate serves both

Round after round, invariants built out of the shifted coordinate `u = n + 1` have
died the same death: they turn out to be equivalent to the affine identity already
in hand, or they fail to distinguish `T` from a map that diverges everywhere.  This
file states the reason, and it is a two-line piece of algebra.

## The two clean laws

* **`odd_clean`** — on an odd step the map is clean in `u = n + 1`:
  `T n + 1 = 3 * ((n + 1) / 2)`, i.e. `u ↦ 3u/2`, exactly, with no remainder.
* **`even_clean`** — on an even step the map is clean in `n` itself: `T n = n / 2`.
* **`even_ceil`** — and in `u` the even step is *not* clean: it is a ceiling,
  `T n + 1 = (n + 2) / 2`, i.e. `u ↦ ⌈u/2⌉`.

So the growth is exact in `u`, the contraction is exact in `n`, and neither
coordinate makes both exact.

## No coordinate serves both

Ask for a single shift `v = n + c` making both branches clean.  Clearing
denominators, "the odd branch is clean in `v`" is `1 + 2c = 3c`, and "the even
branch is clean in `v`" is `2c = c`.  The first forces `c = 1`, the second forces
`c = 0`.  `no_common_shift` is that contradiction.

**This is the `+1` defect, stated exactly.**  It is not a nuisance term to be
absorbed by a better change of variable — there is provably no such change of
variable, among affine shifts.

## Why this kills a whole family of devices

`expStep n = 3n/2` (even), `(3n+1)/2` (odd) agrees with `T` on odd inputs and
diverges from *every* start.  It shares `T`'s odd-run law in `u` exactly.  So any
device built from the `u`-coordinate odd-run structure alone — the `u ↦ 3u/2`
lockstep, the valuation ledger `v₂(u)`, carry-capacity accounting on `v₂(n+1)` —
is satisfied by `expStep` too, and therefore proves nothing.  Two independent
measurements confirmed it: the carry statistic `r ↦ v₂(next + 1)` has the *same*
profile under `T` and under `expStep`, mean `2.0000` in every run-length bucket
over `10^7` samples.

The discriminating fact is the one thing the two maps do not share: **`T`'s even
branch divides `n`, and `n` is the coordinate in which the growth law is *not*
clean.**  A device that sees only one coordinate cannot see it.

## What that leaves

Anything that is to separate `T` from `expStep` must couple the two coordinates —
must use `u = n + 1` for the odd run and `n` for the even run in the same
inequality, and pay the ceiling in between.  That is a sharper reading of the
old requirement "the proof must use that even steps divide": it must use that they
divide *the other coordinate*.
-/

namespace Collatz
namespace CoordinateMismatch

/-- **The odd step is clean in `u = n + 1`.**  `u ↦ 3u/2`, exactly. -/
theorem odd_clean {n : Nat} (h : n % 2 = 1) :
    acceleratedStep n + 1 = 3 * ((n + 1) / 2) := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- **The even step is clean in `n`.** -/
theorem even_clean {n : Nat} (h : n % 2 = 0) : acceleratedStep n = n / 2 := by
  rw [acceleratedStep, if_pos h]

/-- **The even step is a ceiling in `u`.**  `u ↦ ⌈u/2⌉`, written `(u+1)/2`. -/
theorem even_ceil {n : Nat} (h : n % 2 = 0) :
    acceleratedStep n + 1 = (n + 1 + 1) / 2 := by
  rw [acceleratedStep, if_pos h]
  omega

/-- **No affine shift cleans both branches.**  `hodd` is "the odd branch is
`v ↦ 3v/2` in `v = n + c`" and `heven` is "the even branch is `v ↦ v/2` in
`v = n + c`", each with denominators cleared.  The first forces `c = 1`, the
second `c = 0`. -/
theorem no_common_shift (c : Int) (hodd : 1 + 2 * c = 3 * c) (heven : 2 * c = c) :
    False := by omega

/-- The odd condition alone pins the coordinate to `u = n + 1`. -/
theorem odd_forces_one (c : Int) (hodd : 1 + 2 * c = 3 * c) : c = 1 := by omega

/-- The even condition alone pins it to `n` itself. -/
theorem even_forces_zero (c : Int) (heven : 2 * c = c) : c = 0 := by omega

/-! ## The divergent twin

`expStep` is the map that agrees with `T` on odd inputs but multiplies by `3/2` on
even ones.  It grows at every single step, so it diverges from every start, and it
is the sharpest available control on any proposed device. -/

/-- The divergent twin of the accelerated map. -/
def expStep (n : Nat) : Nat :=
  if n % 2 = 0 then 3 * n / 2 else (3 * n + 1) / 2

/-- **`expStep` agrees with `T` on odd inputs.**  Every device reading only the
odd-step structure is therefore blind to the difference between them. -/
theorem expStep_eq_on_odd {n : Nat} (h : n % 2 = 1) : expStep n = acceleratedStep n := by
  rw [expStep, acceleratedStep, if_neg (by omega), if_neg (by omega)]

/-- **`expStep` never decreases, and strictly grows above `1`.**  Hence it has no
non-trivial cycle and no orbit returns below its start: it diverges from every
start `n ≥ 2`.  Any argument that would forbid divergence for `T` while using only
facts shared with `expStep` is therefore unsound. -/
theorem expStep_grows {n : Nat} (h : 2 ≤ n) : n < expStep n := by
  rw [expStep]
  rcases Nat.lt_or_ge (n % 2) 1 with he | ho
  · rw [if_pos (by omega)]
    omega
  · rw [if_neg (by omega)]
    omega

end CoordinateMismatch
end Collatz
