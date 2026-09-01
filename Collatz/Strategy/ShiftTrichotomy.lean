import Collatz.Strategy.AffineCocycle
import Collatz.Strategy.ValuationExchange
import Collatz.Strategy.Mirror

/-!
# One growth law, three shifts: the filters F1 and F2 in a single table

`AffineCocycle` showed that Collatz's block map is affine, `U ↦ λ_a·U + 1`, while the
divergent twin `expStep`'s is purely multiplicative.  That reading put the `+1` in
the *translation* slot of an affine map and made filter F1 exact at block level.

This file finishes the picture, and the answer is cleaner than the affine reading
suggested.  **All three maps have the identical growth law.**  They differ only in
which additive shift makes a maximal odd run clean:

| map | shift `c` | block law |
|---|---|---|
| Collatz `T` | `+1` | `T^a (2^a·w − 1) = 3^a·w − 1` |
| mirror `3n−1` | `−1` | `M^a (2^a·w + 1) = 3^a·w + 1` |
| `expStep` | `0` | `E^a (2^a·w) = 3^a·w` |

Uniformly: **`F^a (2^a·w − c) = 3^a·w − c`** with `c = +1, −1, 0`.  Read down the
last column: the map `2^a·w ↦ 3^a·w` is *the same in all three rows*.  The three
maps are one growth law seen in the three coordinates `u = n + 1`, `n − 1`, `n`.

## Why this is the two filters at once

* **F2** (the sign of the `+1`) separates rows 1 and 2, which have the *same*
  block law and differ only in the sign of `c`.  The mirror has the cycle
  `5 → 7 → 10 → 5`; Collatz on the positives is conjectured to have only the
  trivial one.  So on this reading the entire difference between "has cycles" and
  "conjecturally has none" is a sign.
* **F1** (even steps divide) separates row 3, where `c = 0` degenerates the
  coordinate change to the identity — which is exactly why `expStep` grows from
  every start (`CoordinateMismatch.expStep_grows`) and satisfies every device that
  reads only odd inputs (`expStep_eq_on_odd`).

## What it does not do

It proves no bound.  `RealizableFrontier6809.length_ge_6809` is unchanged.  Its
value is diagnostic and it is sharp about the diagnosis: **any device whose
statement survives replacing `−1` by `+1` or by `0` in the display above cannot
distinguish Collatz from a map with a cycle, or from a map that diverges
everywhere.**  That is a concrete, checkable soundness test, and it is the reason
so many candidate devices in this development died — each was blind to `c`.

Every statement below is kernel-proved for **all** `w`, with no oddness hypothesis.
-/

namespace Collatz
namespace ShiftTrichotomy

/-! ## Row 1 — Collatz, shift `+1` -/

/-- **Collatz's block law.**  A maximal odd run of length `a` starting at
`2^a·w − 1` ends at `3^a·w − 1`: in the coordinate `u = n + 1` it is `u ↦ 3^a·w`.
This is `ValuationExchange.exchange_orbit` at `k = i = a`, `j = 0`. -/
theorem collatz_block (a w : Nat) :
    acceleratedOrbit a (2 ^ a * w - 1) = 3 ^ a * w - 1 := by
  have h := ValuationExchange.exchange_orbit a a 0 w (Nat.le_refl a)
  simpa using h

/-! ## Row 2 — the mirror `3n − 1`, shift `−1` -/

/-- **The mirror's block law.**  `M^a (2^a·w + 1) = 3^a·w + 1`: in the coordinate
`u = n − 1` it is the *same* map `2^a·w ↦ 3^a·w` as Collatz's.  Note the run is
automatically all-odd — `2^a·w + 1` is odd for every `a ≥ 1` and every `w` — so
no hypothesis on `w` is needed. -/
theorem mirror_block : ∀ (a w : Nat), Mirror.mirrorOrbit a (2 ^ a * w + 1) = 3 ^ a * w + 1 := by
  intro a
  induction a with
  | zero => intro w; simp [Mirror.mirrorOrbit]
  | succ a ih =>
    intro w
    have hpow : 2 ^ (a + 1) * w = 2 * (2 ^ a * w) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    have hodd : ¬ ((2 ^ (a + 1) * w + 1) % 2 = 0) := by omega
    have hstep : Mirror.mirrorStep (2 ^ (a + 1) * w + 1) = 2 ^ a * (3 * w) + 1 := by
      rw [Mirror.mirrorStep, if_neg hodd, hpow]
      have hx : 2 ^ a * (3 * w) = 3 * (2 ^ a * w) := Nat.mul_left_comm _ _ _
      omega
    rw [Mirror.mirrorOrbit, hstep, ih (3 * w)]
    have h3 : (3 : Nat) ^ (a + 1) * w = 3 ^ a * (3 * w) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    omega

/-! ## Row 3 — the divergent twin, shift `0` -/

/-- **The twin's block law**, restated here for the table: `E^a (2^a·w) = 3^a·w`.
Same growth map, shift `0`.  Proved in `AffineCocycle.expStep_block`. -/
theorem exp_block (a w : Nat) :
    AffineCocycle.expOrbit a (2 ^ a * w) = 3 ^ a * w :=
  AffineCocycle.expStep_block a w

/-! ## The trichotomy -/

/-- **One growth law, three shifts.**  The three maps agree on `2^a·w ↦ 3^a·w`
and are distinguished exactly by the additive shift `c ∈ {+1, −1, 0}` in whose
coordinate the run is clean.  A device that cannot see `c` cannot tell Collatz
from a map with a cycle (the mirror) or from a map that diverges from every start
(`expStep`). -/
theorem trichotomy (a w : Nat) :
    acceleratedOrbit a (2 ^ a * w - 1) = 3 ^ a * w - 1
    ∧ Mirror.mirrorOrbit a (2 ^ a * w + 1) = 3 ^ a * w + 1
    ∧ AffineCocycle.expOrbit a (2 ^ a * w) = 3 ^ a * w :=
  ⟨collatz_block a w, mirror_block a w, exp_block a w⟩

/-- The mirror really does have the nontrivial cycle `5 → 7 → 10 → 5`, so row 2
is not an idle alternative: it is a map satisfying the same growth law for which
the conjecture is **false**. -/
theorem mirror_has_cycle : Mirror.mirrorOrbit 3 5 = 5 := by
  rfl

end ShiftTrichotomy
end Collatz
