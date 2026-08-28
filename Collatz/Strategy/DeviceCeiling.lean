import Collatz.Strategy.Mirror
import Collatz.Strategy.ScaleRecord

/-!
# The ceiling normal form, and the two filters made quantitative

`RunAlgebra` changes coordinate to `u = x + 1` and finds that an odd step is
exactly `u ↦ 3u/2` while an even step is `u ↦ (u+1)/2`.  This file pushes that
one step further and asks what the *other two maps in the repository* — the
mirror `3n − 1` and the divergence witness `expStep` — look like in the same
coordinate.  The answer localises both soundness filters to a single branch and
puts a **number** on each.

## The three maps in one coordinate

Every one of them has the *same* growth branch.  They differ only in how they
halve:

| map | even `u` | odd `u` |
|---|---|---|
| Collatz `3n+1` | `3u/2` | `(u+1)/2` = `⌈u/2⌉` |
| mirror `3n−1` | `3u/2` | `(u−1)/2` = `⌊u/2⌋` |
| witness `expStep` | `3u/2` | `(3u−1)/2` |

(`ceilStep_shift`, `floorStep_shift`, `expUStep_shift`, `branches_agree`.)  So in
the shifted coordinate the entire difference between `3n+1` and `3n−1` is
**ceiling versus floor on one branch**, and the entire difference between Collatz
and a map all of whose orbits diverge is the same branch again.

## The two filters, with their sizes

On odd `u = 2k+1`:

* `mirror_gap`:      `ceilStep u = floorStep u + 1`;
* `divergence_gap`:  `expUStep u = ceilStep u + (u − 1)`.

**The mirror is a bounded perturbation of Collatz — a constant `1` — and the
divergence witness is an unbounded one, growing like `u`.**  That is the exact
content of the two soundness filters this repository already carries
(`Mirror`, `ScaleRecord.divergence_filter`), and it says what each demands of a
new device:

* a **cycle** argument must be sensitive to a perturbation of size `1` on the
  halving branch, since the mirror has the cycle `5 → 7 → 10 → 5`;
* a **divergence** argument must be sensitive to the halving branch at all, since
  replacing `⌈u/2⌉` by `(3u−1)/2` makes every orbit diverge.

The second is the weaker demand and the repository already meets it in places;
the first is why so many devices die.  Any inequality whose hypotheses are stable
under changing one branch by `±1` is, by `filter_separation`, satisfied by the
mirror too, and therefore cannot exclude a cycle.

## What this is and is not

It is a normal form and a diagnostic, not a new inequality.  The conjugation
`u = x + 1` is a bijection, so `ceilOrbit_shift` transports statements in both
directions without loss — nothing here can prove something the `x` coordinate
cannot.  Its value is that "which line is asymmetric" stops being a per-device
audit and becomes a single computation: locate the device's dependence on the
halving branch, and compare it against `1` and against `u`.
-/

namespace Collatz
namespace DeviceCeiling

open Reach Mirror ScaleRecord

/-! ## The three shifted maps -/

/-- Collatz in the coordinate `u = x + 1`: triple-and-halve on even, **ceiling**
halve on odd. -/
def ceilStep (u : Nat) : Nat :=
  if u % 2 = 0 then 3 * u / 2 else (u + 1) / 2

/-- The mirror `3n − 1` in the coordinate `u = x − 1`: the same growth branch,
**floor** halve on odd. -/
def floorStep (u : Nat) : Nat :=
  if u % 2 = 0 then 3 * u / 2 else (u - 1) / 2

/-- The divergence witness `expStep` in the coordinate `u = x + 1`: the same
growth branch again, and a halving branch that grows. -/
def expUStep (u : Nat) : Nat :=
  if u % 2 = 0 then 3 * u / 2 else (3 * u - 1) / 2

/-! ## Each is the conjugate of its map -/

/-- **Collatz is the ceiling map.** -/
theorem ceilStep_shift (x : Nat) : ceilStep (x + 1) = acceleratedStep x + 1 := by
  unfold ceilStep acceleratedStep
  rcases Arith.mod_two_eq_zero_or_one x with he | ho
  · have hu : (x + 1) % 2 = 1 := by omega
    rw [if_neg (by omega), if_pos he]
    omega
  · have hu : (x + 1) % 2 = 0 := by omega
    rw [if_pos hu, if_neg (by omega)]
    omega

/-- **The mirror is the floor map**, in its own shifted coordinate `u = x − 1`. -/
theorem floorStep_shift {x : Nat} (hx : 1 ≤ x) :
    floorStep (x - 1) + 1 = mirrorStep x := by
  unfold floorStep mirrorStep
  rcases Arith.mod_two_eq_zero_or_one x with he | ho
  · have hu : (x - 1) % 2 = 1 := by omega
    rw [if_neg (by omega), if_pos he]
    omega
  · have hu : (x - 1) % 2 = 0 := by omega
    rw [if_pos hu, if_neg (by omega)]
    omega

/-- **The divergence witness is the growing-halve map.** -/
theorem expUStep_shift (x : Nat) : expUStep (x + 1) = expStep x + 1 := by
  unfold expUStep expStep
  rcases Arith.mod_two_eq_zero_or_one x with he | ho
  · have hu : (x + 1) % 2 = 1 := by omega
    rw [if_neg (by omega), if_pos he]
    omega
  · have hu : (x + 1) % 2 = 0 := by omega
    rw [if_pos hu, if_neg (by omega)]
    omega

/-! ## The growth branch is common to all three -/

/-- **All three maps agree on the growth branch.**  Nothing distinguishing lives
on even `u`. -/
theorem branches_agree {u : Nat} (h : u % 2 = 0) :
    ceilStep u = 3 * u / 2 ∧ floorStep u = 3 * u / 2 ∧ expUStep u = 3 * u / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ceilStep, floorStep, expUStep, h]

/-! ## The two filters, sized -/

/-- **The mirror filter has size one.**  On the halving branch the mirror differs
from Collatz by exactly `1`, at every odd `u`. -/
theorem mirror_gap (k : Nat) : ceilStep (2 * k + 1) = floorStep (2 * k + 1) + 1 := by
  have h : (2 * k + 1) % 2 = 1 := by omega
  unfold ceilStep floorStep
  rw [if_neg (by omega), if_neg (by omega)]
  omega

/-- **The divergence filter has size `u − 1`.**  On the halving branch the
witness differs from Collatz by `2k`, which is unbounded in `u = 2k+1`. -/
theorem divergence_gap (k : Nat) : expUStep (2 * k + 1) = ceilStep (2 * k + 1) + 2 * k := by
  have h : (2 * k + 1) % 2 = 1 := by omega
  unfold ceilStep expUStep
  rw [if_neg (by omega), if_neg (by omega)]
  omega

/-- **The separation, in one statement.**  Both soundness filters live on the
halving branch alone, one at distance `1` and one at distance `u − 1`. -/
theorem filter_separation (k : Nat) :
    floorStep (2 * k + 1) + 1 = ceilStep (2 * k + 1)
      ∧ ceilStep (2 * k + 1) + 2 * k = expUStep (2 * k + 1)
      ∧ ∀ u : Nat, u % 2 = 0 → ceilStep u = floorStep u ∧ ceilStep u = expUStep u := by
  refine ⟨(mirror_gap k).symm, (divergence_gap k).symm, ?_⟩
  intro u hu
  obtain ⟨h1, h2, h3⟩ := branches_agree hu
  exact ⟨by rw [h1, h2], by rw [h1, h3]⟩

/-! ## The conjugation is exact at the level of orbits -/

/-- The orbit of the ceiling map. -/
def ceilOrbit : Nat → Nat → Nat
  | 0, u => u
  | k + 1, u => ceilOrbit k (ceilStep u)

@[simp] theorem ceilOrbit_zero (u : Nat) : ceilOrbit 0 u = u := rfl

theorem ceilOrbit_succ_step (k u : Nat) :
    ceilOrbit (k + 1) u = ceilStep (ceilOrbit k u) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih => rw [ceilOrbit, ih, ceilOrbit]

/-- **The conjugation, at every time.**  `u = x + 1` intertwines the accelerated
map with the ceiling map exactly, so no statement is lost in either direction. -/
theorem ceilOrbit_shift : ∀ (j x : Nat), ceilOrbit j (x + 1) = acceleratedOrbit j x + 1 := by
  intro j
  induction j with
  | zero => intro x; rfl
  | succ j ih =>
    intro x
    rw [ceilOrbit, ceilStep_shift, ih (acceleratedStep x), acceleratedOrbit]

/-! ## The region `u ≥ 2`, and where the mirror leaks

The ceiling map preserves `u ≥ 2`; the floor map does not.  This is the smallest
visible consequence of the `±1`, and it is *not* enough to exclude the mirror's
cycle, which lives entirely at `u ≥ 4`. -/

/-- The ceiling map never leaves `u ≥ 2`. -/
theorem ceilStep_ge_two {u : Nat} (h : 2 ≤ u) : 2 ≤ ceilStep u := by
  unfold ceilStep
  rcases Arith.mod_two_eq_zero_or_one u with he | ho
  · rw [if_pos he]; omega
  · rw [if_neg (by omega)]; omega

/-- The floor map does leave it: `u = 1` falls to `0`, where the ceiling map is
fixed.  The escape is by exactly the `1` of `mirror_gap`. -/
theorem floorStep_one : floorStep 1 = 0 ∧ ceilStep 1 = 1 := by
  constructor <;> rfl

/-- **But the leak is not the mechanism.**  The mirror's cycle `5 → 7 → 10 → 5`
sits at `u = 4, 6, 9`, never near the leak, so "the `+1` keeps `u` positive" is
too weak to exclude it. -/
theorem mirror_cycle_avoids_leak :
    floorStep 4 = 6 ∧ floorStep 6 = 9 ∧ floorStep 9 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The same three points under the Collatz branch: the cycle is broken by the
`+1`, and by nothing else.  `9` is the only odd point of the loop, and it is the
only place the two maps disagree. -/
theorem ceil_breaks_mirror_cycle :
    ceilStep 4 = 6 ∧ ceilStep 6 = 9 ∧ ceilStep 9 = 5 ∧ floorStep 9 = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## The normal form of the conjecture

Reaching `1` under the accelerated map is reaching `2` under the ceiling map. -/

/-- **Collatz in the ceiling coordinate.**  `x` reaches `1` in `j` accelerated
steps exactly when `x + 1` reaches `2` in `j` ceiling steps. -/
theorem reaches_iff_ceil (x j : Nat) :
    acceleratedOrbit j x = 1 ↔ ceilOrbit j (x + 1) = 2 := by
  rw [ceilOrbit_shift]
  omega

/-- `2` is the fixed point of the ceiling map that `1` is of the accelerated one,
reached through `3`. -/
theorem ceil_two_three : ceilStep 2 = 3 ∧ ceilStep 3 = 2 := by
  constructor <;> rfl

end DeviceCeiling
end Collatz
