import Collatz.Strategy.PosBridge

/-!
# The identity holds exactly on a semiconvergent staircase of `log₂ 3`

`PosBridge.hhMin_eq_Bcap` reduced the agreement between the Halbeisen–Hungerbühler
minimum and the `Bcap` realizable-frontier bound to the single arithmetic condition

`hpos a : ∀ i < a, pos (fexp a + 1) a i = fexp i`.

This file says exactly when `hpos` holds, and discharges it unconditionally at every
rung this development uses.

## The characterization

Computed for every `a` up to `~16000`, the holding set is

`1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306, 971, 1636, …, 4296, 4961, …, 15601`

and it is **not** an arithmetic progression — it is a **staircase** read off the
continued fraction of `log₂ 3 = [1; 1,1,2,2,3,1,5,2,23,2,2,1,1,55,…]`, whose
convergent denominators are

`q = 1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, 31867, …`

(the `485/306`, `1054/665`, `24727/15601` already named in `ExclusionRatio` and
`HHThreshold`).  `hpos` holds exactly on the one-sided semiconvergent chain through
the **odd-indexed** convergents: the rungs are `q₁, q₃, q₅, q₇, q₉ = 1, 5, 41, 306,
15601`, and between consecutive rungs one steps by the intervening **even-indexed**
denominator `q₂ₖ`, exactly `a₂ₖ₊₁` times — the next partial quotient:

| rung | step | times | reaching |
|---|---|---|---|
| `1` | `2` | `2` | `5` |
| `5` | `12` | `3` | `41` |
| `41` | `53` | `5` | `306` |
| `306` | `665` | `23` | `15601` |

**This explains the constant gap `665` that made the set look like a progression,
and why `665` itself fails**: `665 = q₈` is the even-index *step*, never a rung, and
the run of `23` steps of size `665` from `306` lands precisely on `q₉ = 15601`.  The
seven values `306, 971, …, 4296` this development had been quoting are just the
opening of that fourth stair.  Reconstructed independently here from the continued
fraction alone, matching the computed holding set term for term.

The `topIndex` off-by-one that has bitten this repo before (`topIndex` is exact only
for `L < 10 439 860 591`) is **not** in play: `fexp` is defined by exact recursive
power comparisons (`fexp_spec`), not by that rational approximation.

## What is and is not proved

Below, `hpos` is discharged by `decide` — genuine kernel reduction, no
`native_decide`, no added axioms — at the seven rungs already in use **and at
`4961`, the next rung on the chain**, giving unconditional `hhMin = Bcap` there.

A closed criterion for `hpos` at *every* `a` on the chain is **not** proved and is
not claimed.  It is a genuine Ostrowski-numeration / three-distance statement about
the rotation by `log₂ 3 mod 1` — why the Beatty word's cumulative one-count
synchronizes with `fexp`'s greedy floor precisely at one-sided semiconvergent
denominators and only there.  That is continued-fraction theory, not something to
force by induction in core Lean without Mathlib.

No new bound: `RealizableFrontier6809.length_ge_6809` is untouched.
-/

open Collatz Collatz.PosBridge Collatz.RealizableBound

namespace Collatz
namespace PosLadder

set_option maxRecDepth 4000000

/-! ## The seven rungs in use -/

theorem hpos_306 : ∀ i : Nat, i < 306 → pos (fexp 306 + 1) 306 i = fexp i := by decide

theorem hhMin_eq_Bcap_306 :
    HalbeisenHungerbuhler.hhMin (fexp 306 + 1) 306 (fexp 306 + 1) = Bcap 306 :=
  hhMin_eq_Bcap 306 hpos_306

theorem hpos_971 : ∀ i : Nat, i < 971 → pos (fexp 971 + 1) 971 i = fexp i := by decide

theorem hhMin_eq_Bcap_971 :
    HalbeisenHungerbuhler.hhMin (fexp 971 + 1) 971 (fexp 971 + 1) = Bcap 971 :=
  hhMin_eq_Bcap 971 hpos_971

theorem hpos_1636 : ∀ i : Nat, i < 1636 → pos (fexp 1636 + 1) 1636 i = fexp i := by decide

theorem hhMin_eq_Bcap_1636 :
    HalbeisenHungerbuhler.hhMin (fexp 1636 + 1) 1636 (fexp 1636 + 1) = Bcap 1636 :=
  hhMin_eq_Bcap 1636 hpos_1636

theorem hpos_2301 : ∀ i : Nat, i < 2301 → pos (fexp 2301 + 1) 2301 i = fexp i := by decide

theorem hhMin_eq_Bcap_2301 :
    HalbeisenHungerbuhler.hhMin (fexp 2301 + 1) 2301 (fexp 2301 + 1) = Bcap 2301 :=
  hhMin_eq_Bcap 2301 hpos_2301

theorem hpos_2966 : ∀ i : Nat, i < 2966 → pos (fexp 2966 + 1) 2966 i = fexp i := by decide

theorem hhMin_eq_Bcap_2966 :
    HalbeisenHungerbuhler.hhMin (fexp 2966 + 1) 2966 (fexp 2966 + 1) = Bcap 2966 :=
  hhMin_eq_Bcap 2966 hpos_2966

theorem hpos_3631 : ∀ i : Nat, i < 3631 → pos (fexp 3631 + 1) 3631 i = fexp i := by decide

theorem hhMin_eq_Bcap_3631 :
    HalbeisenHungerbuhler.hhMin (fexp 3631 + 1) 3631 (fexp 3631 + 1) = Bcap 3631 :=
  hhMin_eq_Bcap 3631 hpos_3631

theorem hpos_4296 : ∀ i : Nat, i < 4296 → pos (fexp 4296 + 1) 4296 i = fexp i := by decide

theorem hhMin_eq_Bcap_4296 :
    HalbeisenHungerbuhler.hhMin (fexp 4296 + 1) 4296 (fexp 4296 + 1) = Bcap 4296 :=
  hhMin_eq_Bcap 4296 hpos_4296

/-! ## The new rung, predicted from the continued fraction and then verified

`4961 = 306 + 665·7` sits on the fourth stair.  It was predicted by the
characterization above before being checked, and the check succeeds. -/

theorem hpos_4961 : ∀ i : Nat, i < 4961 → pos (fexp 4961 + 1) 4961 i = fexp i := by decide

theorem hhMin_eq_Bcap_4961 :
    HalbeisenHungerbuhler.hhMin (fexp 4961 + 1) 4961 (fexp 4961 + 1) = Bcap 4961 :=
  hhMin_eq_Bcap 4961 hpos_4961

end PosLadder
end Collatz
