import Collatz.Strategy.StairGap
import Collatz.Structure.Cycle

/-!
# The cycle equation against the staircase gap

`Strategy.StairGap` and `Strategy.StairLower` control
`gapAt a = 2 ^ (fexp a + 1) − 3 ^ a` *exactly*, by recurrences with no
approximation anywhere.  The cycle equation is

    m · (2 ^ E − 3 ^ a)  =  Q,        `a = oddCount m E`, `Q = affineC E m`,

so `2 ^ E − 3 ^ a` is the same kind of object.  This file connects them, and
then reports what the connection is worth.

## The bridge

A cycle is necessarily **light** — `Cycle.two_pow_gt_three_pow_of_accCycle`
gives `3 ^ a < 2 ^ E` — so `E` is past the Beatty exponent (`fexp_lt_of_light`)
and therefore

    gapAt a  ≤  2 ^ E − 3 ^ a                              (`gapAt_le_of_light`)

with `gapAt a` the *smallest* value the cycle gap can take for that odd count.
Feeding that into the cycle equation:

    m · gapAt a  ≤  Q                                       (`cycle_min_gap_le`)

unconditionally — no verified range, no certificate, no hypothesis beyond being
a cycle.

## What it is worth, stated honestly

**It does not strengthen the frontier.**  Rearranged, the bridge caps the cycle
minimum by `m ≤ Q / gapAt a`, and turning that into a number needs an upper
bound on `Q`.  The only one available is `RealizableBound.affineC_le_Bcap`, which
*is* the certificate — so the chain reproduces the frontier argument in closed
form (`CertClosedForm`, Round LXXV.21) and stops in the same place.

The useful content is where it stops.  The binding constraint on the cycle side
is the bound on `Q`, **not** the gap: `gapAt a` is now known exactly and
contributes no slack, while `Q ≤ Bcap a` is an estimate over all admissible
words that ignores which word the cycle actually has.  Sharpening `2 ^ E − 3 ^ a`
further therefore buys nothing, and future effort on this side belongs on `Q`.

That is a redirection, not a theorem about cycles.  Recording it because three
rounds of exact gap machinery made the gap look like the promising object, and
it is not.
-/

namespace Collatz
namespace CycleGapBridge

open RealizableBound StairGap AffineExact

/-- A light window is past the Beatty exponent. -/
theorem fexp_lt_of_light {a E : Nat} (h : 3 ^ a < 2 ^ E) : fexp a < E := by
  rcases Nat.lt_or_ge (fexp a) E with hok | hcon
  · exact hok
  · exfalso
    have h1 : (2:Nat) ^ E ≤ 2 ^ fexp a := Arith.two_pow_le_two_pow hcon
    have h2 := fexp_le a
    omega

/-- **`gapAt a` is the least gap a light window can have.** -/
theorem gapAt_le_of_light {a E : Nat} (h : 3 ^ a < 2 ^ E) :
    gapAt a ≤ 2 ^ E - 3 ^ a := by
  have hlt := fexp_lt_of_light h
  have hsucc : (2:Nat) ^ (fexp a + 1) ≤ 2 ^ E := Arith.two_pow_le_two_pow (by omega)
  have hpow : (2:Nat) ^ (fexp a + 1) = 2 * 2 ^ fexp a := by
    rw [Nat.pow_succ]; omega
  unfold gapAt
  omega

/-- **The bridge.**  For any accelerated cycle, the minimum times the staircase
gap is at most the path sum.  Unconditional. -/
theorem cycle_min_gap_le {m E : Nat} (hpos : 0 < m) (hE : 0 < E)
    (hcyc : acceleratedOrbit E m = m) :
    m * gapAt (oddCount m E) ≤ affineC E m := by
  have hlight := Cycle.two_pow_gt_three_pow_of_accCycle hpos hE hcyc
  have hgap := gapAt_le_of_light hlight
  have hid := affine_exact m E
  rw [hcyc] at hid
  have hsub : m * (2 ^ E - 3 ^ oddCount m E) = m * 2 ^ E - m * 3 ^ oddCount m E :=
    Nat.mul_sub _ _ _
  have hc1 : (2:Nat) ^ E * m = m * 2 ^ E := Nat.mul_comm _ _
  have hc2 : (3:Nat) ^ oddCount m E * m = m * 3 ^ oddCount m E := Nat.mul_comm _ _
  have hmono : m * gapAt (oddCount m E) ≤ m * (2 ^ E - 3 ^ oddCount m E) :=
    Nat.mul_le_mul (Nat.le_refl m) hgap
  have hle : m * 3 ^ oddCount m E ≤ m * 2 ^ E :=
    Nat.mul_le_mul (Nat.le_refl m) (Nat.le_of_lt hlight)
  omega

/-- The cycle equation itself, in the form the bridge uses. -/
theorem cycle_equation {m E : Nat} (hpos : 0 < m) (hE : 0 < E)
    (hcyc : acceleratedOrbit E m = m) :
    m * (2 ^ E - 3 ^ oddCount m E) = affineC E m := by
  have hlight := Cycle.two_pow_gt_three_pow_of_accCycle hpos hE hcyc
  have hid := affine_exact m E
  rw [hcyc] at hid
  have hsub : m * (2 ^ E - 3 ^ oddCount m E) = m * 2 ^ E - m * 3 ^ oddCount m E :=
    Nat.mul_sub _ _ _
  have hc1 : (2:Nat) ^ E * m = m * 2 ^ E := Nat.mul_comm _ _
  have hc2 : (3:Nat) ^ oddCount m E * m = m * 3 ^ oddCount m E := Nat.mul_comm _ _
  have hle : m * 3 ^ oddCount m E ≤ m * 2 ^ E :=
    Nat.mul_le_mul (Nat.le_refl m) (Nat.le_of_lt hlight)
  omega

end CycleGapBridge
end Collatz
