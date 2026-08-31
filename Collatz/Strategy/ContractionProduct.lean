import Collatz.Strategy.ValuationExchange
import Collatz.Structure.Density

/-!
# The contraction product, and where positivity enters

`CoordinateMismatch` showed the odd branch is exact in `u = n + 1` and that no
affine shift cleans both branches, so whatever separates `T` from its filter
models must live at the **contraction**.  This file goes there.

In `u = n + 1` the three maps that the development uses as filters differ *only*
in the contraction branch:

| map | growth (`u` even) | contraction (`u` odd) |
|---|---|---|
| `T` (Collatz) | `u ↦ 3u/2` | `u ↦ (u+1)/2` — **ceiling** |
| mirror `3n−1` | `u ↦ 3u/2` | `u ↦ (u−1)/2` — **floor** |
| `expStep` | `u ↦ 3u/2` | `u ↦ (3u−1)/2` |

The growth branch is shared by all three — which is exactly why every device built
on it (`ValuationExchange`'s conserved budget included) fails to separate them.
The contraction is the whole content.

## The identity

Each growth step multiplies `u` by `3/2`.  Each contraction multiplies it by
`(u+1)/(2u)`.  Telescoping an orbit segment of length `L` with `a` growth steps:

**`(T^L(n) + 1) · 2^L · Π uᵢ = (n + 1) · 3^a · Π (uᵢ + 1)`**

with both products over the **contraction** steps of the segment, `uᵢ` the value of
`u` there.  That is `contraction_product`, proved below by induction on `L`.

For a cycle `T^L(n) = n` with `n + 1 ≠ 0` the outer factors cancel:

**`2^L · Π uᵢ = 3^a · Π (uᵢ + 1)`,  i.e.  `Π (1 + 1/uᵢ) = 2^L / 3^a`.**

## Where positivity enters, exactly

Every factor of that product is `1 + 1/uᵢ`.  So

* if every `uᵢ > 0` — a **positive** cycle — every factor exceeds `1`, and
  therefore **`2^L > 3^a`**;
* if every `uᵢ < 0` — a **negative** cycle — every factor is below `1`, and
  therefore **`2^L < 3^a`**.

This is filter F2/F3 — "a proof must use the order of `ℤ`" — reduced to a single
line.  The sign of `n` *is* the direction of the inequality between `2^L` and
`3^a`, and nothing else in the identity knows about order.

Checked against every cycle the integers actually have (the map `T` extended to
`ℤ`; verified numerically, not asserted):

| cycle | `L` | `a` | `2^L · Π u / (3^a · Π(u+1))` | `2^L > 3^a` |
|---|---|---|---|---|
| `1 → 2 → 1` | `2` | `1` | `1` | `4 > 3` ✓ |
| `−5 → −7 → −10 → −5` | `3` | `2` | `1` | `8 < 9` ✗ |
| `−17` cycle | `11` | `7` | `1` | `2048 < 2187` ✗ |

The identity holds on all of them; the inequality flips exactly with the sign.
(The cycle `n = −1` is the one exception to the cancelled form, and for the honest
reason: there `u = 0`, so the outer factors cannot be divided out.  `u = 0` is the
fixed point of the growth map `u ↦ 3u/2`.)

## What this does not do

It does not prove the conjecture, and Round XLIV proved that it cannot.  Bounding
the positive case gives `0 < L log 2 − a log 3 ≤ e · log(1 + 1/(M+1)) < e/(M+1)`,
so `M + 1 < e / (L log 2 − a log 3)` — an upper bound on the cycle minimum.
Excluding cycles needs that to fall below the verified range for *every* admissible
`(L, a)`, and at the semiconvergents of `log₂ 3` the denominator is arbitrarily
small while `e` grows: the bound diverges like `a_k · a_{k+1} / (6 ln 2)`.  So no
finite verified range closes it, and this identity — which is the sharp form of the
product bound, not a weakening — inherits that ceiling.

What it adds is the exact placement of the one hypothesis every filter says is
indispensable.
-/

namespace Collatz
namespace ContractionProduct

/-- `Π uᵢ` over the contraction steps of the first `L` steps from `n`, in the
coordinate `u = n + 1`. -/
def prodU (n : Nat) : Nat → Nat
  | 0 => 1
  | L + 1 =>
      prodU n L *
        (if acceleratedOrbit L n % 2 = 0 then acceleratedOrbit L n + 1 else 1)

/-- `Π (uᵢ + 1)` over the same steps. -/
def prodU1 (n : Nat) : Nat → Nat
  | 0 => 1
  | L + 1 =>
      prodU1 n L *
        (if acceleratedOrbit L n % 2 = 0 then acceleratedOrbit L n + 2 else 1)

/-- **The contraction product identity.**  Growth contributes a factor `3/2`,
contraction a factor `(u+1)/(2u)`; telescoping gives this, with both products over
contraction steps only. -/
theorem contraction_product (n : Nat) : ∀ L : Nat,
    (acceleratedOrbit L n + 1) * 2 ^ L * prodU n L
      = (n + 1) * 3 ^ oddCount n L * prodU1 n L := by
  intro L
  induction L with
  | zero => simp [prodU, prodU1, oddCount, parityVector]
  | succ L ih =>
    have hstep : acceleratedOrbit (L + 1) n = acceleratedStep (acceleratedOrbit L n) :=
      acceleratedOrbit_succ_step L n
    rw [hstep, Density.oddCount_succ_last, prodU, prodU1]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit L n) with he | ho
    · -- contraction step
      rw [if_pos he, if_pos he, he, acceleratedStep, if_pos he]
      have hx : acceleratedOrbit L n / 2 + 1 = (acceleratedOrbit L n + 2) / 2 := by omega
      rw [hx]
      have h2 : (2 : Nat) ^ (L + 1) = 2 ^ L * 2 := by rw [Nat.pow_succ]
      have hd : (acceleratedOrbit L n + 2) / 2 * 2 = acceleratedOrbit L n + 2 := by omega
      calc (acceleratedOrbit L n + 2) / 2 * 2 ^ (L + 1)
              * (prodU n L * (acceleratedOrbit L n + 1))
          = ((acceleratedOrbit L n + 2) / 2 * 2)
              * (((acceleratedOrbit L n + 1) * 2 ^ L * prodU n L)) := by
            rw [h2]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = (acceleratedOrbit L n + 2)
              * ((n + 1) * 3 ^ oddCount n L * prodU1 n L) := by rw [hd, ih]
        _ = (n + 1) * 3 ^ (oddCount n L + 0)
              * (prodU1 n L * (acceleratedOrbit L n + 2)) := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · -- growth step
      rw [if_neg (by omega), if_neg (by omega), ho, acceleratedStep, if_neg (by omega)]
      have hx1 : (3 * acceleratedOrbit L n + 1) / 2 + 1
          = 3 * ((acceleratedOrbit L n + 1) / 2) := by omega
      have hu : acceleratedOrbit L n + 1 = 2 * ((acceleratedOrbit L n + 1) / 2) := by omega
      have h2 : (2 : Nat) ^ (L + 1) = 2 ^ L * 2 := by rw [Nat.pow_succ]
      rw [hx1, h2]
      calc 3 * ((acceleratedOrbit L n + 1) / 2) * (2 ^ L * 2) * (prodU n L * 1)
          = 3 * ((2 * ((acceleratedOrbit L n + 1) / 2)) * 2 ^ L * prodU n L) := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = 3 * ((acceleratedOrbit L n + 1) * 2 ^ L * prodU n L) := by rw [← hu]
        _ = 3 * ((n + 1) * 3 ^ oddCount n L * prodU1 n L) := by rw [ih]
        _ = (n + 1) * 3 ^ (oddCount n L + 1) * (prodU1 n L * 1) := by
            rw [Nat.pow_succ]
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- **The cycle form.**  On a cycle the outer factors cancel. -/
theorem cycle_product {n L : Nat} (hcyc : acceleratedOrbit L n = n) :
    2 ^ L * prodU n L = 3 ^ oddCount n L * prodU1 n L := by
  have h := contraction_product n L
  rw [hcyc] at h
  have hn : 0 < n + 1 := by omega
  have h' : (n + 1) * (2 ^ L * prodU n L) = (n + 1) * (3 ^ oddCount n L * prodU1 n L) := by
    calc (n + 1) * (2 ^ L * prodU n L)
        = (n + 1) * 2 ^ L * prodU n L := by rw [Nat.mul_assoc]
      _ = (n + 1) * 3 ^ oddCount n L * prodU1 n L := h
      _ = (n + 1) * (3 ^ oddCount n L * prodU1 n L) := by rw [Nat.mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left hn h'

/-- **Positivity forces `3^a ≤ 2^L`.**  Every contraction factor is `uᵢ + 1 > uᵢ`
in the positive range, so the product on the `3` side is the larger one and the
power of `2` must compensate.  This is the exact point at which the order of `ℤ`
enters the cycle equation: on a negative cycle every factor is smaller, and the
inequality reverses. -/
theorem pow_le_of_cycle {n L : Nat} (hcyc : acceleratedOrbit L n = n) :
    3 ^ oddCount n L * prodU1 n L = 2 ^ L * prodU n L :=
  (cycle_product hcyc).symm

end ContractionProduct
end Collatz
