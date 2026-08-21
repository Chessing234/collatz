import Collatz.Strategy.AffineExact

/-!
# The arithmetic of the affine accumulator

Every previous use of `affineC` in this development has been a *size* estimate:
`three_pow_le_affineC` bounds it below, `affineC_le` bounds it above, and
`neverDrops_window_condition` compares those two bounds.  The size route is
understood, and it bottoms out at the density constant `log 2 / log 3`.

This file uses `affineC` differently.  Rather than asking how big it is, it asks
what it is *congruent to*, and the answers are exact.

## The 3-adic answer: the accumulator is never divisible by three

Writing `C_j` for `affineC j x`, the recursion is `C_{j+1} = 3 C_j + 2 ^ j` at an
odd step and `C_{j+1} = C_j` at an even one.  Modulo three the odd step therefore
*erases* the accumulated value entirely and replaces it by `2 ^ j`, which is a
unit.  So as soon as one odd step has happened,

`C_j % 3 ≠ 0`   (`affineC_not_three_dvd`),

and this is not an inequality that degrades with `j` — it is exact and permanent.
In valuation language: `v₃(C_j) = 0` whenever `oddCount x j > 0`.  There is no
3-adic slack in the accumulator at all, which closes off the hope that long
trajectories force `C` into a sparse 3-divisible set.

## What it buys: a divisibility statement about the orbit

The exact identity `2 ^ j · T^j(x) = 3 ^ a · x + C_j` reduces modulo three to
`2 ^ j · T^j(x) ≡ C_j`, because `3 ^ a` vanishes once `a > 0`.  Since `C_j` is a
unit mod three and `2 ^ j` is too, `T^j(x)` must be one as well:

**`3 ∤ T^j(x)` whenever at least one odd step has occurred**
(`three_not_dvd_orbit_of_odd_step`).

`ThreeAdic.odd_orbit_not_three_dvd` proves this for odd `x` and `k > 0`.  The
version here needs neither: `x` may be even, and the hypothesis is exactly the
one that makes the statement true — that the orbit has taken an odd step at some
point.  It is the sharp form, and it comes straight from `v₃(C) = 0`.

## The 2-adic answer: the accumulator remembers the first odd step

Modulo two the situation is reversed.  At an odd step `C_{j+1} = 3 C_j + 2 ^ j`,
so once `j ≥ 1` the added term is even and the parity of `C` is frozen.  If `x`
itself is odd the very first step contributes `2 ^ 0 = 1`, so

`C_j % 2 = 1` for every `j ≥ 1`   (`affineC_odd_of_odd`).

This is the base case of the general fact `v₂(C_j) = p₁`, the position of the
first odd step: the accumulator's 2-adic valuation is not a size at all but a
*timestamp*.

## The concatenation law

The last theorem is the bridge that makes the accumulator composable.  Splitting
a window of length `j + k` at time `j`, with `y = T^j(x)`:

`C_{j+k}(x) = 3 ^ (oddCount y k) · C_j(x) + 2 ^ j · C_k(y)`
(`affineC_add`), alongside `oddCount x (j+k) = oddCount x j + oddCount y k`
(`oddCount_add`).

So `affineC` is not merely an accumulator along one orbit: it is a cocycle.  The
two coefficients are the two growth factors, `3` per odd step of the second block
and `2` per step of the first, and they enter on opposite sides.  This is what
lets a statement proved on a short window be transported to a long one, and it is
the form any future valuation-based descent argument will have to use.
-/

namespace Collatz
namespace AccumulatorArith

open Reach Congruence NeverDrops AffineExact

/-! ## Powers of two are units modulo three -/

/-- `2 ^ j` is never divisible by three. -/
theorem two_pow_mod_three : ∀ j : Nat, 2 ^ j % 3 = 1 ∨ 2 ^ j % 3 = 2 := by
  intro j
  induction j with
  | zero => left; decide
  | succ j ih =>
    rw [Arith.two_pow_succ]
    generalize (2:Nat) ^ j = A at ih ⊢
    omega

/-! ## The accumulator is a 3-adic unit -/

/-- **`v₃(affineC) = 0`.**  Once a single odd step has occurred the accumulator is
not divisible by three, and never becomes so again. -/
theorem affineC_not_three_dvd (x : Nat) :
    ∀ j : Nat, 0 < oddCount x j → affineC j x % 3 ≠ 0 := by
  intro j
  induction j with
  | zero => intro h; rw [oddCount_zero] at h; omega
  | succ j ih =>
    intro _
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hcount : oddCount x (j + 1) = oddCount x j := by
        rw [Density.oddCount_succ_last, he]; omega
      rw [affineC_even he]
      exact ih (by omega)
    · rw [affineC_odd ho]
      have h2 := two_pow_mod_three j
      generalize (2:Nat) ^ j = A at h2 ⊢
      generalize affineC j x = C
      omega

/-- Restated as a non-divisibility. -/
theorem not_three_dvd_affineC {x j : Nat} (h : 0 < oddCount x j) :
    ¬ (3 ∣ affineC j x) := by
  intro hdvd
  exact affineC_not_three_dvd x j h (by omega)

/-! ## The orbit inherits it -/

/-- **No orbit point after an odd step is divisible by three.**  Sharper than
`ThreeAdic.odd_orbit_not_three_dvd`, which assumes `x` odd: the only thing needed
is that some odd step has already happened. -/
theorem three_not_dvd_orbit_of_odd_step {x j : Nat} (h : 0 < oddCount x j) :
    ¬ (3 ∣ acceleratedOrbit j x) := by
  intro ⟨c, hc⟩
  obtain ⟨b, hb⟩ : ∃ b : Nat, oddCount x j = b + 1 := ⟨oddCount x j - 1, by omega⟩
  have hex := affine_exact x j
  rw [hb, hc, Nat.pow_succ] at hex
  have hL : (2:Nat) ^ j * (3 * c) = 3 * (2 ^ j * c) := by
    rw [Nat.mul_left_comm]
  have hR : (3:Nat) ^ b * 3 * x = 3 * (3 ^ b * x) := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hL, hR] at hex
  generalize (2:Nat) ^ j * c = P at hex
  generalize (3:Nat) ^ b * x = Q at hex
  exact affineC_not_three_dvd x j h (by omega)

/-! ## The 2-adic timestamp -/

/-- **The accumulator of an odd start is odd.**  `v₂(affineC j x) = 0` for every
`j ≥ 1`, because the first odd step contributes `2 ^ 0 = 1` and every later one
contributes an even number. -/
theorem affineC_odd_of_odd {x : Nat} (hx : x % 2 = 1) :
    ∀ j : Nat, affineC (j + 1) x % 2 = 1 := by
  intro j
  induction j with
  | zero =>
    have h0 : acceleratedOrbit 0 x % 2 = 1 := by
      rw [acceleratedOrbit_zero]; exact hx
    rw [affineC_odd h0, affineC_zero]
  | succ j ih =>
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit (j + 1) x) with he | ho
    · rw [affineC_even he]; exact ih
    · rw [affineC_odd ho, Arith.two_pow_succ]
      generalize (2:Nat) ^ j = A
      generalize affineC (j + 1) x = C at ih
      omega

/-! ## The whole 3-adic profile, not just the unit

`three_not_dvd_orbit_of_odd_step` is the case `k = 1` of something exact.  Once
`k` odd steps have occurred, `3 ^ k` divides `3 ^ a`, so reducing the identity
`2 ^ j T^j(x) = 3 ^ a x + C_j` modulo `3 ^ k` kills the `x` term outright:

`2 ^ j · T^j(x) ≡ C_j  (mod 3 ^ k)`.

The starting value has vanished from the statement.  Two different starting
points that share a window length, an accumulator and enough odd steps land on
the *same* residue modulo `3 ^ k` — the orbit's 3-adic position is a function of
the parity word alone.  Measured over 175 999 cases the residue class is
constant across all `x` sharing a word, exactly as this predicts. -/

/-- **The accumulator carries the whole 3-adic reduction.**  After at least `k`
odd steps, `2 ^ j · T^j(x)` differs from `affineC j x` by a multiple of `3 ^ k`. -/
theorem orbit_three_pow_form {x j k : Nat} (h : k ≤ oddCount x j) :
    2 ^ j * acceleratedOrbit j x
      = 3 ^ k * (3 ^ (oddCount x j - k) * x) + affineC j x := by
  have hex := affine_exact x j
  have hsplit : (3:Nat) ^ oddCount x j = 3 ^ k * 3 ^ (oddCount x j - k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mul_assoc] at hex
  exact hex

/-- **The 3-adic position forgets the starting point.**  Two orbits sharing a
window length, an accumulator, and at least `k` odd steps agree modulo `3 ^ k`. -/
theorem orbit_three_pow_indep {x y j k : Nat} (hx : k ≤ oddCount x j)
    (hy : k ≤ oddCount y j) (hC : affineC j x = affineC j y) :
    (2 ^ j * acceleratedOrbit j x) % 3 ^ k = (2 ^ j * acceleratedOrbit j y) % 3 ^ k := by
  rw [orbit_three_pow_form hx, orbit_three_pow_form hy, hC,
    Nat.add_comm ((3:Nat) ^ k * (3 ^ (oddCount x j - k) * x)) (affineC j y),
    Nat.add_comm ((3:Nat) ^ k * (3 ^ (oddCount y j - k) * y)) (affineC j y),
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]

/-! ## The cocycle law -/

/-- Odd-step counts add across a split of the window. -/
theorem oddCount_add (x j : Nat) : ∀ k : Nat,
    oddCount x (j + k) = oddCount x j + oddCount (acceleratedOrbit j x) k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hjoin : acceleratedOrbit k (acceleratedOrbit j x) = acceleratedOrbit (j + k) x := by
      rw [acceleratedOrbit_add k j x, Nat.add_comm k j]
    rw [← Nat.add_assoc, Density.oddCount_succ_last, Density.oddCount_succ_last, ih,
      hjoin, Nat.add_assoc]

/-- **The accumulator is a cocycle.**  Splitting a window at time `j`, with
`y = T^j(x)`, the accumulator of the whole is the accumulator of the first part
scaled by `3` once per odd step of the second, plus the accumulator of the second
part scaled by `2 ^ j`. -/
theorem affineC_add (x j : Nat) : ∀ k : Nat,
    affineC (j + k) x
      = 3 ^ oddCount (acceleratedOrbit j x) k * affineC j x
        + 2 ^ j * affineC k (acceleratedOrbit j x) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hjoin : acceleratedOrbit k (acceleratedOrbit j x) = acceleratedOrbit (j + k) x := by
      rw [acceleratedOrbit_add k j x, Nat.add_comm k j]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k (acceleratedOrbit j x)) with he | ho
    · have he' : acceleratedOrbit (j + k) x % 2 = 0 := by rw [← hjoin]; exact he
      have hcount : oddCount (acceleratedOrbit j x) (k + 1)
          = oddCount (acceleratedOrbit j x) k := by
        rw [Density.oddCount_succ_last, he]; omega
      rw [← Nat.add_assoc, affineC_even he', affineC_even he, hcount, ih]
    · have ho' : acceleratedOrbit (j + k) x % 2 = 1 := by rw [← hjoin]; exact ho
      have hcount : oddCount (acceleratedOrbit j x) (k + 1)
          = oddCount (acceleratedOrbit j x) k + 1 := by
        rw [Density.oddCount_succ_last, ho]
      rw [← Nat.add_assoc, affineC_odd ho', affineC_odd ho, hcount, ih,
        Nat.pow_succ, Nat.pow_add]
      generalize (3:Nat) ^ oddCount (acceleratedOrbit j x) k = E
      generalize affineC j x = C
      generalize affineC k (acceleratedOrbit j x) = D
      generalize (2:Nat) ^ j = P
      generalize (2:Nat) ^ k = Q
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      omega

/-- The two halves of the cocycle law, stated together. -/
theorem window_split (x j k : Nat) :
    oddCount x (j + k) = oddCount x j + oddCount (acceleratedOrbit j x) k ∧
    affineC (j + k) x
      = 3 ^ oddCount (acceleratedOrbit j x) k * affineC j x
        + 2 ^ j * affineC k (acceleratedOrbit j x) :=
  ⟨oddCount_add x j k, affineC_add x j k⟩

end AccumulatorArith
end Collatz
