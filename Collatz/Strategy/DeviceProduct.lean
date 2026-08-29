import Collatz.Strategy.DeviceSwap

/-!
# The product identity, and the one inequality that does separate ceiling from floor

Round XVIII closed with a target: *an inequality that is false for `⌊u/2⌋` and true
for `⌈u/2⌉`*.  This file produces one, in the swap coordinate, from a single
telescoping identity.

## The one-step law

For odd `y`, writing `s = v₂((y+1)/2)`,

`2 ^ (s+1) · nu y = 3 ^ s · (y + 1)`   (`nu_identity`),

and for the mirror map `mnu y = swap23 ((y−1)/2)`,

`2 ^ (s+1) · mnu y = 3 ^ s · (y − 1)`  (`mnu_identity`).

**The two laws differ in exactly one character.**  That character is the whole of
`DeviceCeiling.mirror_gap`, and it is the only place the two dynamics part.

## Telescoping

Multiplying the law along `B` steps and cancelling the shared product gives, for
a cycle `nu^B y = y` (`nu_cycle_product`),

`2 ^ (S + B) · ∏ yᵢ = 3 ^ S · ∏ (yᵢ + 1)`,  `S = s₁ + ⋯ + s_B`,

and for a mirror cycle (`mnu_cycle_product`),

`2 ^ (S + B) · ∏ yᵢ = 3 ^ S · ∏ (yᵢ − 1)`.

`S` is the accelerated odd-step count and `S + B` the accelerated length, so these
are the cycle relation in the coordinate where the even branch is the clock.

## The separation

`∏ (yᵢ + 1) > ∏ yᵢ` and `∏ (yᵢ − 1) < ∏ yᵢ`, both by the same trivial comparison.
Feeding each into its own identity:

* **`cycle_light`** — a Collatz cycle satisfies `3 ^ S < 2 ^ (S+B)`;
* **`mirror_cycle_heavy`** — a mirror cycle satisfies `2 ^ (S+B) < 3 ^ S`.

The two conclusions are *contradictory*.  This is the requested inequality: it
holds for `⌈u/2⌉`, its negation holds for `⌊u/2⌋`, and the proof consumes nothing
but the sign.  Witnesses check out — `three_cycle_light` (`3 < 4`) and
`nine_cycle_heavy` (`8 < 9`), the mirror's cycle `5 → 7 → 10 → 5`.

## Honest verdict — this is not new mathematics

The dichotomy is the classical one: a `3n+1` cycle is light, a `3n−1` cycle is
heavy, equivalently `a / L < log 2 / log 3` for the first and `>` for the second.
`CycleProduct` carries it already, in the dual form `∏ (3 + 1/nᵢ) = 2 ^ L` over the
*odd* elements; the identity here is the same relation taken over the *even*
elements instead.  What this file adds is where the dichotomy comes from: one
character in one law, isolated so that it cannot be mistaken for anything else.

**And it does not close the cycle half.**  Being light is a necessary condition
that the repository has had since Round IV; excluding a cycle needs a bound on
`L`, which is `CycleLength2593` and `length_ge_6809`, and those leave an infinite
admissible set.  Comparing the exponents the two bounds give:

* over the even elements (here): `2 ^ j / 3 ^ a ≤ (1 + 1/m) ^ (j−a)`;
* over the odd elements (`CycleProduct`): `2 ^ j / 3 ^ a ≤ (1 + 1/(3m)) ^ a`.

With `a ≈ 0.63 j` the second is smaller by a factor of about `1.75`, so the
identity proved here is the **weaker** of the two.  It is the better *explanation*
and the worse *bound*.

## Why the device stops here

`DeviceSwap.run_length_ledger` cannot be improved by asking which run-length
sequences are arithmetically realizable, because **all of them are**: every
sequence `(s₁, …, s_B)` over `{0,1,2}` is realized, checked exhaustively for
`B ≤ 4`.  That is the swap-coordinate form of the repository's parity-word
bijection, and it means the ledger is already extremal.  The remaining content is
the same wall as before: a light cycle needs `2 ^ j / 3 ^ a` within `O(1/m)` of
`1`, and separating that from `1` is a linear-forms-in-logarithms problem, not an
elementary one.
-/

namespace Collatz
namespace DeviceProduct

open Reach DeviceSwap

/-! ## The two-adic split, as a function -/

/-- Split `n = 2 ^ s · w` with `w` odd, using `fuel` to stay structurally
recursive.  Returns the pair `(s, w)`. -/
def splitAux : Nat → Nat → Nat × Nat
  | 0, n => (0, n)
  | fuel + 1, n =>
      if n % 2 = 0 then ((splitAux fuel (n / 2)).1 + 1, (splitAux fuel (n / 2)).2)
      else (0, n)

/-- The two-adic valuation of `n`. -/
def val2 (n : Nat) : Nat := (splitAux n n).1

/-- The odd part of `n`. -/
def oddPart (n : Nat) : Nat := (splitAux n n).2

/-- `swapAux` and `splitAux` run the same recursion, so the swap is the odd part
with threes in place of twos. -/
theorem swapAux_eq_split : ∀ (fuel n : Nat),
    swapAux fuel n = 3 ^ (splitAux fuel n).1 * (splitAux fuel n).2 := by
  intro fuel
  induction fuel with
  | zero => intro n; simp [swapAux, splitAux]
  | succ fuel ih =>
    intro n
    rcases Arith.mod_two_eq_zero_or_one n with he | ho
    · show (if n % 2 = 0 then 3 * swapAux fuel (n / 2) else n)
          = 3 ^ (splitAux (fuel + 1) n).1 * (splitAux (fuel + 1) n).2
      have hs : splitAux (fuel + 1) n
          = ((splitAux fuel (n / 2)).1 + 1, (splitAux fuel (n / 2)).2) := by
        show (if n % 2 = 0 then _ else _) = _
        rw [if_pos he]
      rw [if_pos he, hs, ih (n / 2), Nat.pow_succ,
        Nat.mul_comm ((3:Nat) ^ (splitAux fuel (n / 2)).1) 3, Nat.mul_assoc]
    · have hs : splitAux (fuel + 1) n = (0, n) := by
        show (if n % 2 = 0 then _ else _) = _
        rw [if_neg (by omega)]
      show (if n % 2 = 0 then 3 * swapAux fuel (n / 2) else n) = _
      rw [if_neg (by omega), hs]
      simp

/-- The factorisation the split computes. -/
theorem splitAux_spec : ∀ (fuel n : Nat), 0 < n → n ≤ fuel →
    n = 2 ^ (splitAux fuel n).1 * (splitAux fuel n).2 := by
  intro fuel
  induction fuel with
  | zero => intro n hn hle; omega
  | succ fuel ih =>
    intro n hn hle
    rcases Arith.mod_two_eq_zero_or_one n with he | ho
    · have hs : splitAux (fuel + 1) n
          = ((splitAux fuel (n / 2)).1 + 1, (splitAux fuel (n / 2)).2) := by
        show (if n % 2 = 0 then _ else _) = _
        rw [if_pos he]
      have hrec := ih (n / 2) (by omega) (by omega)
      rw [hs]
      have h2 : (2:Nat) ^ ((splitAux fuel (n / 2)).1 + 1) * (splitAux fuel (n / 2)).2
          = 2 * (2 ^ (splitAux fuel (n / 2)).1 * (splitAux fuel (n / 2)).2) := by
        rw [Arith.two_pow_succ, Nat.mul_assoc]
      rw [h2, ← hrec]
      omega
    · have hs : splitAux (fuel + 1) n = (0, n) := by
        show (if n % 2 = 0 then _ else _) = _
        rw [if_neg (by omega)]
      rw [hs]
      simp

/-- `n = 2 ^ v₂(n) · oddPart n`. -/
theorem split_spec {n : Nat} (hn : 0 < n) : n = 2 ^ val2 n * oddPart n :=
  splitAux_spec n n hn (Nat.le_refl n)

/-- `swap23 n = 3 ^ v₂(n) · oddPart n`. -/
theorem swap23_eq {n : Nat} : swap23 n = 3 ^ val2 n * oddPart n :=
  swapAux_eq_split n n

/-! ## Small multiplicative helpers (core Lean only) -/

theorem mul_lt_mul_pos_left {y A B : Nat} (hy : 0 < y) (h : A < B) : y * A < y * B := by
  have h1 : y * (A + 1) ≤ y * B := Nat.mul_le_mul_left y h
  have h2 : y * (A + 1) = y * A + y := by rw [Nat.mul_add, Nat.mul_one]
  omega

theorem mul_lt_mul_pos_right {y A B : Nat} (hy : 0 < y) (h : A < B) : A * y < B * y := by
  have := mul_lt_mul_pos_left hy h
  rw [Nat.mul_comm y A, Nat.mul_comm y B] at this
  exact this

theorem lt_of_mul_lt_mul_right' {a b c : Nat} (h : a * c < b * c) : a < b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd h (Nat.not_lt.mpr (Nat.mul_le_mul_right c hge))

/-- **The swap law.**  `2 ^ (v₂ z + 1) · swap23 z = 3 ^ (v₂ z) · 2z`. -/
theorem swap_law_aux (s w : Nat) :
    2 ^ (s + 1) * (3 ^ s * w) = 3 ^ s * (2 * (2 ^ s * w)) := by
  rw [Arith.two_pow_succ]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem swap_law {z : Nat} (hz : 0 < z) :
    2 ^ (val2 z + 1) * swap23 z = 3 ^ val2 z * (2 * z) := by
  have hfac := split_spec hz
  have hval : swap23 z = 3 ^ val2 z * oddPart z := swap23_eq
  calc 2 ^ (val2 z + 1) * swap23 z
      = 2 ^ (val2 z + 1) * (3 ^ val2 z * oddPart z) := by rw [hval]
    _ = 3 ^ val2 z * (2 * (2 ^ val2 z * oddPart z)) := swap_law_aux _ _
    _ = 3 ^ val2 z * (2 * z) := by rw [← hfac]

/-! ## The one-step laws, differing in one character -/

/-- The run length of a `nu` step. -/
def runOf (y : Nat) : Nat := val2 ((y + 1) / 2)

/-- The run length of a mirror step. -/
def mrunOf (y : Nat) : Nat := val2 ((y - 1) / 2)

/-- The mirror of `nu`: the same construction on `(y−1)/2`. -/
def mnu (y : Nat) : Nat := swap23 ((y - 1) / 2)

/-- **The Collatz law.**  `2 ^ (s+1) · nu y = 3 ^ s · (y + 1)`. -/
theorem nu_identity {y : Nat} (hy : y % 2 = 1) :
    2 ^ (runOf y + 1) * nu y = 3 ^ runOf y * (y + 1) := by
  have hz : 0 < (y + 1) / 2 := by omega
  have h := swap_law hz
  have h2 : 2 * ((y + 1) / 2) = y + 1 := by omega
  rw [h2] at h
  exact h

/-- **The mirror law.**  `2 ^ (s+1) · mnu y = 3 ^ s · (y − 1)`.  The only
difference from `nu_identity` is the sign. -/
theorem mnu_identity {y : Nat} (hy : y % 2 = 1) (hy3 : 3 ≤ y) :
    2 ^ (mrunOf y + 1) * mnu y = 3 ^ mrunOf y * (y - 1) := by
  have hz : 0 < (y - 1) / 2 := by omega
  have h := swap_law hz
  have h2 : 2 * ((y - 1) / 2) = y - 1 := by omega
  rw [h2] at h
  exact h

/-! ## Telescoping along the orbit -/

/-- The mirror orbit. -/
def mnuOrbit : Nat → Nat → Nat
  | 0, y => y
  | k + 1, y => mnuOrbit k (mnu y)

/-- Total run length over `B` steps. -/
def runSum : Nat → Nat → Nat
  | 0, _ => 0
  | B + 1, y => runOf y + runSum B (nu y)

/-- `∏ yᵢ` over the first `B` points. -/
def orbProd : Nat → Nat → Nat
  | 0, _ => 1
  | B + 1, y => y * orbProd B (nu y)

/-- `∏ (yᵢ + 1)` over the first `B` points. -/
def orbSucc : Nat → Nat → Nat
  | 0, _ => 1
  | B + 1, y => (y + 1) * orbSucc B (nu y)

/-- Mirror versions. -/
def mrunSum : Nat → Nat → Nat
  | 0, _ => 0
  | B + 1, y => mrunOf y + mrunSum B (mnu y)

def morbProd : Nat → Nat → Nat
  | 0, _ => 1
  | B + 1, y => y * morbProd B (mnu y)

def morbPred : Nat → Nat → Nat
  | 0, _ => 1
  | B + 1, y => (y - 1) * morbPred B (mnu y)

/-- `nu` preserves positivity. -/
theorem nu_pos {y : Nat} (hy : 0 < y) : 0 < nu y := by
  have := nu_odd hy
  omega

/-- **The telescoped Collatz identity.** -/
theorem nu_telescope : ∀ (B y : Nat), y % 2 = 1 → 0 < y →
    2 ^ (runSum B y + B) * orbProd B (nu y) = 3 ^ runSum B y * orbSucc B y := by
  intro B
  induction B with
  | zero => intro y _ _; simp [runSum, orbProd, orbSucc]
  | succ B ih =>
    intro y hy hpos
    have hstep := nu_identity hy
    have hrec := ih (nu y) (nu_odd hpos) (nu_pos hpos)
    show 2 ^ (runOf y + runSum B (nu y) + (B + 1)) * (nu y * orbProd B (nu (nu y)))
        = 3 ^ (runOf y + runSum B (nu y)) * ((y + 1) * orbSucc B (nu y))
    have hsplit : (2:Nat) ^ (runOf y + runSum B (nu y) + (B + 1))
        = 2 ^ (runOf y + 1) * 2 ^ (runSum B (nu y) + B) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have h3 : (3:Nat) ^ (runOf y + runSum B (nu y))
        = 3 ^ runOf y * 3 ^ runSum B (nu y) := by
      rw [← Nat.pow_add]
    calc 2 ^ (runOf y + runSum B (nu y) + (B + 1)) * (nu y * orbProd B (nu (nu y)))
        = (2 ^ (runOf y + 1) * nu y)
            * (2 ^ (runSum B (nu y) + B) * orbProd B (nu (nu y))) := by
          rw [hsplit]
          rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_assoc (2 ^ (runSum B (nu y) + B))]
          rw [Nat.mul_comm (2 ^ (runSum B (nu y) + B)) (nu y), Nat.mul_assoc]
      _ = (3 ^ runOf y * (y + 1)) * (3 ^ runSum B (nu y) * orbSucc B (nu y)) := by
          rw [hstep, hrec]
      _ = 3 ^ (runOf y + runSum B (nu y)) * ((y + 1) * orbSucc B (nu y)) := by
          rw [h3, Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_assoc (y + 1)]
          rw [Nat.mul_comm (y + 1) (3 ^ runSum B (nu y)), Nat.mul_assoc]

/-- **The telescoped mirror identity.**  Same proof, one character different. -/
theorem mnu_telescope : ∀ (B y : Nat), y % 2 = 1 → 3 ≤ y →
    (∀ i : Nat, i ≤ B → 3 ≤ mnuOrbit i y ∧ mnuOrbit i y % 2 = 1) →
    2 ^ (mrunSum B y + B) * morbProd B (mnu y) = 3 ^ mrunSum B y * morbPred B y := by
  intro B
  induction B with
  | zero => intro y _ _ _; simp [mrunSum, morbProd, morbPred]
  | succ B ih =>
    intro y hy hy3 hall
    have hstep := mnu_identity hy hy3
    have hnext : 3 ≤ mnu y ∧ mnu y % 2 = 1 := by
      have h1 := hall 1 (by omega)
      have h2 : mnuOrbit 1 y = mnu y := rfl
      rw [h2] at h1
      exact h1
    have hrec := ih (mnu y) hnext.2 hnext.1 (by
      intro i hi
      have := hall (i + 1) (by omega)
      have hshift : mnuOrbit (i + 1) y = mnuOrbit i (mnu y) := rfl
      rw [hshift] at this
      exact this)
    show 2 ^ (mrunOf y + mrunSum B (mnu y) + (B + 1)) * (mnu y * morbProd B (mnu (mnu y)))
        = 3 ^ (mrunOf y + mrunSum B (mnu y)) * ((y - 1) * morbPred B (mnu y))
    have hsplit : (2:Nat) ^ (mrunOf y + mrunSum B (mnu y) + (B + 1))
        = 2 ^ (mrunOf y + 1) * 2 ^ (mrunSum B (mnu y) + B) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have h3 : (3:Nat) ^ (mrunOf y + mrunSum B (mnu y))
        = 3 ^ mrunOf y * 3 ^ mrunSum B (mnu y) := by
      rw [← Nat.pow_add]
    calc 2 ^ (mrunOf y + mrunSum B (mnu y) + (B + 1)) * (mnu y * morbProd B (mnu (mnu y)))
        = (2 ^ (mrunOf y + 1) * mnu y)
            * (2 ^ (mrunSum B (mnu y) + B) * morbProd B (mnu (mnu y))) := by
          rw [hsplit]
          rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_assoc (2 ^ (mrunSum B (mnu y) + B))]
          rw [Nat.mul_comm (2 ^ (mrunSum B (mnu y) + B)) (mnu y), Nat.mul_assoc]
      _ = (3 ^ mrunOf y * (y - 1)) * (3 ^ mrunSum B (mnu y) * morbPred B (mnu y)) := by
          rw [hstep, hrec]
      _ = 3 ^ (mrunOf y + mrunSum B (mnu y)) * ((y - 1) * morbPred B (mnu y)) := by
          rw [h3, Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_assoc (y - 1)]
          rw [Nat.mul_comm (y - 1) (3 ^ mrunSum B (mnu y)), Nat.mul_assoc]

/-! ## Cancelling the shared product on a cycle -/

/-- Peeling the product from the right. -/
theorem orbProd_snoc : ∀ (B y : Nat),
    orbProd (B + 1) y = orbProd B y * nuOrbit B y := by
  intro B
  induction B with
  | zero => intro y; simp [orbProd, nuOrbit]
  | succ B ih =>
    intro y
    show y * orbProd (B + 1) (nu y) = (y * orbProd B (nu y)) * nuOrbit (B + 1) y
    have hshift : nuOrbit (B + 1) y = nuOrbit B (nu y) := rfl
    rw [ih (nu y), hshift, Nat.mul_assoc]

/-- On a cycle the shifted product equals the unshifted one. -/
theorem orbProd_rotate {B y : Nat} (hpos : 0 < y) (hcyc : nuOrbit B y = y) :
    orbProd B (nu y) = orbProd B y := by
  have h1 : orbProd (B + 1) y = y * orbProd B (nu y) := rfl
  have h2 := orbProd_snoc B y
  rw [hcyc] at h2
  have : y * orbProd B (nu y) = orbProd B y * y := by rw [← h1, h2]
  have hcomm : orbProd B y * y = y * orbProd B y := Nat.mul_comm _ _
  rw [hcomm] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

/-- Mirror version. -/
theorem morbProd_snoc : ∀ (B y : Nat),
    morbProd (B + 1) y = morbProd B y * mnuOrbit B y := by
  intro B
  induction B with
  | zero => intro y; simp [morbProd, mnuOrbit]
  | succ B ih =>
    intro y
    show y * morbProd (B + 1) (mnu y) = (y * morbProd B (mnu y)) * mnuOrbit (B + 1) y
    have hshift : mnuOrbit (B + 1) y = mnuOrbit B (mnu y) := rfl
    rw [ih (mnu y), hshift, Nat.mul_assoc]

theorem morbProd_rotate {B y : Nat} (hpos : 0 < y) (hcyc : mnuOrbit B y = y) :
    morbProd B (mnu y) = morbProd B y := by
  have h1 : morbProd (B + 1) y = y * morbProd B (mnu y) := rfl
  have h2 := morbProd_snoc B y
  rw [hcyc] at h2
  have : y * morbProd B (mnu y) = morbProd B y * y := by rw [← h1, h2]
  have hcomm : morbProd B y * y = y * morbProd B y := Nat.mul_comm _ _
  rw [hcomm] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

/-! ## The comparison of the two products -/

theorem orbProd_pos : ∀ (B y : Nat), 0 < y → 0 < orbProd B y := by
  intro B
  induction B with
  | zero => intro y _; exact Nat.one_pos
  | succ B ih =>
    intro y hy
    exact Nat.mul_pos hy (ih (nu y) (nu_pos hy))

/-- `∏ (yᵢ + 1) > ∏ yᵢ` for a nonempty orbit segment. -/
theorem orbProd_lt_orbSucc : ∀ (B y : Nat), 0 < y → 0 < B →
    orbProd B y < orbSucc B y := by
  intro B
  induction B with
  | zero => intro _ _ h; omega
  | succ B ih =>
    intro y hy _
    show y * orbProd B (nu y) < (y + 1) * orbSucc B (nu y)
    have hposn := nu_pos hy
    match B with
    | 0 =>
      show y * 1 < (y + 1) * 1
      rw [Nat.mul_one, Nat.mul_one]
      omega
    | (k + 1) =>
      have hrec := ih (nu y) hposn (by omega)
      have h1 : y * orbProd (k + 1) (nu y) < y * orbSucc (k + 1) (nu y) :=
        mul_lt_mul_pos_left hy hrec
      have h2 : y * orbSucc (k + 1) (nu y) ≤ (y + 1) * orbSucc (k + 1) (nu y) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

/-- The mirror product is positive along a segment of points `≥ 3`. -/
theorem morbProd_pos : ∀ (B y : Nat), 3 ≤ y →
    (∀ i : Nat, i ≤ B → 3 ≤ mnuOrbit i y) → 0 < morbProd B y := by
  intro B
  induction B with
  | zero => intro _ _ _; exact Nat.one_pos
  | succ B ih =>
    intro y hy hall
    have hnext : 3 ≤ mnu y := by
      have h1 := hall 1 (by omega)
      have h2 : mnuOrbit 1 y = mnu y := rfl
      rw [h2] at h1
      exact h1
    have hrec := ih (mnu y) hnext (by
      intro i hi
      have hthis := hall (i + 1) (by omega)
      have hshift : mnuOrbit (i + 1) y = mnuOrbit i (mnu y) := rfl
      rw [hshift] at hthis
      exact hthis)
    exact Nat.mul_pos (by omega) hrec

/-- `∏ (yᵢ − 1) < ∏ yᵢ` for a nonempty mirror orbit segment of points `≥ 3`. -/
theorem morbPred_lt_morbProd : ∀ (B y : Nat), 3 ≤ y → 0 < B →
    (∀ i : Nat, i ≤ B → 3 ≤ mnuOrbit i y) →
    morbPred B y < morbProd B y := by
  intro B
  induction B with
  | zero => intro _ _ h; omega
  | succ B ih =>
    intro y hy _ hall
    show (y - 1) * morbPred B (mnu y) < y * morbProd B (mnu y)
    have hnext : 3 ≤ mnu y := by
      have h1 := hall 1 (by omega)
      have h2 : mnuOrbit 1 y = mnu y := rfl
      rw [h2] at h1
      exact h1
    have htail : ∀ i : Nat, i ≤ B → 3 ≤ mnuOrbit i (mnu y) := by
      intro i hi
      have hthis := hall (i + 1) (by omega)
      have hshift : mnuOrbit (i + 1) y = mnuOrbit i (mnu y) := rfl
      rw [hshift] at hthis
      exact hthis
    have hppos : 0 < morbProd B (mnu y) := morbProd_pos B (mnu y) hnext htail
    match B with
    | 0 =>
      show (y - 1) * 1 < y * 1
      rw [Nat.mul_one, Nat.mul_one]
      omega
    | (k + 1) =>
      have hrec := ih (mnu y) hnext (by omega) htail
      have h1 : (y - 1) * morbPred (k + 1) (mnu y) ≤ (y - 1) * morbProd (k + 1) (mnu y) :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hrec)
      have h2 : (y - 1) * morbProd (k + 1) (mnu y) < y * morbProd (k + 1) (mnu y) :=
        mul_lt_mul_pos_right hppos (by omega)
      omega

/-! ## The separation -/

/-- **A Collatz cycle is light.**  `3 ^ S < 2 ^ (S + B)`, i.e. `3 ^ a < 2 ^ j`. -/
theorem cycle_light {B y : Nat} (hy : y % 2 = 1) (hpos : 0 < y) (hB : 0 < B)
    (hcyc : nuOrbit B y = y) :
    3 ^ runSum B y < 2 ^ (runSum B y + B) := by
  have htel := nu_telescope B y hy hpos
  rw [orbProd_rotate hpos hcyc] at htel
  have hlt := orbProd_lt_orbSucc B y hpos hB
  have hP := orbProd_pos B y hpos
  have hgt : 3 ^ runSum B y * orbProd B y < 3 ^ runSum B y * orbSucc B y :=
    mul_lt_mul_pos_left (Arith.three_pow_pos _) hlt
  rw [← htel] at hgt
  exact lt_of_mul_lt_mul_right' hgt

/-- **A mirror cycle is heavy.**  `2 ^ (S + B) < 3 ^ S`.  The negation of
`cycle_light`, proved by the same argument with the sign reversed. -/
theorem mirror_cycle_heavy {B y : Nat} (hy : y % 2 = 1) (hy3 : 3 ≤ y) (hB : 0 < B)
    (hcyc : mnuOrbit B y = y)
    (hall : ∀ i : Nat, i ≤ B → 3 ≤ mnuOrbit i y ∧ mnuOrbit i y % 2 = 1) :
    2 ^ (mrunSum B y + B) < 3 ^ mrunSum B y := by
  have htel := mnu_telescope B y hy hy3 hall
  rw [morbProd_rotate (by omega) hcyc] at htel
  have hlt := morbPred_lt_morbProd B y hy3 hB (fun i hi => (hall i hi).1)
  have hgt : 3 ^ mrunSum B y * morbPred B y < 3 ^ mrunSum B y * morbProd B y :=
    mul_lt_mul_pos_left (Arith.three_pow_pos _) hlt
  rw [← htel] at hgt
  exact lt_of_mul_lt_mul_right' hgt

/-- **The separation, as the two conclusions side by side.**  For the same shape
`(B, S)` the ceiling branch forces `3 ^ S < 2 ^ (S+B)` and the floor branch forces
the reverse.  No statement invariant under the swap can prove either. -/
theorem separation {B y z : Nat}
    (hy : y % 2 = 1) (hpos : 0 < y) (hB : 0 < B) (hcyc : nuOrbit B y = y)
    (hz : z % 2 = 1) (hz3 : 3 ≤ z) (hzcyc : mnuOrbit B z = z)
    (hall : ∀ i : Nat, i ≤ B → 3 ≤ mnuOrbit i z ∧ mnuOrbit i z % 2 = 1) :
    3 ^ runSum B y < 2 ^ (runSum B y + B)
      ∧ 2 ^ (mrunSum B z + B) < 3 ^ mrunSum B z :=
  ⟨cycle_light hy hpos hB hcyc, mirror_cycle_heavy hz hz3 hB hzcyc hall⟩

/-! ## The witnesses -/

/-- The Collatz cycle `y = 3` — the image of `1 → 2 → 1` — is light: `3 < 4`. -/
theorem three_cycle_light : nu 3 = 3 ∧ runSum 1 3 = 1 ∧ 3 ^ 1 < 2 ^ (1 + 1) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The mirror cycle `y = 9` — the image of `5 → 7 → 10 → 5` — is heavy: `8 < 9`. -/
theorem nine_cycle_heavy : mnu 9 = 9 ∧ mrunSum 1 9 = 2 ∧ 2 ^ (2 + 1) < 3 ^ 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The mirror's four-step cycle `135 → 67 → 33 → 81 → 135` — the image of the
`3n−1` cycle through `17` — is heavy as well: `2 ^ 11 = 2048 < 2187 = 3 ^ 7`. -/
theorem long_mirror_cycle_heavy :
    mnuOrbit 4 135 = 135 ∧ mrunSum 4 135 = 7 ∧ 2 ^ (7 + 4) < 3 ^ 7 := by
  refine ⟨by decide, by decide, by decide⟩

end DeviceProduct
end Collatz
