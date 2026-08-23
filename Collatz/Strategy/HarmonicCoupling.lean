import Collatz.Strategy.CouplingNormal

/-!
# Round XII — the harmonic coupling `Σ 1/(3 xᵢ)`, its exact form, and its dominator

## What the object is

Round XI reported a "universal accumulation constant"

>  `Σ over odd orbit values xᵢ of 1/(3 xᵢ)  ≤  0.2299545`, attained at `n = 993`.

That number is **not** `log(1+r)`, as the Round XI text says.  Recomputed in exact
rationals (two independent implementations, accelerated map and plain map, identical
odd-value lists):

* `S(993) := Σ_{odd xᵢ ∈ orbit(993)} 1/(3 xᵢ) = 0.229954486122031…`  — this **is** the
  reported constant.
* `ρ(993) := 2^61 / (3^32 · 993) = 2305843009213693952/1840049047529878113
  = 1.253142144395068…`, so `log ρ(993) = 0.225654112731978…`.

Round XI's "`1 + r = 1.258543`" is `exp(S(993))`, not `1 + r`; the two objects were
composed by mistake.  `S` and `log ρ` differ in the **third** digit.  (COMPUTATIONAL,
exact rationals.)

## The exact closed form

For a start `n` whose orbit reaches `1` after `L` halvings with `a` odd steps
(`L` = length of the *accelerated* orbit = number of halvings of the *plain* orbit;
`a` is the same for both maps, and both maps visit the same odd values in the same
order — so `S` is map-independent and only `L` names a map):

>  `∏_{odd xᵢ} (1 + 1/(3 xᵢ)) = 2^L / (3^a n) = ρ(n)`   (`one_add_coupling` with
>  `x_L = 1`), hence `log ρ(n) ≤ S(n) ≤ ρ(n) − 1`.

`ρ(n)` is an **exact rational**; `S(n)` is an exact rational too, but a different one
(at `n = 993` its reduced form has a 60-digit numerator and a 61-digit denominator).
Neither is a "nice" constant: the maximum is the value of an explicit finite sum at one
explicit integer, `S(993) = Σ over the 32 odd values of the orbit of 993`.  There is no
logarithm and no limit in it.  (MATHEMATICALLY_PROVED for the identity; the exact
rationals are COMPUTATIONAL.)

## What is formalised here

The upper half of the sandwich, in `Nat`, with no rationals:

* `couplingTerms n j 0 = affineC j n` (`couplingTerms_eq_affineC`).  `affineC` **is** the
  sum `Σ_{i<j, xᵢ odd} 2^i · 3^(#odd steps in (i,j))`, made explicit as a summation
  rather than a recursion.
* `harmonic_term_le`: for every odd index `i`, the `i`-th harmonic term is dominated by
  the `i`-th coupling term over the common denominator `3^(A_j)·n`:
  `3^(A_j)·n ≤ 3·xᵢ·(2^i·3^(A'))`, i.e. `1/(3 xᵢ) ≤ tᵢ / (3^(A_j)·n)`.

Summing the second over `i < j` and substituting the first gives, termwise and with no
inequality between infinite objects,

>  **`S_j(n) = Σ_{i<j, xᵢ odd} 1/(3 xᵢ)  ≤  affineC j n / (3^(A_j)·n) = ρ_j(n) − 1`.**

At `j = L` and `x_L = 1` this is `S(n) ≤ 2^L/(3^a n) − 1`.  Checked: `0.2299545 ≤
0.2531421` at `n = 993`.

## Why `993`, formalised

`S(T n) = S(n) − 1/(3n)` for odd `n` and `S(2n) = S(n)`, so `S` is **strictly
increasing along backward orbits**: a maximiser can have no odd predecessor.  An odd
`m` has an odd `T`-predecessor iff `2m ≡ 1 (mod 3)`, so *every odd multiple of `3` is a
leaf of the backward tree*.  `993 = 3·331` is such a leaf, and it is the smallest odd
predecessor of `745`, which is the smallest odd predecessor of `559`
(`993 = (4·745−1)/3`, `745 = (4·559−1)/3`).  `no_odd_preimage_of_three_dvd` is the leaf
theorem; `leaf_993` is the instance.

The record chain for `S` is `1, 3, 7, 9, 559, 745, 993` and its last three entries are a
single backward chain, each the *smallest* odd predecessor of the next, terminating
because `3 ∣ 993`.  The gap to the runner-up below it is exactly one term:
`S(993) − S(745) = 1/(3·993) = 1/2979` (`step_993_745`, `step_745_559`).

## Status of the maximality claim

**CONJECTURE**, verified COMPUTATIONALLY: `993` maximises both `S` and `ρ` over all
`n ≤ 10^9` (exhaustive, C and Python agreeing; `S(2n) = S(n)` reduces the search to odd
`n`).  It is *not* proved and cannot be by these means: `S(n) = H(n,B) + S(m)` where
`m < B` is the first orbit value below `B`, and `max_{m<B} S(m) = S(993)` as soon as
`B > 993`, so no exhaustive range ever closes the argument.  The runner-up is `3531`
with `S = 0.229860033`, and the next values accumulate from above at
`λ ≈ 0.2298345`, strictly below `S(993)`: `993` is an **isolated** maximiser, not the
head of an extremal family.
-/

set_option maxRecDepth 40000

namespace Collatz
namespace HarmonicCoupling

open AccumulatorArith CycleAccumulator AffineExact CouplingNormal

/-! ## The coupling accumulator as an explicit sum of per-odd-step terms -/

/-- `couplingTerms n k i` is the sum, over the `k` orbit indices `i, …, i+k−1`, of the
term `2^t · 3^(number of odd steps strictly after `t` and before `i+k`)` contributed by
each **odd** index `t`.  This is the summation form of `affineC`. -/
def couplingTerms (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, i =>
      (if acceleratedOrbit i n % 2 = 1 then
          2 ^ i * 3 ^ oddCount (acceleratedOrbit (i + 1) n) k else 0)
        + couplingTerms n k (i + 1)

@[simp] theorem couplingTerms_zero (n i : Nat) : couplingTerms n 0 i = 0 := rfl

theorem couplingTerms_succ (n k i : Nat) :
    couplingTerms n (k + 1) i
      = (if acceleratedOrbit i n % 2 = 1 then
            2 ^ i * 3 ^ oddCount (acceleratedOrbit (i + 1) n) k else 0)
          + couplingTerms n k (i + 1) := rfl

/-- `affineC 1 y` is the indicator of `y` being odd. -/
theorem affineC_one (y : Nat) : affineC 1 y = if y % 2 = 1 then 1 else 0 := by
  rcases Arith.mod_two_eq_zero_or_one y with he | ho
  · rw [show (1 : Nat) = 0 + 1 from rfl, affineC_even (by simpa using he), if_neg (by omega)]
    rfl
  · rw [show (1 : Nat) = 0 + 1 from rfl, affineC_odd (by simpa using ho), if_pos ho]
    rfl

/-- **The window sum is the window accumulator, weighted by its start.**  The absolute
`2`-powers of a window starting at index `i` are `2^i` times the window's own. -/
theorem couplingTerms_eq (n : Nat) :
    ∀ (k i : Nat), couplingTerms n k i = 2 ^ i * affineC k (acceleratedOrbit i n) := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
    intro i
    have hshift : acceleratedOrbit 1 (acceleratedOrbit i n) = acceleratedOrbit (i + 1) n := by
      rw [acceleratedOrbit_add 1 i n, Nat.add_comm 1 i]
    have hsplit :=
      affineC_add (acceleratedOrbit i n) 1 k
    rw [hshift] at hsplit
    have hcomm : (1 : Nat) + k = k + 1 := Nat.add_comm 1 k
    rw [hcomm] at hsplit
    rw [couplingTerms_succ, ih (i + 1), hsplit, affineC_one, Nat.mul_add]
    have h2 : 2 ^ (i + 1) = 2 ^ i * 2 := by rw [Nat.pow_succ]
    rw [h2]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit i n) with he | ho
    · rw [if_neg (by omega), if_neg (by omega)]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · rw [if_pos ho, if_pos ho]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- **`affineC` is the explicit sum of the per-odd-step coupling terms.** -/
theorem couplingTerms_eq_affineC (n j : Nat) : couplingTerms n j 0 = affineC j n := by
  have h := couplingTerms_eq n j 0
  simpa using h

/-! ## Each harmonic term is dominated by its coupling term -/

/-- The orbit never falls below its own affine lower bound: `3^(A i)·n ≤ 2^i·xᵢ`. -/
theorem three_pow_mul_le (n i : Nat) :
    3 ^ oddCount n i * n ≤ 2 ^ i * acceleratedOrbit i n := by
  rw [← one_add_coupling n i]
  exact Nat.le_add_right _ _

/-- **The termwise domination.**  For an odd orbit index `i` and any continuation of
length `k`, with `j = i+1+k` and `A_j = oddCount n j`:

  `3^(A_j)·n  ≤  3·xᵢ·(2^i·3^(A'))`,  where `A' = oddCount (x_{i+1}) k`,

which is exactly `1/(3 xᵢ) ≤ tᵢ / (3^(A_j)·n)` for the `i`-th term `tᵢ` of
`couplingTerms`.  Summing over `i < j` and using `couplingTerms_eq_affineC` gives
`Σ 1/(3 xᵢ) ≤ affineC j n / (3^(A_j)·n)`. -/
theorem harmonic_term_le (n i k : Nat) (h : acceleratedOrbit i n % 2 = 1) :
    3 ^ oddCount n (i + 1 + k) * n
      ≤ 3 * acceleratedOrbit i n * (2 ^ i * 3 ^ oddCount (acceleratedOrbit (i + 1) n) k) := by
  have hcount : oddCount n (i + 1 + k)
      = oddCount n i + 1 + oddCount (acceleratedOrbit (i + 1) n) k := by
    rw [oddCount_add n (i + 1) k, Density.oddCount_succ_last n i, h]
  have hbase := three_pow_mul_le n i
  generalize hK : oddCount (acceleratedOrbit (i + 1) n) k = K
  rw [hcount, hK]
  have hstep : 3 ^ (oddCount n i + 1 + K) * n
      = (3 ^ oddCount n i * n) * (3 * 3 ^ K) := by
    rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have htarget : 3 * acceleratedOrbit i n * (2 ^ i * 3 ^ K)
      = (2 ^ i * acceleratedOrbit i n) * (3 * 3 ^ K) := by
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hstep, htarget]
  exact Nat.mul_le_mul_right _ hbase

/-- Each single coupling term is itself below the total accumulator — the crude
consequence of the sum identity, kept because it needs no summation. -/
theorem term_le_affineC (n i k : Nat) (h : acceleratedOrbit i n % 2 = 1) :
    2 ^ i * 3 ^ oddCount (acceleratedOrbit (i + 1) n) k ≤ affineC (i + 1 + k) n := by
  have hsplit := affineC_add n (i + 1) k
  have hone : affineC (i + 1) n = 3 * affineC i n + 2 ^ i := affineC_odd h
  rw [hsplit, hone]
  have : 2 ^ i * 3 ^ oddCount (acceleratedOrbit (i + 1) n) k
      ≤ 3 ^ oddCount (acceleratedOrbit (i + 1) n) k * (3 * affineC i n + 2 ^ i) := by
    rw [Nat.mul_comm (2 ^ i)]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Leaves of the backward tree, and why `993` -/

/-- **Odd multiples of three are leaves.**  No odd number maps onto a multiple of `3`
under the accelerated map, so an odd multiple of `3` has no odd predecessor and `S`
cannot be increased past it by extending the orbit backwards. -/
theorem no_odd_preimage_of_three_dvd {m x : Nat} (hm : m % 3 = 0) (hx : x % 2 = 1) :
    acceleratedStep x ≠ m := by
  intro hstep
  rw [acceleratedStep, if_neg (by omega)] at hstep
  omega

/-- `993 = 3 · 331` is a leaf. -/
theorem leaf_993 {x : Nat} (hx : x % 2 = 1) : acceleratedStep x ≠ 993 :=
  no_odd_preimage_of_three_dvd (by decide) hx

/-- Doubling changes nothing: `T(2n) = n`, so `S(2n) = S(n)` and the search for a
maximiser may be restricted to odd starts. -/
theorem step_two_mul (n : Nat) : acceleratedStep (2 * n) = n := by
  rw [acceleratedStep, if_pos (by omega)]
  omega

/-! ## The extremal orbit, exactly -/

/-- The two accelerated steps from `993` land on `745`: the single term `1/(3·993)` is
the whole gap between the maximiser and the best start below it. -/
theorem step_993_745 : acceleratedOrbit 2 993 = 745 := by decide

/-- And from `745` to `559`, the next link of the record chain. -/
theorem step_745_559 : acceleratedOrbit 2 745 = 559 := by decide

/-- `993` is the smallest odd predecessor of `745`, and `745` of `559`:
`p = (4m−1)/3`. -/
theorem smallest_pred_993 : 4 * 745 = 3 * 993 + 1 := by decide

theorem smallest_pred_745 : 4 * 559 = 3 * 745 + 1 := by decide

/-- The orbit of `993` reaches `1` in `61` accelerated steps. -/
theorem orbit_993 : acceleratedOrbit 61 993 = 1 := by decide

/-- …with exactly `32` odd steps. -/
theorem oddCount_993 : oddCount 993 61 = 32 := by decide

/-- **The exact rational `ρ(993)`, cleared of division.**  `2^61 = 3^32·993 + C`, so
`ρ(993) = 2^61/(3^32·993) = 2305843009213693952/1840049047529878113`, and the upper
bound of the sandwich is `ρ(993) − 1 = 465793961683815839/1840049047529878113 =
0.2531421…`, against `S(993) = 0.2299545…`. -/
theorem rho_993 : 3 ^ 32 * 993 + affineC 61 993 = 2 ^ 61 := by
  have h := one_add_coupling 993 61
  rw [orbit_993, oddCount_993] at h
  omega

/-- The accumulator at `993` in closed integer form. -/
theorem affineC_993 : affineC 61 993 = 465793961683815839 := by
  have h := rho_993
  omega

end HarmonicCoupling
end Collatz
