import Collatz.Strategy.ThreeAdic
import Collatz.Strategy.ScaleRecord

/-!
# The +1-carry cocycle

A cocycle for `T` is an `A : Nat → Nat → Nat` with

    A n (k + ℓ)  =  A n k  +  A (T^k n) ℓ.

Coboundaries `Φ(T^k n) − Φ(n)` are the special case of a potential (and a
ranking, when `Φ` decreases).  The path-sum of extra halvings is the
valuation budget.  This file records a third integer cocycle: the count of
even steps that inject 3-divisibility into `u = x + 1`.

    injBit x  =  1  if x is even and x ≡ 1 (mod 3), else 0
    injCount n k  =  Σ_{i < k} injBit (T^i n)

This is the base-3 carry of adding `1` to `x+1` on even steps, equivalently
`3 ∣ (T x + 1)` (`injects_iff_three_dvd`).  It is not `v₂(T x + 1) − v₂(x + 1)`
(both sides odd at `x = 4`, while `injBit 4 = 1`) and it is not `Σ W_i`
(a length-two even run injects once; two length-one even runs inject never).

Proved:

* the cocycle law (`injCount_add`);
* the winding of even runs around `ℤ/3` (`odd_step_mod_three`,
  `even_kill_to_inj`, `even_inj_to_kill`, `injBit_step_of_odd`);
* support on the least never-dropper: the cocycle vanishes on every prefix
  that stays below `3m + 1` (`injCount_eq_zero_of_low_window`);
* it is not a class potential modulo 6 (`inj_not_class_potential`);
* it vanishes on the known never-dropper `1` and on every even `expStep`
  (`injCount_one`, `expStep_even_not_three_dvd_succ`).

No statement about Collatz is made.
-/

namespace Collatz
namespace DeviceCocycle

open Reach
open NeverDrops
open ThreeAdic
open ScaleRecord

/-! ## The 1-cochain -/

/-- `1` on even `x ≡ 1 (mod 3)`, else `0`.  Equivalently, `x ≡ 4 (mod 6)`. -/
def injBit (x : Nat) : Nat :=
  if x % 2 = 0 then (if x % 3 = 1 then 1 else 0) else 0

theorem injBit_of_odd {x : Nat} (h : x % 2 = 1) : injBit x = 0 := by
  unfold injBit
  rw [if_neg (by omega)]

theorem injBit_of_inject {x : Nat} (he : x % 2 = 0) (h3 : x % 3 = 1) :
    injBit x = 1 := by
  unfold injBit
  rw [if_pos he, if_pos h3]

theorem injBit_of_even_ne {x : Nat} (he : x % 2 = 0) (h3 : x % 3 ≠ 1) :
    injBit x = 0 := by
  unfold injBit
  rw [if_pos he, if_neg h3]

theorem injBit_four : injBit 4 = 1 := by
  decide

theorem injBit_eight : injBit 8 = 0 := by
  decide

theorem injBit_two : injBit 2 = 0 := by
  decide

theorem injBit_one : injBit 1 = 0 := by
  decide

/-! ## The cocycle -/

/-- Path integral of `injBit` along the first `k` accelerated steps. -/
def injCount : Nat → Nat → Nat
  | _, 0 => 0
  | n, k + 1 => injCount n k + injBit (acceleratedOrbit k n)

@[simp] theorem injCount_zero (n : Nat) : injCount n 0 = 0 := rfl

theorem injCount_succ (n k : Nat) :
    injCount n (k + 1) = injCount n k + injBit (acceleratedOrbit k n) :=
  rfl

/-- **The cocycle law.**  Splitting a window at time `j`,
`injCount n (j + k) = injCount n j + injCount (T^j n) k`. -/
theorem injCount_add (n j : Nat) : ∀ k : Nat,
    injCount n (j + k) = injCount n j + injCount (acceleratedOrbit j n) k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hjoin : acceleratedOrbit k (acceleratedOrbit j n)
        = acceleratedOrbit (j + k) n := by
      rw [acceleratedOrbit_add k j n, Nat.add_comm k j]
    rw [← Nat.add_assoc, injCount_succ, ih, ← hjoin, injCount_succ, Nat.add_assoc]

/-- The cocycle is nondecreasing in the window, so it is not a descent in time. -/
theorem injCount_mono (n j k : Nat) :
    injCount n j ≤ injCount n (j + k) := by
  rw [injCount_add]
  omega

/-! ## Identification with the +1 injection -/

/-- **Even injection is `3 ∣ (T x + 1)`.**  The 1-cochain is exactly the
even-step case of `ThreeAdic.three_dvd_even_step_iff`. -/
theorem injects_iff_three_dvd {x : Nat} (he : x % 2 = 0) :
    injBit x = 1 ↔ 3 ∣ (acceleratedStep x + 1) := by
  constructor
  · intro h
    have h3 : x % 3 = 1 := by
      unfold injBit at h
      rw [if_pos he] at h
      by_cases hmod : x % 3 = 1
      · exact hmod
      · rw [if_neg hmod] at h; omega
    exact (three_dvd_even_step_iff he).mpr h3
  · intro hdvd
    exact injBit_of_inject he ((three_dvd_even_step_iff he).mp hdvd)

/-- Not the `v₂(x+1)` coboundary: at `4` the injection bit is `1` while both
`x+1` and `T x + 1` are odd. -/
theorem inj_not_shift_val2 :
    injBit 4 = 1 ∧ (4 + 1) % 2 = 1 ∧ (acceleratedStep 4 + 1) % 2 = 1 := by
  decide

/-! ## Winding around `ℤ/3` -/

/-- An odd step lands on `2 (mod 3)` — the kill class, sitting on a power of
3 in the shift `u = n+1`. -/
theorem odd_step_mod_three {x : Nat} (h : x % 2 = 1) :
    acceleratedStep x % 3 = 2 := by
  have hx : x = 2 * (x / 2) + 1 := by omega
  have hstep : acceleratedStep x = (3 * x + 1) / 2 := by
    rw [acceleratedStep, if_neg (by omega)]
  have harith : (3 * x + 1) / 2 = 3 * (x / 2) + 2 := by omega
  rw [hstep, harith]
  omega

/-- A kill step (even, `≡ 2 (mod 3)`) lands on the injection class. -/
theorem even_kill_to_inj {x : Nat} (he : x % 2 = 0) (h3 : x % 3 = 2) :
    acceleratedStep x % 3 = 1 := by
  have hx : x = 6 * (x / 6) + 2 := by omega
  have hstep : acceleratedStep x = x / 2 := by
    rw [acceleratedStep, if_pos he]
  have harith : x / 2 = 3 * (x / 6) + 1 := by omega
  rw [hstep, harith]
  omega

/-- An injection step (even, `≡ 1 (mod 3)`) lands on the kill class. -/
theorem even_inj_to_kill {x : Nat} (he : x % 2 = 0) (h3 : x % 3 = 1) :
    acceleratedStep x % 3 = 2 := by
  have hx : x = 6 * (x / 6) + 4 := by omega
  have hstep : acceleratedStep x = x / 2 := by
    rw [acceleratedStep, if_pos he]
  have harith : x / 2 = 3 * (x / 6) + 2 := by omega
  rw [hstep, harith]
  omega

/-- **No injection immediately after an odd step.**  The winding always
starts on the kill class. -/
theorem injBit_step_of_odd {x : Nat} (h : x % 2 = 1) :
    injBit (acceleratedStep x) = 0 := by
  have hmod : acceleratedStep x % 3 = 2 := odd_step_mod_three h
  have hne : acceleratedStep x % 3 ≠ 1 := by omega
  unfold injBit
  rcases Arith.mod_two_eq_zero_or_one (acceleratedStep x) with he | ho
  · rw [if_pos he, if_neg hne]
  · rw [if_neg (by omega)]

/-! ## Not a class potential -/

/-- **Not a coboundary of a class function that identifies `8` with `2`.**
Those two are the same residue modulo 6 (`≡ 2`), so any potential constant on
`ℤ/6` would have to identify them.  The 1-cochain does not telescope. -/
theorem inj_not_class_potential {Φ : Nat → Nat}
    (h4 : Φ (acceleratedStep 4) = Φ 4 + injBit 4)
    (h8 : Φ (acceleratedStep 8) = Φ 8 + injBit 8)
    (hcls : Φ 8 = Φ 2) : False := by
  have hs4 : acceleratedStep 4 = 2 := by decide
  have hs8 : acceleratedStep 8 = 4 := by decide
  rw [hs4, injBit_four] at h4
  rw [hs8, injBit_eight] at h8
  omega

/-! ## Constraint on never-dropping orbits -/

/-- The 1-cochain vanishes at every low orbit point of the least never-dropper:
an injection would be an even point `≡ 1 (mod 3)`, hence at least `3m + 1`. -/
theorem injBit_eq_zero_of_low {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hsmall : acceleratedOrbit i m < 3 * m + 1) :
    injBit (acceleratedOrbit i m) = 0 := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit i m) with he | ho
  · by_cases h3 : acceleratedOrbit i m % 3 = 1
    · have hge := even_orbit_one_mod_three_ge hgt hnd hmin he h3
      omega
    · exact injBit_of_even_ne he h3
  · exact injBit_of_odd ho

/-- **Support law.**  On the least never-dropper, the injection cocycle of any
prefix that stays below `3m + 1` is zero.  All injections live in the high
orbit. -/
theorem injCount_eq_zero_of_low_window {m k : Nat} (hgt : 1 < m)
    (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (hbound : ∀ i : Nat, i < k → acceleratedOrbit i m < 3 * m + 1) :
    injCount m k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlow : acceleratedOrbit k m < 3 * m + 1 := hbound k (by omega)
    have hbit := injBit_eq_zero_of_low hgt hnd hmin hlow
    have ih' : injCount m k = 0 :=
      ih (fun i hi => hbound i (by omega))
    rw [injCount_succ, ih', hbit]

/-! ## The known never-dropper -/

/-- The accelerated orbit of `1` is the 2-cycle `1, 2, 1, 2, …`. -/
theorem orbit_one : ∀ k : Nat,
    acceleratedOrbit k 1 = if k % 2 = 0 then 1 else 2 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [acceleratedOrbit_succ_step, ih]
    by_cases hk : k % 2 = 0
    · rw [if_pos hk, acceleratedStep_one]
      have : (k + 1) % 2 ≠ 0 := by omega
      rw [if_neg this]
    · rw [if_neg hk, acceleratedStep_two]
      have : (k + 1) % 2 = 0 := by omega
      rw [if_pos this]

/-- **The injection cocycle vanishes on `1`.**  Neither point of the trivial
cycle is an even `≡ 1 (mod 3)`. -/
theorem injCount_one : ∀ k : Nat, injCount 1 k = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [injCount_succ, ih, orbit_one]
    by_cases hk : k % 2 = 0
    · rw [if_pos hk, injBit_one]
    · rw [if_neg hk, injBit_two]

/-! ## expStep filter -/

/-- **expStep never injects on even inputs.**  The even branch is `3x/2`, so
`2 (expStep x + 1) = 3x + 2 ≡ 2 (mod 3)`. -/
theorem expStep_even_not_three_dvd_succ {x : Nat} (he : x % 2 = 0) :
    ¬ (3 ∣ (expStep x + 1)) := by
  unfold expStep
  rw [if_pos he]
  intro ⟨c, hc⟩
  have h2 : 2 * (3 * x / 2 + 1) = 3 * x + 2 := by omega
  rw [hc] at h2
  omega

/-- The expStep analogue of `injBit` — `3 ∣ (expStep x + 1)` on evens — is
identically zero. -/
def expInjBit (x : Nat) : Nat :=
  if x % 2 = 0 then (if (expStep x + 1) % 3 = 0 then 1 else 0) else 0

theorem expInjBit_eq_zero (x : Nat) : expInjBit x = 0 := by
  unfold expInjBit
  by_cases he : x % 2 = 0
  · have hne : (expStep x + 1) % 3 ≠ 0 := by
      intro hz
      exact expStep_even_not_three_dvd_succ he (Nat.dvd_of_mod_eq_zero hz)
    rw [if_pos he, if_neg hne]
  · rw [if_neg he]

/-! ## `3x+d` filter -/

/-- The `3x−1` cycle `5 → 7 → 10 → 5` carries an injection at `10`, which sits
below `3·5 + 1 = 16`.  The support law is therefore `d = 1`-specific; the
cocycle law is not (the even branch never depends on `d`). -/
theorem three_x_minus_one_cycle_injects :
    (3 * 5 - 1) / 2 = 7 ∧ (3 * 7 - 1) / 2 = 10 ∧ 10 / 2 = 5
      ∧ 10 % 2 = 0 ∧ 10 % 3 = 1 ∧ 10 < 3 * 5 + 1 := by
  decide

/-- The `3x+5` cycle `1 → 4 → 2` injects at `4`. -/
theorem three_x_plus_five_cycle_injects :
    (3 * 1 + 5) / 2 = 4 ∧ 4 / 2 = 2 ∧ 2 / 2 = 1
      ∧ injBit 4 = 1 := by
  decide

/-! ## Package -/

/-- The exact cocycle law, the never-dropper support constraint, the
class-potential obstruction, and the two filters.  No Collatz claim. -/
theorem round_summary :
    (∀ n j k, injCount n (j + k)
        = injCount n j + injCount (acceleratedOrbit j n) k)
      ∧ (∀ {m k : Nat}, 1 < m → NeverDrops m →
          (∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) →
          (∀ i : Nat, i < k → acceleratedOrbit i m < 3 * m + 1) →
          injCount m k = 0)
      ∧ (∀ k, injCount 1 k = 0)
      ∧ (∀ x : Nat, x % 2 = 0 → ¬ (3 ∣ (expStep x + 1)))
      ∧ (10 % 2 = 0 ∧ 10 % 3 = 1 ∧ 10 < 3 * 5 + 1) :=
  ⟨injCount_add,
   fun hgt hnd hmin hbound => injCount_eq_zero_of_low_window hgt hnd hmin hbound,
   injCount_one,
   fun _ he => expStep_even_not_three_dvd_succ he,
   by decide⟩

end DeviceCocycle
end Collatz

section AxiomAudit
open Collatz.DeviceCocycle
#print axioms injCount_add
#print axioms injCount_eq_zero_of_low_window
#print axioms inj_not_class_potential
#print axioms injCount_one
#print axioms expStep_even_not_three_dvd_succ
#print axioms odd_step_mod_three
end AxiomAudit
