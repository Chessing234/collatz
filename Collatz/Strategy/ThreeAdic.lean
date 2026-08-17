import Collatz.Strategy.BackwardRun

/-!
# The exact 3-adic law of a forward step

`OddRuns` computes what a step does to the 2-adic valuation of `u = x + 1`.
This file computes what it does to the **3-adic** valuation, which is what the
master bound of `BackwardRun` is stated in terms of.

Two exact laws, in divisibility form so that no valuation function is needed:

* **odd step:** for odd `x`,  `3 ^ k ∣ (x + 1)  ↔  3 ^ (k+1) ∣ (T(x) + 1)`.
  The 3-adic valuation of `u` rises by *exactly one*, because `2(T(x)+1) = 3(x+1)`
  and `3` is coprime to `2`.
* **even step:** for even `x`,  `3 ^ j ∣ (T(x) + 1)  ↔  3 ^ j ∣ (x + 2)/2`;
  in particular `3 ∣ (T(x)+1)` exactly when `x ≡ 1 (mod 3)`.

A first guess — that `v₃(u)` simply counts the current run of odd steps — is
**false**: an even step can *inject* 3-divisibility from nothing.  Measured over
all orbits from odd starts below `20 000`, about `32%` of even steps do exactly
that.  So the even steps are where the master bound has content.

## The new constraint

Combining the even-step law with `BackwardRun.orbit_backward_bound` at the *next*
index gives, for the least never-dropper `m`:

**every even orbit point `x ≡ 1 (mod 3)` satisfies `x ≥ 3m + 1`.**

Equivalently, the window `[m, 3m+1)` contains no even orbit point congruent to
`1` modulo `3` — a forbidden region of width `2m`, in a residue class the earlier
results said nothing about.  Together with
`OrbitDescent.orbit_not_two_mod_three_below` (points `≡ 2 mod 3` are `≥ (3m+1)/2`)
both non-zero classes modulo three are now constrained, and by different amounts.
-/

namespace Collatz
namespace ThreeAdic

open Reach Congruence NeverDrops BackwardRun

/-! ## Coprimality -/

/-- A power of three dividing `2 y` divides `y`.  The mirror of
`OddRuns.dvd_of_three_mul`. -/
theorem dvd_of_two_mul : ∀ (k y : Nat), 3 ^ k ∣ 2 * y → 3 ^ k ∣ y := by
  intro k
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hdvd
    have hthree : y % 3 = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have h3 : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := Arith.three_pow_succ k
      rw [h3, Nat.mul_assoc] at hc
      omega
    obtain ⟨y', hy'⟩ : ∃ y', y = 3 * y' := ⟨y / 3, by omega⟩
    subst hy'
    have hstrip : 3 ^ k ∣ 2 * y' := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have h3 : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := Arith.three_pow_succ k
      rw [h3, Nat.mul_assoc] at hc
      omega
    obtain ⟨d, hd⟩ := ih y' hstrip
    refine ⟨d, ?_⟩
    have hA : (3:Nat) ^ (k + 1) * d = 3 * (3 ^ k * d) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc]
    rw [hA, ← hd]

/-! ## The odd step raises the 3-adic valuation by exactly one -/

/-- **The odd-step law.**  For odd `x`, `3 ^ k` divides `x + 1` exactly when
`3 ^ (k+1)` divides `T(x) + 1`. -/
theorem three_pow_odd_step_iff {x : Nat} (hx : x % 2 = 1) (k : Nat) :
    3 ^ k ∣ (x + 1) ↔ 3 ^ (k + 1) ∣ (acceleratedStep x + 1) := by
  have hid : 2 * (acceleratedStep x + 1) = 3 * (x + 1) := OddRuns.two_mul_succ_step hx
  constructor
  · intro ⟨c, hc⟩
    refine dvd_of_two_mul (k + 1) _ ⟨c, ?_⟩
    have hA : (3:Nat) ^ (k + 1) * c = 3 * (3 ^ k * c) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc]
    rw [hA, ← hc, ← hid]
  · intro ⟨c, hc⟩
    refine ⟨2 * c, ?_⟩
    have hA : (3:Nat) ^ (k + 1) * c = 3 * (3 ^ k * c) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc]
    have hB : (3:Nat) ^ k * (2 * c) = 2 * (3 ^ k * c) := by
      rw [Nat.mul_left_comm]
    rw [hc, hA] at hid
    rw [hB]
    omega

/-! ## The even step can inject 3-divisibility -/

/-- **The even-step law at level one.**  For even `x`, the successor's shift is
divisible by three exactly when `x ≡ 1 (mod 3)`. -/
theorem three_dvd_even_step_iff {x : Nat} (hx : x % 2 = 0) :
    3 ∣ (acceleratedStep x + 1) ↔ x % 3 = 1 := by
  have hstep : acceleratedStep x = x / 2 := by
    rw [acceleratedStep, if_pos hx]
  rw [hstep]
  omega

/-! ## The new forbidden window -/

/-- **Even orbit points congruent to one modulo three are large.**  For the least
never-dropper, such a point is at least `3m + 1`.

The even step sends `x` to `x/2`, whose shift is divisible by three precisely on
this class; the master bound then applies at the next index with `j = 1`. -/
theorem even_orbit_one_mod_three_ge {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (heven : acceleratedOrbit i m % 2 = 0)
    (hthree : acceleratedOrbit i m % 3 = 1) :
    3 * m + 1 ≤ acceleratedOrbit i m := by
  have hstep : acceleratedOrbit (i + 1) m = acceleratedOrbit i m / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos heven]
  have hdvd : (3:Nat) ^ 1 ∣ (acceleratedOrbit (i + 1) m + 1) := by
    rw [Nat.pow_one, hstep]
    omega
  have hb := orbit_backward_bound (i := i + 1) (j := 1) hgt hnd hmin hdvd
  rw [Nat.pow_one, Nat.pow_one, hstep] at hb
  omega

/-- Restated as a forbidden window: no even orbit point below `3m + 1` is
`1 (mod 3)`. -/
theorem no_even_one_mod_three_below {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x))
    (heven : acceleratedOrbit i m % 2 = 0)
    (hsmall : acceleratedOrbit i m < 3 * m + 1) :
    acceleratedOrbit i m % 3 ≠ 1 := by
  intro h
  have := even_orbit_one_mod_three_ge hgt hnd hmin heven h
  omega

/-- **Both non-zero classes modulo three are now constrained**, and by different
amounts: points `≡ 2 (mod 3)` are at least `(3m+1)/2`, and *even* points
`≡ 1 (mod 3)` are at least `3m + 1`. -/
theorem orbit_mod_three_windows {m i : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) :
    (2 * acceleratedOrbit i m < 3 * m + 1 → acceleratedOrbit i m % 3 ≠ 2) ∧
    (acceleratedOrbit i m % 2 = 0 → acceleratedOrbit i m < 3 * m + 1 →
      acceleratedOrbit i m % 3 ≠ 1) :=
  ⟨fun h => OrbitDescent.orbit_not_two_mod_three_below hgt hnd hmin h,
   fun he hs => no_even_one_mod_three_below hgt hnd hmin he hs⟩

end ThreeAdic
end Collatz
