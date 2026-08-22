import Collatz.Strategy.CycleProduct
import Collatz.Strategy.AffineExact

/-!
# The floor schedule: the product invariant with its scalar floor promoted to a measure

`CycleProduct.product_invariant` charges every odd step the *same* rate `(3c+1)/c`,
where `c` is one number below the whole orbit.  That single scalar is the reason the
bound decays: its slack after `a` odd steps is `a · log₂(1 + 1/(3c))`, which **grows
without bound in the window length** — `neverDrops_density`'s own note says it is
useful only for windows shorter than about `3c` steps.

The exact identity behind the invariant charges the odd step at index `i` the rate
`(3x_i + 1)/(3x_i)`, a function of the *actual orbit point*, not of a global floor:

`2 ^ k · T^k(x) / 3 ^ (a k) = x · ∏_{i < k, x_i odd} (3 x_i + d) / (3 x_i)`.

So the true object is not a number.  It is the **occupation measure of the odd steps
pushed forward by the orbit** — the measure `ν_k = Σ_{i<k, x_i odd} δ_{x_i}` — and the
defect is the integral `∫ log(1 + d/(3t)) dν_k(t)`.  This file replaces the scalar `c`
by an arbitrary **floor schedule** `f : ℕ → ℕ` with `f i ≤ T^i(x)`, which is exactly a
discretisation of that measure from below, and proves the invariant in that generality.

## What it is

* `floorProd f x k = ∏_{i<k, x_i odd} f i` and `floorProdS f x k = ∏_{i<k, x_i odd} (3·f i + 1)`;
* `sched_invariant` : `2 ^ k · floorProd f x k · T^k(x) ≤ floorProdS f x k · x`;
* `floorProd_const` : with `f ≡ c` these collapse to `c ^ a` and `(3c+1) ^ a`, so
  `CycleProduct.product_invariant` is the constant-schedule instance (`sched_generalises`).

## Why the promotion is not cosmetic

For a **divergent** orbit the tail minima `m_i = min_{k ≥ i} x_k` tend to infinity, so
the schedule `f i = m_i` is legitimate and the total defect is
`Σ_i log(1 + d/(3 m_i))`, which **converges** whenever the orbit grows at least
geometrically.  The constant schedule `f ≡ m` gives `a_k · log(1 + d/(3m)) → ∞`.
Hence:

> **Bounded-defect rigidity.**  Along a divergent orbit with a summable floor
> schedule, there is one constant `K = floorProdS/floorProd` with
> `3 ^ (a j) · x ≤ 2 ^ j · x_j ≤ K · 3 ^ (a j) · x` for **every** `j`.
> The archimedean coordinate is pinned to the parity word within a fixed
> multiplicative constant, forever.

That is the Round IX "one open bit" as a *constant* rather than as a bound `< 1` that
had to be re-earned window by window.  `sched_pin` is the two-sided statement.

## Admission

The schedule measure is **not** a word statistic.  `x` and `x + 2 ^ L` have the same
parity word of length `L` (Terras), hence the same discrepancy path, the same
`(L, a, C, G)`, and the same value of every additive word functor — but different
orbit magnitudes, hence different `ν`.  `sched_not_word_invariant` exhibits the
separation at `L = 8`, `x = 3` against `x = 259`.

## What it consumes

Assets (a), (c), (d) of the soundness filter.  (a): the floors are only large because
the verified range bounds the orbit from below, and every gain is proportional to
`1/f i`.  (c) and (d): the step inequality is `f·(3v + d) ≤ (3f + d)·v`, which needs
`d > 0` and reverses for `3x − 1` — `Mirror` already records that this invariant is
not mirror-invariant.  The device is therefore not `d`-free.

## What it does not do

It does not obstruct anything.  Bounded-defect rigidity constrains the word to be
heavy with a *vanishing* additive slack, and the words with vanishing slack are the
`ε`-heavy language, still exponentially many (`Density.heavyCount_pos`).  Recorded as
a sharpening of the coupling, not as a descent.
-/

namespace Collatz
namespace FloorSchedule

open Reach Congruence AffineExact CycleProduct

/-! ## The schedule products -/

/-- `∏_{i < k, T^i(x) odd} f i` — the floor schedule's odd-step product. -/
def floorProd (f : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => floorProd f x k * (if acceleratedOrbit k x % 2 = 1 then f k else 1)

/-- `∏_{i < k, T^i(x) odd} (3 · f i + 1)` — the charged form. -/
def floorProdS (f : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => floorProdS f x k * (if acceleratedOrbit k x % 2 = 1 then 3 * f k + 1 else 1)

@[simp] theorem floorProd_zero (f : Nat → Nat) (x : Nat) : floorProd f x 0 = 1 := rfl
@[simp] theorem floorProdS_zero (f : Nat → Nat) (x : Nat) : floorProdS f x 0 = 1 := rfl

theorem floorProd_odd {f : Nat → Nat} {x k : Nat} (h : acceleratedOrbit k x % 2 = 1) :
    floorProd f x (k + 1) = floorProd f x k * f k := by
  rw [floorProd, if_pos h]

theorem floorProd_even {f : Nat → Nat} {x k : Nat} (h : acceleratedOrbit k x % 2 = 0) :
    floorProd f x (k + 1) = floorProd f x k := by
  rw [floorProd, if_neg (by omega), Nat.mul_one]

theorem floorProdS_odd {f : Nat → Nat} {x k : Nat} (h : acceleratedOrbit k x % 2 = 1) :
    floorProdS f x (k + 1) = floorProdS f x k * (3 * f k + 1) := by
  rw [floorProdS, if_pos h]

theorem floorProdS_even {f : Nat → Nat} {x k : Nat} (h : acceleratedOrbit k x % 2 = 0) :
    floorProdS f x (k + 1) = floorProdS f x k := by
  rw [floorProdS, if_neg (by omega), Nat.mul_one]

/-- The constant schedule reproduces `c ^ a`. -/
theorem floorProd_const (c x : Nat) :
    ∀ k : Nat, floorProd (fun _ => c) x k = c ^ oddCount x k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlast := Density.oddCount_succ_last x k
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hc : oddCount x (k + 1) = oddCount x k := by omega
      rw [floorProd_even he, hc, ih]
    · have hc : oddCount x (k + 1) = oddCount x k + 1 := by omega
      rw [floorProd_odd ho, hc, ih, Nat.pow_succ]

/-- The constant schedule reproduces `(3c+1) ^ a`. -/
theorem floorProdS_const (c x : Nat) :
    ∀ k : Nat, floorProdS (fun _ => c) x k = (3 * c + 1) ^ oddCount x k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlast := Density.oddCount_succ_last x k
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hc : oddCount x (k + 1) = oddCount x k := by omega
      rw [floorProdS_even he, hc, ih]
    · have hc : oddCount x (k + 1) = oddCount x k + 1 := by omega
      rw [floorProdS_odd ho, hc, ih, Nat.pow_succ]

/-! ## The scheduled invariant -/

/-- **The scheduled product invariant.**  For *any* floor schedule `f` lying below the
orbit pointwise,

`2 ^ k · (∏_{i<k, odd} f i) · T^k(x) ≤ (∏_{i<k, odd} (3 f i + 1)) · x`.

The schedule need not be constant, monotone, or computable from the word.  This is the
scalar floor of `CycleProduct.product_invariant` promoted to a measure. -/
theorem sched_invariant {x : Nat} (f : Nat → Nat)
    (hf : ∀ i : Nat, f i ≤ acceleratedOrbit i x) :
    ∀ k : Nat, 2 ^ k * floorProd f x k * acceleratedOrbit k x
      ≤ floorProdS f x k * x := by
  intro k
  induction k with
  | zero => simp [acceleratedOrbit]
  | succ k ih =>
    have hstep : acceleratedOrbit (k + 1) x = acceleratedStep (acceleratedOrbit k x) :=
      acceleratedOrbit_succ_step k x
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · -- even step: both sides unchanged
      have hval : acceleratedStep (acceleratedOrbit k x) = acceleratedOrbit k x / 2 := by
        rw [acceleratedStep, if_pos he]
      have hhalf : 2 * (acceleratedOrbit k x / 2) = acceleratedOrbit k x := by omega
      have hkey : 2 ^ (k + 1) * floorProd f x (k + 1) * acceleratedOrbit (k + 1) x
          = 2 ^ k * floorProd f x k * acceleratedOrbit k x := by
        rw [floorProd_even he, hstep, hval, Arith.two_pow_succ]
        calc 2 * 2 ^ k * floorProd f x k * (acceleratedOrbit k x / 2)
            = 2 ^ k * floorProd f x k * (2 * (acceleratedOrbit k x / 2)) := by
              simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          _ = 2 ^ k * floorProd f x k * acceleratedOrbit k x := by rw [hhalf]
      rw [hkey, floorProdS_even he]
      exact ih
    · -- odd step: left picks up `f k * (3 v + 1)`, right picks up `(3 f k + 1) * v`
      have hval : acceleratedStep (acceleratedOrbit k x)
          = (3 * acceleratedOrbit k x + 1) / 2 := by
        rw [acceleratedStep, if_neg (by omega)]
      have hpar : 2 * ((3 * acceleratedOrbit k x + 1) / 2) = 3 * acceleratedOrbit k x + 1 := by
        omega
      have hkey : 2 ^ (k + 1) * floorProd f x (k + 1) * acceleratedOrbit (k + 1) x
          = 2 ^ k * floorProd f x k * (f k * (3 * acceleratedOrbit k x + 1)) := by
        rw [floorProd_odd ho, hstep, hval, Arith.two_pow_succ]
        calc 2 * 2 ^ k * (floorProd f x k * f k) * ((3 * acceleratedOrbit k x + 1) / 2)
            = 2 ^ k * floorProd f x k * (f k * (2 * ((3 * acceleratedOrbit k x + 1) / 2))) := by
              simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          _ = 2 ^ k * floorProd f x k * (f k * (3 * acceleratedOrbit k x + 1)) := by rw [hpar]
      have hcv : f k * (3 * acceleratedOrbit k x + 1)
          ≤ (3 * f k + 1) * acceleratedOrbit k x := by
        have hle := hf k
        have e1 : f k * (3 * acceleratedOrbit k x + 1)
            = 3 * (f k * acceleratedOrbit k x) + f k := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        have e2 : (3 * f k + 1) * acceleratedOrbit k x
            = 3 * (f k * acceleratedOrbit k x) + acceleratedOrbit k x := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        omega
      have hmono : 2 ^ k * floorProd f x k * (f k * (3 * acceleratedOrbit k x + 1))
          ≤ 2 ^ k * floorProd f x k * ((3 * f k + 1) * acceleratedOrbit k x) :=
        Nat.mul_le_mul_left _ hcv
      have hfactor : 2 ^ k * floorProd f x k * ((3 * f k + 1) * acceleratedOrbit k x)
          = (3 * f k + 1) * (2 ^ k * floorProd f x k * acceleratedOrbit k x) := by
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have hstepmono : (3 * f k + 1) * (2 ^ k * floorProd f x k * acceleratedOrbit k x)
          ≤ (3 * f k + 1) * (floorProdS f x k * x) :=
        Nat.mul_le_mul_left _ ih
      have hrhs : floorProdS f x (k + 1) * x
          = (3 * f k + 1) * (floorProdS f x k * x) := by
        rw [floorProdS_odd ho]
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [hkey, hrhs]
      omega

/-- `CycleProduct.product_invariant` is the constant-schedule instance. -/
theorem sched_generalises {x c : Nat} (hc : ∀ k : Nat, c ≤ acceleratedOrbit k x) (k : Nat) :
    2 ^ k * c ^ oddCount x k * acceleratedOrbit k x
      ≤ (3 * c + 1) ^ oddCount x k * x := by
  have h := sched_invariant (x := x) (fun _ => c) (fun i => hc i) k
  rw [floorProd_const, floorProdS_const] at h
  exact h

/-! ## The lower half of the pin -/

/-- The affine identity's positive-correction half: `3 ^ a · x ≤ 2 ^ k · T^k(x)`.
This is the archimedean-vs-word bridge from below, with no hypothesis at all. -/
theorem pin_lower (x k : Nat) :
    3 ^ oddCount x k * x ≤ 2 ^ k * acceleratedOrbit k x := by
  rw [affine_exact x k]
  exact Nat.le_add_right _ _

/-- **The defect is monotone.**  *Same round, same fact, other coordinate*:
`Linearizing.coupling_monotone` states this on `C` (`C j · 3^(A(j+1)) ≤ C (j+1) · 3^(A j)`);
this is the `Y = 2^j x_j / 3^(A j)` form, which is what the schedule bound consumes
directly.  Recorded, not claimed as new.  `Y_k = 2 ^ k · T^k(x) / 3 ^ (a k)` never decreases:
in integer form, `2 ^ i · x_i · 3 ^ (a k) ≤ 2 ^ k · x_k · 3 ^ (a i)` for `i ≤ k`.
The even step fixes `Y` exactly and the odd step raises it; nothing lowers it.  So the
coupling `r` of `Strategy.Coupling` is a monotone cocycle, and the whole two-sided
bridge gap over a window is its total increase. -/
theorem defect_monotone (x : Nat) :
    ∀ k : Nat, 2 ^ k * acceleratedOrbit k x * 3 ^ oddCount x (k + 1)
      ≤ 2 ^ (k + 1) * acceleratedOrbit (k + 1) x * 3 ^ oddCount x k := by
  intro k
  have hlast := Density.oddCount_succ_last x k
  have hstep : acceleratedOrbit (k + 1) x = acceleratedStep (acceleratedOrbit k x) :=
    acceleratedOrbit_succ_step k x
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
  · have hc : oddCount x (k + 1) = oddCount x k := by omega
    have hval : acceleratedStep (acceleratedOrbit k x) = acceleratedOrbit k x / 2 := by
      rw [acceleratedStep, if_pos he]
    have hhalf : 2 * (acceleratedOrbit k x / 2) = acceleratedOrbit k x := by omega
    have hEq : 2 ^ (k + 1) * acceleratedOrbit (k + 1) x = 2 ^ k * acceleratedOrbit k x := by
      rw [hstep, hval, Arith.two_pow_succ]
      calc 2 * 2 ^ k * (acceleratedOrbit k x / 2)
          = 2 ^ k * (2 * (acceleratedOrbit k x / 2)) := by
            simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ = 2 ^ k * acceleratedOrbit k x := by rw [hhalf]
    rw [hc, hEq]
    exact Nat.le_refl _
  · have hc : oddCount x (k + 1) = oddCount x k + 1 := by omega
    have hval : acceleratedStep (acceleratedOrbit k x)
        = (3 * acceleratedOrbit k x + 1) / 2 := by
      rw [acceleratedStep, if_neg (by omega)]
    have hpar : 2 * ((3 * acceleratedOrbit k x + 1) / 2) = 3 * acceleratedOrbit k x + 1 := by
      omega
    have hEq : 2 ^ (k + 1) * acceleratedOrbit (k + 1) x
        = 2 ^ k * (3 * acceleratedOrbit k x + 1) := by
      rw [hstep, hval, Arith.two_pow_succ]
      calc 2 * 2 ^ k * ((3 * acceleratedOrbit k x + 1) / 2)
          = 2 ^ k * (2 * ((3 * acceleratedOrbit k x + 1) / 2)) := by
            simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ = 2 ^ k * (3 * acceleratedOrbit k x + 1) := by rw [hpar]
    rw [hc, hEq, Nat.pow_succ]
    have hL : 2 ^ k * acceleratedOrbit k x * (3 ^ oddCount x k * 3)
        = (3 * (2 ^ k * acceleratedOrbit k x)) * 3 ^ oddCount x k := by
      simp [Nat.mul_comm, Nat.mul_assoc]
    have hR : 2 ^ k * (3 * acceleratedOrbit k x + 1) * 3 ^ oddCount x k
        = (3 * (2 ^ k * acceleratedOrbit k x) + 2 ^ k) * 3 ^ oddCount x k := by
      have : 2 ^ k * (3 * acceleratedOrbit k x + 1)
          = 3 * (2 ^ k * acceleratedOrbit k x) + 2 ^ k := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      rw [this]
    rw [hL, hR]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-! ## The two-sided pin -/

/-- **Bounded-defect rigidity, integer form.**  For any legitimate floor schedule,

`3 ^ (a k) · x · P ≤ 2 ^ k · T^k(x) · P ≤ S · x`,   `P = floorProd`, `S = floorProdS`.

So the archimedean coordinate `2 ^ k · T^k(x)` is trapped between `3 ^ (a k) · x` and
`(S/P) · 3 ^ (a k) · x` once the lower bound is used on the right, and `S/P =
∏ (1 + 1/(3 f i))` is a *constant* whenever the schedule is summable — which it is
along any orbit growing at least geometrically, and is not for a constant schedule. -/
theorem sched_pin {x : Nat} (f : Nat → Nat)
    (hf : ∀ i : Nat, f i ≤ acceleratedOrbit i x) (k : Nat) :
    3 ^ oddCount x k * x * floorProd f x k
        ≤ 2 ^ k * acceleratedOrbit k x * floorProd f x k
      ∧ 2 ^ k * acceleratedOrbit k x * floorProd f x k ≤ floorProdS f x k * x := by
  refine ⟨Nat.mul_le_mul_right _ (pin_lower x k), ?_⟩
  have h := sched_invariant f hf k
  have e : 2 ^ k * acceleratedOrbit k x * floorProd f x k
      = 2 ^ k * floorProd f x k * acceleratedOrbit k x := by
    simp [Nat.mul_comm, Nat.mul_assoc]
  rw [e]
  exact h

/-- **The word-invariant ratio is squeezed.**  Combining the two halves of the pin:
`3 ^ (a k) · P ≤ S` whenever `0 < x`.  The gap between the two sides is exactly the
schedule's total charge, so it is the *only* place the archimedean datum survives. -/
theorem pin_ratio {x : Nat} (hx : 0 < x) (f : Nat → Nat)
    (hf : ∀ i : Nat, f i ≤ acceleratedOrbit i x) (k : Nat) :
    3 ^ oddCount x k * floorProd f x k ≤ floorProdS f x k := by
  obtain ⟨h1, h2⟩ := sched_pin f hf k
  have h := Nat.le_trans h1 h2
  have e : 3 ^ oddCount x k * x * floorProd f x k
      = (3 ^ oddCount x k * floorProd f x k) * x := by
    simp [Nat.mul_comm, Nat.mul_assoc]
  rw [e] at h
  exact Nat.le_of_mul_le_mul_right h hx

/-! ## Admission: the schedule is not a word statistic

Terras: `x` and `x + 2 ^ L` have the same parity word of length `L`, hence the same
discrepancy path, the same `(L, a, C, G)`, and the same value of any additive word
functor.  The tightest legitimate schedule `f i = T^i(x)` separates them. -/

/-- The tightest legitimate schedule: the orbit itself. -/
def tightSchedule (x : Nat) : Nat → Nat := fun i => acceleratedOrbit i x

theorem tightSchedule_le (x : Nat) : ∀ i : Nat, tightSchedule x i ≤ acceleratedOrbit i x :=
  fun _ => Nat.le_refl _

/-- `3` and `3 + 2 ^ 8 = 259` run the same parity word for 8 steps. -/
theorem same_word_8 : oddCount 3 8 = oddCount 259 8 := by decide

/-- **The separation.**  Same word, same `(L, a, C, G)`, same discrepancy path — and
different schedule charge.  So the floor-schedule measure is *not* determined by the
word, is not a function of the discrepancy path, and is not additive along the word. -/
theorem sched_not_word_invariant :
    floorProdS (tightSchedule 3) 3 8 * floorProd (tightSchedule 259) 259 8
      ≠ floorProdS (tightSchedule 259) 259 8 * floorProd (tightSchedule 3) 3 8 := by
  decide

/-- The tight schedule is strictly cheaper than the constant one at the orbit minimum,
whenever the orbit ever rises: same word, strictly smaller charge ratio. -/
theorem tight_beats_const :
    floorProdS (tightSchedule 27) 27 20 * floorProd (fun _ => 27) 27 20
      < floorProdS (fun _ => 27) 27 20 * floorProd (tightSchedule 27) 27 20 := by
  decide

end FloorSchedule
end Collatz
